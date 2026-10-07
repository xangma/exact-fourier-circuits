#!/usr/bin/env python3
"""Execute a bounded projected network with its actual scalar-gate ordering.

Requires NumPy and CuPy on the execution host. Each family/precision/FMA/shear
case runs in a subprocess with a wall-clock deadline. Numerical overflow is a
recorded diagnostic outcome. This experiment makes no speedup or full-seed
verification claim.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import A, B, Call, Scale, shear_steps


SCHEMA = "exact-fourier-projected-program/v1"


def checked_integer(value, name, low=0, high=None):
    if type(value) is not int or value < low or (high is not None and value > high):
        raise ValueError(f"invalid {name}")
    return value


def validate_program(data, *, max_roles=4096, max_width=256, max_records=250_000):
    if not isinstance(data, dict) or data.get("schema") != SCHEMA:
        raise ValueError("invalid projected-program schema")
    metadata = data.get("metadata")
    if not isinstance(metadata, dict):
        raise ValueError("missing projected-program metadata")
    roles = checked_integer(metadata.get("roles"), "roles", 1, max_roles)
    width = checked_integer(metadata.get("width"), "width", 2, max_width)
    if roles & (roles - 1) or width & (width - 1):
        raise ValueError("roles and width must be powers of two")
    records = data.get("records")
    if not isinstance(records, list) or len(records) > max_records:
        raise ValueError("record array exceeds the import limit")
    coefficients = set()
    for record in records:
        if not isinstance(record, (list, tuple)) or len(record) != 6:
            raise ValueError("a record must be [op,target,arg,num,den,inverse]")
        op, target, arg, numerator, denominator, inverse = record
        checked_integer(op, "operation", 0, 4)
        checked_integer(target, "target role", 0, roles - 1)
        checked_integer(arg, "record argument")
        if type(inverse) is not bool:
            raise ValueError("record inverse must be a bool")
        if type(numerator) is not int or abs(numerator).bit_length() > 31:
            raise ValueError("coefficient numerator exceeds the import limit")
        checked_integer(denominator, "coefficient denominator", 1, (1 << 31) - 1)
        if op in (0, 3):
            if arg >= width:
                raise ValueError("direction/translation mask exceeds address width")
        else:
            if arg >= roles:
                raise ValueError("source role/mask exceeds role width")
            if op in (1, 2) and target == arg:
                raise ValueError("pair roles must be distinct")
            if op == 4 and (arg == 0 or arg & (arg - 1)):
                raise ValueError("a role-axis mask must be one nonzero role bit")
        if op != 1 and (numerator != 0 or denominator != 1):
            raise ValueError("only shear records have a coefficient")
        if op != 0 and inverse:
            raise ValueError("only directional records have inverse semantics")
        if op == 1:
            coefficient = Fraction(numerator, denominator)
            if not coefficient:
                raise ValueError("compiled three-C shear coefficients must be nonzero")
            coefficients.add(coefficient)
    if len(coefficients) > 32:
        raise ValueError("too many distinct shear coefficients")
    checkpoints = data.get("checkpoints", [])
    if not isinstance(checkpoints, list) or len(checkpoints) > 64:
        raise ValueError("checkpoint array exceeds the import limit")
    previous = -1
    labels = set()
    for checkpoint in checkpoints:
        if not isinstance(checkpoint, dict) or set(checkpoint) != {"label", "record_index"}:
            raise ValueError("invalid checkpoint")
        label = checkpoint["label"]
        if not isinstance(label, str) or not label or len(label) > 120 or label in labels:
            raise ValueError("checkpoint labels must be short and unique")
        index = checked_integer(checkpoint["record_index"], "checkpoint index", 0, len(records))
        if index < previous:
            raise ValueError("checkpoints must be chronological")
        previous = index
        labels.add(label)
    bank_size = checked_integer(metadata.get("bank_size", 0), "bank size", 0, roles // 2)
    original_roles = checked_integer(metadata.get("original_roles", roles), "original roles",
                                     2 * bank_size, roles)
    return roles, width, tuple(sorted(coefficients)), original_roles, bank_size


def digest_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def read_program(path):
    path = Path(path)
    if path.stat().st_size > 64 * 1024 * 1024:
        raise ValueError("program exceeds the JSON byte limit")
    data = json.loads(path.read_text())
    validate_program(data)
    return data


def check_fixture_size(path, *, max_uncompressed_bytes=512 * 1024 * 1024):
    """Bound decompressed arrays before NumPy reads a compressed NPZ fixture."""
    with zipfile.ZipFile(path) as archive:
        if sum(item.file_size for item in archive.infolist()) > max_uncompressed_bytes:
            raise ValueError("fixture exceeds the 512MiB uncompressed import cap")


def exact_pair(x, y):
    """The same four charged scalar gates used by Word.compile()."""
    difference = y - x
    scaled = B * difference
    return x + scaled, y - scaled


def exact_compiled_shear(y, x, coefficient):
    """Standard-library reference for the generated three-C local interpreter."""
    values = [QI.coerce(y), QI.coerce(x)]
    for step in shear_steps(0, 1, coefficient):
        if isinstance(step, Scale):
            values[step.coordinate] = step.coefficient * values[step.coordinate]
        elif isinstance(step, Call):
            first, second = step.coordinates
            values[first], values[second] = exact_pair(values[first], values[second])
        else:
            raise ValueError("unsupported step in compiled shear")
    return tuple(values)


def scalar_literal(value):
    return f"(T)({float(value):.17g})"


def shear_cases(coefficients):
    """Generate instructions from words.shear_steps, never rederive its identity."""
    lines = []
    descriptions = []
    for index, coefficient in enumerate(coefficients):
        steps = shear_steps(0, 1, coefficient)
        lines.append(f"case {index}: {{")
        for step in steps:
            if isinstance(step, Scale):
                lines.append(f"s{step.coordinate}=scale_z(s{step.coordinate},"
                             f"{scalar_literal(step.coefficient.real)},"
                             f"{scalar_literal(step.coefficient.imag)},peak,nans,infs);")
            elif isinstance(step, Call):
                first, second = step.coordinates
                lines.append(f"c_pair(s{first},s{second},peak,nans,infs);")
            else:
                raise ValueError("unsupported step in shear code generation")
        lines.append("break; }")
        calls = sum(isinstance(step, Call) for step in steps)
        scalings = sum(isinstance(step, Scale) for step in steps)
        if calls != 3:
            raise ValueError("nonzero shear does not compile to three C calls")
        descriptions.append({"numerator": coefficient.numerator, "denominator": coefficient.denominator,
                             "C_calls": calls, "scalings": scalings, "scalar_gates": calls * 4 + scalings})
    return "\n".join(lines), descriptions


CUDA_TEMPLATE = r'''
typedef @TYPE@ T;
struct Z { T r, i; };
__device__ __forceinline__ Z load_z(const T* real,const T* imag,long long index) {
    Z z={real[index],imag[index]}; return z;
}
__device__ __forceinline__ void store_z(T* real,T* imag,long long index,Z z) {
    real[index]=z.r; imag[index]=z.i;
}
__device__ __forceinline__ void track(Z z,double& peak,unsigned long long& nans,unsigned long long& infs) {
    double parts[2]={(double)z.r,(double)z.i};
    for(int j=0;j<2;j++) {
        double part=parts[j];
        if(part!=part) nans++;
        else if(part>1.7976931348623157e308 || part<-1.7976931348623157e308) infs++;
        else {
            double magnitude=part<0 ? -part : part;
            if(magnitude>peak) peak=magnitude;
        }
    }
}
__device__ __forceinline__ Z add_z(Z x,Z y,double& peak,unsigned long long& nans,unsigned long long& infs) {
    Z z={x.r+y.r,x.i+y.i}; track(z,peak,nans,infs); return z;
}
__device__ __forceinline__ Z sub_z(Z x,Z y,double& peak,unsigned long long& nans,unsigned long long& infs) {
    Z z={x.r-y.r,x.i-y.i}; track(z,peak,nans,infs); return z;
}
__device__ __forceinline__ Z scale_z(Z x,T real,T imag,double& peak,unsigned long long& nans,unsigned long long& infs) {
    Z z={real*x.r-imag*x.i,real*x.i+imag*x.r}; track(z,peak,nans,infs); return z;
}
__device__ __forceinline__ void c_pair(Z& x,Z& y,double& peak,unsigned long long& nans,unsigned long long& infs) {
    Z d=sub_z(y,x,peak,nans,infs);
    Z t=scale_z(d,(T)0.5,(T)-0.5,peak,nans,infs);
    Z u=add_z(x,t,peak,nans,infs);
    Z v=sub_z(y,t,peak,nans,infs);
    x=u; y=v;
}
__device__ __forceinline__ void compiled_shear(int id,Z& s0,Z& s1,double& peak,unsigned long long& nans,unsigned long long& infs) {
    switch(id) {
    @SHEAR_CASES@
    }
}
__device__ __forceinline__ void checkpoint(const T* real,const T* imag,T* checkpoints_real,T* checkpoints_imag,
                                          int checkpoint_id,int roles,int width,int address) {
    long long base=(long long)checkpoint_id*roles*width;
    for(int role=0;role<roles;role++) {
        long long index=(long long)role*width+address;
        checkpoints_real[base+index]=real[index];
        checkpoints_imag[base+index]=imag[index];
    }
}
extern "C" __global__ void projected_network(T* real,T* imag,const long long* records,int nrecords,
    int roles,int width,int direct_shear,const int* checkpoint_indices,int ncheckpoints,
    T* checkpoints_real,T* checkpoints_imag,double* peaks,unsigned long long* nan_events,unsigned long long* inf_events) {
    int address=threadIdx.x;
    double peak=0;
    unsigned long long nans=0,infs=0;
    int next_checkpoint=0;
    for(int role=0;role<roles;role++) track(load_z(real,imag,(long long)role*width+address),peak,nans,infs);
    while(next_checkpoint<ncheckpoints && checkpoint_indices[next_checkpoint]==0) {
        checkpoint(real,imag,checkpoints_real,checkpoints_imag,next_checkpoint,roles,width,address);
        next_checkpoint++;
    }
    __syncthreads();
    for(int operation=0;operation<nrecords;operation++) {
        const long long* record=records+(long long)operation*7;
        int op=(int)record[0],target=(int)record[1],arg=(int)record[2];
        long long first=(long long)target*width+address;
        if(op==0 && arg!=0) {
            int pivot=arg & -arg;
            if((address & pivot)==0) {
                long long second=(long long)target*width+(address ^ arg);
                Z x=load_z(real,imag,first),y=load_z(real,imag,second);
                c_pair(x,y,peak,nans,infs);
                if(record[5]) { Z tmp=x; x=y; y=tmp; }
                store_z(real,imag,first,x); store_z(real,imag,second,y);
            }
        } else if(op==1) {
            long long second=(long long)arg*width+address;
            Z y=load_z(real,imag,first),x=load_z(real,imag,second);
            if(direct_shear) {
                T coefficient=(T)record[3]/(T)record[4];
                Z scaled=scale_z(x,coefficient,(T)0,peak,nans,infs);
                y=add_z(y,scaled,peak,nans,infs);
                store_z(real,imag,first,y);
            } else {
                compiled_shear((int)record[6],y,x,peak,nans,infs);
                store_z(real,imag,first,y); store_z(real,imag,second,x);
            }
        } else if(op==2) {
            long long second=(long long)arg*width+address;
            Z x=load_z(real,imag,first),y=load_z(real,imag,second);
            Z negative={-x.r,-x.i}; track(negative,peak,nans,infs);
            store_z(real,imag,first,y); store_z(real,imag,second,negative);
        } else if(op==3 && arg!=0) {
            int pivot=arg & -arg;
            if((address & pivot)==0) {
                long long second=(long long)target*width+(address ^ arg);
                Z x=load_z(real,imag,first),y=load_z(real,imag,second);
                store_z(real,imag,first,y); store_z(real,imag,second,x);
            }
        } else if(op==4) {
            for(int role=0;role<roles;role++) if((role & arg)==0) {
                long long left=(long long)role*width+address;
                long long right=(long long)(role ^ arg)*width+address;
                Z x=load_z(real,imag,left),y=load_z(real,imag,right);
                c_pair(x,y,peak,nans,infs);
                store_z(real,imag,left,x); store_z(real,imag,right,y);
            }
        }
        // One block owns every address; this barrier also orders global writes.
        __syncthreads();
        while(next_checkpoint<ncheckpoints && checkpoint_indices[next_checkpoint]==operation+1) {
            checkpoint(real,imag,checkpoints_real,checkpoints_imag,next_checkpoint,roles,width,address);
            next_checkpoint++;
        }
        __syncthreads();
    }
    peaks[address]=peak; nan_events[address]=nans; inf_events[address]=infs;
}
'''


def cuda_source(dtype, coefficients):
    if dtype not in ("float32", "float64"):
        raise ValueError("unsupported CUDA precision")
    cases, descriptions = shear_cases(coefficients)
    source = CUDA_TEMPLATE.replace("@TYPE@", "float" if dtype == "float32" else "double")
    return source.replace("@SHEAR_CASES@", cases), descriptions


def normalize_fixture(data, roles, width):
    """Check NPZ arrays; 2D is one family, 3D has a leading family axis."""
    import numpy as np
    arrays = {}
    for key in ("real", "imag", "reference_real", "reference_imag"):
        if key not in data:
            raise ValueError(f"fixture lacks {key}")
        value = np.asarray(data[key])
        if value.ndim == 2:
            value = value[None]
        if value.ndim != 3 or value.shape[1:] != (roles, width) or value.dtype.kind not in "fiu":
            raise ValueError(f"invalid fixture {key} shape/type")
        arrays[key] = value
    if len({value.shape for value in arrays.values()}) != 1:
        raise ValueError("input and reference fixture shapes differ")
    families = arrays["real"].shape[0]
    if not 1 <= families <= 32:
        raise ValueError("fixture exceeds the family limit")
    if any(not np.isfinite(value).all() for value in arrays.values()):
        raise ValueError("inputs and exact-to-float references must be finite")
    for key in ("checkpoint_reference_real", "checkpoint_reference_imag"):
        if key in data:
            value = np.asarray(data[key])
            if value.ndim == 3:
                value = value[None]
            if value.ndim != 4 or value.shape[0] != families or value.shape[2:] != (roles, width):
                raise ValueError(f"invalid fixture {key} shape")
            if value.dtype.kind not in "fiu" or not np.isfinite(value).all():
                raise ValueError(f"invalid fixture {key} type/values")
            arrays[key] = value
    if ("checkpoint_reference_real" in arrays) != ("checkpoint_reference_imag" in arrays):
        raise ValueError("both checkpoint reference components are required")
    names = [f"family-{index}" for index in range(families)]
    if "family_names" in data:
        raw_names = np.asarray(data["family_names"])
        if raw_names.shape != (families,) or raw_names.dtype.kind not in "SU":
            raise ValueError("family_names must be a one-dimensional string array")
        names = [str(name) if raw_names.dtype.kind == "U" else bytes(name).decode() for name in raw_names]
    return arrays, names


def metrics(real, imag, reference_real, reference_imag):
    import math
    import numpy as np
    real = np.asarray(real, dtype=np.float64)
    imag = np.asarray(imag, dtype=np.float64)
    reference_real = np.asarray(reference_real, dtype=np.float64)
    reference_imag = np.asarray(reference_imag, dtype=np.float64)
    finite = np.isfinite(real) & np.isfinite(imag)
    result = {"elements": int(real.size), "nonfinite_elements": int((~finite).sum()),
              "nan_components": int(np.isnan(real).sum() + np.isnan(imag).sum()),
              "inf_components": int(np.isinf(real).sum() + np.isinf(imag).sum()),
              "exact_reference_match": bool(np.array_equal(real, reference_real) and np.array_equal(imag, reference_imag)),
              "relative_l2": None, "max_scaled_error": None, "max_absolute_error": None}
    if real.size == 0:
        result.update(relative_l2=0.0, max_scaled_error=0.0, max_absolute_error=0.0)
        return result
    if not finite.all():
        return result
    # Subtract first: normalizing two adjacent floats separately can round them
    # to the same value and incorrectly erase a one-ULP discrepancy.
    with np.errstate(over="ignore", invalid="ignore"):
        delta_real = real - reference_real
        delta_imag = imag - reference_imag
    raw_safe = np.isfinite(delta_real).all() and np.isfinite(delta_imag).all()
    result["error_evaluation"] = "raw-subtraction" if raw_safe else "scaled-overflow-fallback"
    reference_scale = max(float(np.max(np.abs(reference_real))), float(np.max(np.abs(reference_imag))), np.finfo(float).tiny)
    expected = reference_real / reference_scale + 1j * (reference_imag / reference_scale)
    if raw_safe:
        error_scale = max(float(np.max(np.abs(delta_real))), float(np.max(np.abs(delta_imag))), np.finfo(float).tiny)
        difference = delta_real / error_scale + 1j * (delta_imag / error_scale)
    else:
        # Overflowing raw differences necessarily dominate any normalization
        # rounding. Keep that case finite without claiming exact agreement.
        error_scale = max(reference_scale, float(np.max(np.abs(real))), float(np.max(np.abs(imag))))
        difference = (real / error_scale - reference_real / error_scale) + 1j * (imag / error_scale - reference_imag / error_scale)

    def scaled_ratio(numerator_scale, numerator_unit, denominator_scale, denominator_unit):
        if numerator_unit == 0:
            return 0.0
        if denominator_unit == 0:
            return None
        # Avoid intermediate overflow when the final ratio is representable.
        numerator_mantissa, numerator_exponent = math.frexp(numerator_scale)
        denominator_mantissa, denominator_exponent = math.frexp(denominator_scale)
        mantissa = (numerator_mantissa / denominator_mantissa) * (numerator_unit / denominator_unit)
        try:
            return math.ldexp(mantissa, numerator_exponent - denominator_exponent)
        except OverflowError:
            return None

    error_norm = float(np.linalg.norm(difference))
    error_maximum = float(np.max(np.abs(difference)))
    reference_norm = float(np.linalg.norm(expected))
    reference_maximum = float(np.max(np.abs(expected)))
    result["relative_l2"] = scaled_ratio(error_scale, error_norm, reference_scale, reference_norm)
    result["max_scaled_error"] = scaled_ratio(error_scale, error_maximum, reference_scale, reference_maximum)
    result["max_absolute_error"] = scaled_ratio(error_scale, error_maximum, 1.0, 1.0)
    return result


def group_metrics(real, imag, reference_real, reference_imag, bank_size, original_roles):
    groups = {"all": slice(None), "X_bank": slice(0, bank_size),
              "Y_bank": slice(bank_size, 2 * bank_size),
              "auxiliary": slice(2 * bank_size, original_roles),
              "padding": slice(original_roles, real.shape[0])}
    return {name: metrics(real[group], imag[group], reference_real[group], reference_imag[group])
            for name, group in groups.items()}


def worker(args):
    import numpy as np
    import cupy as cp
    data = read_program(args.program)
    roles, width, coefficients, original_roles, bank_size = validate_program(data)
    check_fixture_size(args.fixture)
    with np.load(args.fixture, allow_pickle=False) as loaded:
        fixture, names = normalize_fixture(loaded, roles, width)
    checked_integer(args.family, "family index", 0, len(names) - 1)
    checkpoints = data.get("checkpoints", [])
    if "checkpoint_reference_real" in fixture and fixture["checkpoint_reference_real"].shape[1] != len(checkpoints):
        raise ValueError("checkpoint reference count differs from program")
    # Arrays plus reference/checkpoint storage; refuse unexpectedly large cases.
    element_bytes = np.dtype(args.dtype).itemsize
    allocated = (2 + 2 * len(checkpoints)) * roles * width * element_bytes + len(data["records"]) * 7 * 8
    if allocated > 512 * 1024 * 1024:
        raise ValueError("case exceeds the 512MiB GPU allocation cap")
    coefficient_indices = {value: index for index, value in enumerate(coefficients)}
    encoded_records = [list(record) + [coefficient_indices[Fraction(record[3], record[4])] if record[0] == 1 else -1]
                       for record in data["records"]]
    records = cp.asarray(np.asarray(encoded_records, dtype=np.int64).reshape(-1, 7))
    checkpoint_indices = cp.asarray(np.array([item["record_index"] for item in checkpoints], dtype=np.int32))
    real = cp.asarray(fixture["real"][args.family], dtype=args.dtype, order="C")
    imag = cp.asarray(fixture["imag"][args.family], dtype=args.dtype, order="C")
    checkpoint_real = cp.empty((len(checkpoints), roles, width), dtype=args.dtype)
    checkpoint_imag = cp.empty_like(checkpoint_real)
    peaks = cp.empty(width, dtype=np.float64)
    nan_events = cp.empty(width, dtype=np.uint64)
    inf_events = cp.empty(width, dtype=np.uint64)
    source, descriptions = cuda_source(args.dtype, coefficients)
    options = ("--std=c++11", f"--fmad={'true' if args.fmad == 'on' else 'false'}")
    module = cp.RawModule(code=source, options=options, backend="nvrtc")
    kernel = module.get_function("projected_network")
    begin = time.perf_counter()
    kernel((1,), (width,), (real, imag, records, np.int32(len(encoded_records)), np.int32(roles),
                          np.int32(width), np.int32(args.shear_mode == "direct"), checkpoint_indices,
                          np.int32(len(checkpoints)), checkpoint_real, checkpoint_imag, peaks, nan_events, inf_events))
    cp.cuda.runtime.deviceSynchronize()
    elapsed = time.perf_counter() - begin
    outputs = {"real": cp.asnumpy(real), "imag": cp.asnumpy(imag),
               "checkpoint_real": cp.asnumpy(checkpoint_real), "checkpoint_imag": cp.asnumpy(checkpoint_imag)}
    prefix = Path(args.output_prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(str(prefix) + ".npz", **outputs)
    reference_real, reference_imag = fixture["reference_real"][args.family], fixture["reference_imag"][args.family]
    checkpoints_results = []
    if "checkpoint_reference_real" in fixture:
        for index, checkpoint in enumerate(checkpoints):
            checkpoints_results.append({**checkpoint, "metrics": group_metrics(
                outputs["checkpoint_real"][index], outputs["checkpoint_imag"][index],
                fixture["checkpoint_reference_real"][args.family, index],
                fixture["checkpoint_reference_imag"][args.family, index], bank_size, original_roles)})
    counts = Counter(record[0] for record in data["records"])
    device = cp.cuda.runtime.getDeviceProperties(cp.cuda.Device().id)
    device_name = device["name"].decode() if isinstance(device["name"], bytes) else str(device["name"])
    result = {"schema": "projected-cuda-case/v1", "status": "completed", "diagnostic_only": True,
              "family": names[args.family], "family_index": args.family, "dtype": args.dtype,
              "fmad": args.fmad, "shear_mode": args.shear_mode, "roles": roles, "width": width,
              "records": len(encoded_records), "operation_counts": {str(k): v for k, v in sorted(counts.items())},
              "elapsed_kernel_seconds": elapsed, "GPU_allocation_estimate_bytes": allocated,
              "max_finite_intermediate_component": float(cp.max(peaks).get()),
              "nan_gate_component_events": int(cp.sum(nan_events).get()),
              "inf_gate_component_events": int(cp.sum(inf_events).get()),
              "intermediate_tracking": "inputs and complex scalar gate outputs; events may count one value repeatedly",
              "compiled_shears": descriptions, "primitive_C_scalar_gates": 4,
              "metrics": group_metrics(outputs["real"], outputs["imag"], reference_real, reference_imag,
                                        bank_size, original_roles),
              "checkpoints": checkpoints_results, "output_npz": str(prefix) + ".npz",
              "program_sha256": digest_file(args.program), "fixture_sha256": digest_file(args.fixture),
              "kernel_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "runner_sha256": digest_file(__file__), "cuda_compile_options": list(options),
              "host":platform.node(),"pid":os.getpid(),"cwd":str(Path.cwd()),
              "device": device_name, "cupy_version": cp.__version__,"numpy_version":np.__version__,
              "cuda_runtime_version": cp.cuda.runtime.runtimeGetVersion(),
              "cuda_driver_version": cp.cuda.runtime.driverGetVersion(), "metadata": data["metadata"]}
    Path(str(prefix) + ".json").write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"status": "completed", "output": str(prefix) + ".json"}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program", required=True)
    parser.add_argument("--fixture", required=True)
    parser.add_argument("--output-prefix", required=True)
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--dtype", choices=("float32", "float64"))
    parser.add_argument("--fmad", choices=("on", "off"))
    parser.add_argument("--shear-mode", choices=("compiled", "direct"))
    parser.add_argument("--family", type=int, help="Run just one zero-based fixture family")
    parser.add_argument("--_worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not 0 < args.timeout <= 180:
        parser.error("timeout must be in (0,180] seconds")
    if args._worker:
        worker(args)
        return
    import numpy as np
    data = read_program(args.program)
    roles, width, _, _, _ = validate_program(data)
    check_fixture_size(args.fixture)
    with np.load(args.fixture, allow_pickle=False) as loaded:
        fixture, names = normalize_fixture(loaded, roles, width)
    # Drop the loaded references before starting workers; they reload one case.
    del fixture
    families = range(len(names)) if args.family is None else (checked_integer(args.family, "family", 0, len(names)-1),)
    prefix = Path(args.output_prefix).resolve()
    prefix.parent.mkdir(parents=True, exist_ok=True)
    results = []
    for family in families:
        for dtype in ((args.dtype,) if args.dtype else ("float32", "float64")):
            for fmad in ((args.fmad,) if args.fmad else ("on", "off")):
                for mode in ((args.shear_mode,) if args.shear_mode else ("compiled", "direct")):
                    case_prefix = str(prefix) + f".family{family}.{dtype}.fmad-{fmad}.{mode}"
                    command = [sys.executable, str(Path(__file__).resolve()), "--_worker", "--program", str(Path(args.program).resolve()),
                               "--fixture", str(Path(args.fixture).resolve()), "--output-prefix", case_prefix,
                               "--dtype", dtype, "--fmad", fmad, "--shear-mode", mode, "--family", str(family)]
                    base = {"family": names[family], "dtype": dtype, "fmad": fmad, "shear_mode": mode}
                    try:
                        process = subprocess.run(command, capture_output=True, text=True, timeout=args.timeout)
                        log_path = case_prefix + ".log"
                        Path(log_path).write_text(process.stdout + process.stderr)
                        if process.returncode:
                            result = {**base, "status": "execution_error", "returncode": process.returncode, "log": log_path}
                        else:
                            result = json.loads(Path(case_prefix + ".json").read_text())
                    except subprocess.TimeoutExpired as error:
                        log_path = case_prefix + ".log"
                        output_parts = [part if isinstance(part, bytes) else part.encode()
                                        for part in (error.stdout or "", error.stderr or "")]
                        Path(log_path).write_bytes(b"".join(output_parts))
                        result = {**base, "status": "timeout", "timeout_seconds": args.timeout, "log": log_path}
                    results.append(result)
                    print(json.dumps({**base, "status": result["status"]}), flush=True)
                    # Retain complete cases even if a later case fails or is interrupted.
                    aggregate = {"schema": "projected-cuda-results/v1", "diagnostic_only": True,
                                 "program_sha256": digest_file(args.program), "fixture_sha256": digest_file(args.fixture),
                                 "metadata": data["metadata"], "cases": results}
                    Path(str(prefix) + ".results.json").write_text(json.dumps(aggregate, indent=2, allow_nan=False) + "\n")
                    if result["status"] != "completed":
                        sys.exit(1)
    if any(result["status"] != "completed" for result in results):
        sys.exit(1)


if __name__ == "__main__":
    main()
