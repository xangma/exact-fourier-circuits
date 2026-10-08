#!/usr/bin/env python3
"""Bounded, synchronized JAX experiments; projected circuits are not DFTs."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--suite", choices=("all", "fft", "projection", "shear", "newton"), default="all")
    parser.add_argument("--require-gpu", action="store_true")
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--projection-input", choices=("random", "dyadic"), default="random")
    args = parser.parse_args()
    if not 1 <= args.repeats <= 100:
        parser.error("repeats must be between 1 and 100")
    import jax
    jax.config.update("jax_enable_x64", True)
    import jax.numpy as jnp
    import numpy as np
    from exact_fourier.jax_fft import compile_bluestein, compile_radix2
    from exact_fourier.jax_backend import compile_projected, compile_projected_target, compile_shear
    from exact_fourier.projection import build_projected_program, projected_target_exact
    from exact_fourier.scalars import GaussianRational as QI

    devices = jax.devices()
    if args.require_gpu and not all(d.platform == "gpu" for d in devices):
        raise SystemExit(f"Expected CUDA devices, got {devices}")
    receipt = dict(schema="exact-fourier-jax-replication/v1", passed=False,
                   started_utc=datetime.now(timezone.utc).isoformat(), host=platform.node(),
                   pid=os.getpid(), cwd=str(Path.cwd()), command=sys.argv,
                   python=sys.version, jax=jax.__version__, jaxlib=__import__("jaxlib").__version__,
                   numpy=np.__version__, devices=[str(d) for d in devices],
                   platforms=[d.platform for d in devices], repeats=args.repeats,
                   timing="First call includes JIT compilation; warm samples fence every result; transfers excluded.",
                   convention="DFT: sum_j x[j] exp(+2*pi*i*j*k/n), unnormalized.",
                   scope="Small projected tensor identities and classical DFTs; no full saving-instance execution or paper-DFT speedup claim.",
                   fft=[], projection=[], shear=[], newton=[])
    paths = sorted((ROOT / "src/exact_fourier").glob("*.py")) + [Path(__file__)]
    receipt["source_sha256"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        temp = args.output.with_suffix(".tmp")
        temp.write_text(json.dumps(receipt, indent=2, allow_nan=False) + "\n")
        temp.replace(args.output)

    def errors(actual, reference):
        actual = np.asarray(actual, dtype=np.complex128)
        reference = np.asarray(reference, dtype=np.complex128)
        if not np.all(np.isfinite(actual)):
            return dict(finite=False, relative_l2=None, maximum_absolute=None)
        delta = actual - reference
        return dict(finite=True, relative_l2=float(np.linalg.norm(delta.ravel()) / max(np.linalg.norm(reference.ravel()), 1e-300)),
                    maximum_absolute=float(np.max(np.abs(delta))))

    def measure(fn, x, repeats=None):
        tic = time.perf_counter()
        out = fn(x).block_until_ready()
        first = time.perf_counter() - tic
        fn(x).block_until_ready()
        samples = []
        for _ in range(args.repeats if repeats is None else repeats):
            tic = time.perf_counter()
            out = fn(x).block_until_ready()
            samples.append(time.perf_counter() - tic)
        return out, dict(first_call_seconds=first, warm_median_seconds=float(np.median(samples)),
                         warm_min_seconds=min(samples), warm_max_seconds=max(samples), warm_samples_seconds=samples)

    save()
    if args.suite in ("all", "fft"):
        lengths = [16, 64, 256, 1024, 4096, 16384, 65536, 17, 257, 4093]
        if args.quick:
            lengths = [16, 17, 64]
        rng = np.random.default_rng(130)
        for n in lengths:
            random = rng.normal(size=n) + 1j * rng.normal(size=n)
            dynamic = random * np.power(2.0, np.linspace(-20, 20, n))
            for dtype in (np.complex64, np.complex128):
                host = random.astype(dtype)
                x = jax.device_put(host)
                reference = np.fft.ifft(host.astype(np.complex128), norm="forward")
                methods = {"jax_fft": jax.jit(lambda z: jnp.conj(jnp.fft.fft(jnp.conj(z)))),
                           "legacy_ifft_forward": jax.jit(lambda z: jnp.fft.ifft(z, norm="forward")),
                           "bluestein": compile_bluestein(n)}
                if n & (n - 1) == 0:
                    methods["radix2"] = compile_radix2(n)
                if n <= 256:
                    # Constants prepared in host float64; preparation is excluded from warm timing.
                    matrix = np.exp(2j * np.pi * np.outer(np.arange(n), np.arange(n)) / n)
                    methods["dense_dft"] = jax.jit(lambda z, m=matrix: jnp.asarray(m, dtype=z.dtype) @ z)
                    dense_reference = matrix @ host.astype(np.complex128)
                    assert np.allclose(reference, dense_reference, rtol=2e-12, atol=2e-12)
                for name, fn in methods.items():
                    out, timing = measure(fn, x)
                    error = errors(out, reference)
                    tolerance = 3e-5 if dtype == np.complex64 else 3e-11
                    accuracy_pass = error["finite"] and error["relative_l2"] < tolerance
                    assert error["finite"] and (accuracy_pass or name == "legacy_ifft_forward"), (name, n, error)
                    dhost = dynamic.astype(dtype)
                    dout = fn(jax.device_put(dhost)).block_until_ready()
                    derror = errors(dout, np.fft.ifft(dhost.astype(np.complex128), norm="forward"))
                    assert derror["finite"] and (derror["relative_l2"] < tolerance or name == "legacy_ifft_forward"), (name, n, derror)
                    row = dict(n=n, dtype=np.dtype(dtype).name, method=name, input_bytes=host.nbytes,
                               random_error=error, dynamic_range_error=derror,
                               accuracy_pass=bool(accuracy_pass), accuracy_required=name != "legacy_ifft_forward", **timing)
                    receipt["fft"].append(row)
                    save()
                    print(f"FFT {n} {row['dtype']} {name}: {timing['warm_median_seconds']:.6g}s L2={error['relative_l2']:.3g}", flush=True)

    if args.suite in ("all", "projection"):
        for bits in ([1] if args.quick else [1, 4]):
            program = build_projected_program(h=4, bits=bits)
            roles, width = program.metadata["roles"], program.metadata["width"]
            exact = tuple(tuple(QI(Fraction((17*r+5*a) % 29-14, 8), Fraction((11*r+7*a) % 31-15, 16))
                                for a in range(width)) for r in range(roles))
            if args.projection_input == "random":
                rng = np.random.default_rng(130 + bits)
                host = rng.normal(size=(roles, width)) + 1j * rng.normal(size=(roles, width))
            else:
                host = np.array([[complex(float(v.real), float(v.imag)) for v in row] for row in exact])
            for dtype in (np.complex64, np.complex128):
                # Treat the actually supplied binary floats as exact Q(i).
                typed = host.astype(dtype)
                supplied = tuple(tuple(QI(Fraction(float(z.real)), Fraction(float(z.imag))) for z in row) for row in typed)
                exact_result = projected_target_exact(program, supplied)
                reference = np.array([[complex(float(v.real), float(v.imag)) for v in row] for row in exact_result])
                x = jax.device_put(typed)
                methods = {"independent_target": compile_projected_target(program),
                           "compiled_three_C": compile_projected(program, compiled_shears=True),
                           "direct_shear": compile_projected(program, compiled_shears=False)}
                for name, fn in methods.items():
                    # The full tape is intentionally bounded; one timed sample costs 72,842 records.
                    out, timing = measure(fn, x, repeats=1)
                    error = errors(out, reference)
                    assert error["finite"] and error["relative_l2"] < (1e-3 if dtype == np.complex64 else 1e-10), (name, bits, error)
                    row = dict(bits=bits, dtype=np.dtype(dtype).name, method=name,
                               metadata=program.metadata, input_family=args.projection_input, error=error, **timing)
                    receipt["projection"].append(row)
                    save()
                    print(f"Projection {bits} {row['dtype']} {name}: {timing['warm_median_seconds']:.6g}s L2={error['relative_l2']:.3g}", flush=True)

    if args.suite in ("all", "newton"):
        from exact_fourier.jax_newton import compile_newton, newton_factors
        rng = np.random.default_rng(130)
        for n in (2, 3, 4, 5, 8, 16, 32, 64):
            host = rng.normal(size=n) + 1j * rng.normal(size=n)
            for dtype in (np.complex64, np.complex128):
                typed = host.astype(dtype)
                x = jax.device_put(typed)
                reference = np.fft.ifft(typed.astype(np.complex128), norm="forward")
                N, diagonal = newton_factors(n, dtype=np.dtype(dtype).name)
                N, diagonal = np.asarray(N), np.asarray(diagonal)
                for name, fn in (("newton", compile_newton(n)),
                                 ("jax_fft", jax.jit(lambda z: jnp.conj(jnp.fft.fft(jnp.conj(z)))))):
                    out, timing = measure(fn, x)
                    error = errors(out, reference)
                    required = name == "jax_fft" or n <= 8
                    tolerance = 3e-5 if dtype == np.complex64 else 3e-11
                    accuracy_pass = error["finite"] and error["relative_l2"] < tolerance
                    assert error["finite"] and (accuracy_pass or not required), (n, name, error)
                    receipt["newton"].append(dict(n=n, dtype=np.dtype(dtype).name, method=name,
                        error=error, accuracy_required=required, accuracy_pass=bool(accuracy_pass),
                        factor_condition_estimate=float(np.linalg.cond(N.astype(np.complex128))),
                        factor_maximum_absolute=float(np.max(np.abs(N))),
                        intermediate_maximum_absolute=float(np.max(np.abs(N.T @ typed))), **timing))
                    save()
                    print(f"Newton {n} {np.dtype(dtype).name} {name}: L2={error['relative_l2']:.6g}", flush=True)

    if args.suite in ("all", "shear"):
        for dtype, top in ((np.complex64, 40), (np.complex128, 80)):
            exponents = np.arange(0, top + 1)
            targets = np.exp2(exponents).astype(dtype)
            host = np.stack([targets, np.ones_like(targets)])
            x = jax.device_put(host)
            for compiled in (True, False):
                out = np.asarray(compile_shear(Fraction(1), compiled_shears=compiled)(x).block_until_ready())
                # Exact mathematical source is 1 for every exponent.
                for k, exponent in enumerate(exponents):
                    receipt["shear"].append(dict(dtype=np.dtype(dtype).name, compiled=compiled,
                        exponent=int(exponent), target_real=float(out[0, k].real), target_imag=float(out[0, k].imag),
                        source_real=float(out[1, k].real), source_imag=float(out[1, k].imag),
                        source_absolute_error=float(abs(out[1,k]-1)),
                        relative_l2=float(np.linalg.norm(out[:,k].astype(np.complex128)-[float(2**int(exponent))+1,1]) /
                                          np.linalg.norm([float(2**int(exponent))+1,1]))))
                assert np.all(np.isfinite(out)), "Bounded shear sweep overflowed"
                if not compiled:
                    assert np.array_equal(out[1], np.ones_like(out[1])), "Direct shear changed source"
            save()
        print("Shear source-preservation sweep completed", flush=True)

    receipt["passed"] = True
    receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    print(f"PASS: {args.output}", flush=True)


if __name__ == "__main__":
    main()
