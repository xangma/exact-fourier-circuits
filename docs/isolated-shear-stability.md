# A source-restoration failure in the compiled three-C shear

The literal three-C implementation is exact over Gaussian rationals but can
lose its source in FP32 and FP64. For the actual network coefficient `t=1`,
input `(y,x)=(2^24,1)` produces source `0` in FP32; `(2^64,1)` produces
source `0` in FP64. The direct shear preserves source `1`. Both compiled
targets equal the rounded large target, so a normwise error measure can hide
the 100% relative error in the source.

This is a finite-precision implementation failure, not a machine-precision
error in Lean's exact-complex proof. The full two-dimensional matrix of every
tested literal shear was checked with Gaussian rationals before execution.
The complete saving word's Lean action/count certificate is now checked;
see the [final conclusion](conclusion.md). Equivalence of the Python producer
to that Lean word remains a separate obligation.

## Evidence and controls

The [predeclared contract](isolated-shear-contract.md) requires finite outputs,
target error at most `64u * max_j(|y_j|+|t*x_j|)`, and source error at most
`64u * max_j|x_j|`. References and error subtraction use exact Fractions of
stored floating-point components. Each of sixteen arms ran 585 cases on
**len / RTX4090**, covering balanced inputs, cancellation, large targets with
small sources, exponent-range stress, and one tiny-coefficient control.

Failures below include nonfinite outputs, shown separately in parentheses.
FMA on/off gave identical output bytes in every arm.

| Implementation | FP32 failed / 585 (nonfinite) | FP64 failed / 585 (nonfinite) |
|---|---:|---:|
| Direct shear | 0 (0) | 0 (0) |
| Literal compiled shear | 21 (5) | 13 (5) |
| Common power-of-two normalization | 17 (0) | 9 (0) |
| Source scaling, then coefficient-one shear | 19 (2) | 11 (2) |

All balanced and cancellation cases passed this criterion. This does not
establish accuracy relative to every small cancelling output. The decisive
source-loss cases have normal finite inputs and use a coefficient from the
actual network, independent of the generic tiny-coefficient control.
Common normalization removed the observed overflow but did not restore lost
source information. Source scaling also retained source-loss cases.

An independent CPU replay rounds each scalar component operation separately
and follows the chronological literal word. Compare input source `1` with
source `0`, using the same large target. The complete two-coordinate states
first become identical after step 7 (zero-based) for FP32 and step 2 for FP64.
They remain identical afterwards and reproduce the non-FMA CUDA outputs.
Mixing the large target with the small source has rounded away the source
information; later algebraic cancellation cannot recover it.

These traces diagnose this arithmetic ordering and these inputs. They do
not prove instability of every allowed saving circuit or provide a full-width
error bound. The astronomical saving instance cannot be materialized, and
these experiments make no FFT performance claim.

## Reproduce and retained artifacts

[Raw archive](../verification/isolated-shear/completed.tar.gz) retains inputs,
outputs, per-case hexadecimal values, exact reference fractions, generated CUDA,
compiled objects, source hashes, logs and the controller's terminal receipt.
[Independent summary](../verification/isolated-shear/verified-summary.json)
checks all 9,360 cases; [CPU traces](../verification/isolated-shear/source-loss-traces.json)
record the information loss. The worker completed in 10.632 seconds, exited
zero and was reaped; a subsequent read-only process check found neither the
worker nor controller still running. Existing GPU services were preserved.

```sh
mkdir -p outputs/isolated-shear-retained
tar -xzf verification/isolated-shear/completed.tar.gz -C outputs/isolated-shear-retained
.venv/bin/python scripts/verify-isolated-shear.py outputs/isolated-shear-retained \
  --summary outputs/isolated-shear-summary.json --traces outputs/source-loss-traces.json
```

To rerun CUDA, stage the diagnostic scripts and `src/` in a separate root on
a CUDA host, then execute `python scripts/isolated-shear-controller.py` with
CuPy installed. It takes no arguments, writes to that root’s `output/`,
imposes a 180-second worker deadline, and records cleanup. The harness compiles
through NVRTC with explicit `--ftz=false` because CuPy's RawKernel cache adds
a conflicting `-ftz=true`. The first rejected compilation and its reassessment
are retained under `verification/isolated-shear/attempt-1`.
