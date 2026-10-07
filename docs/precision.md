# Exact proof versus hardware precision

Lean's theorem uses mathematical complex numbers and equality for every input.
It has no hardware epsilon. The kernel successfully checked the original
proof, with only the three usual permitted axioms recorded in
`verification/lean-axioms.txt`.

The cost model counts each predetermined scalar multiplication as one gate;
it does not constrain coefficient precision, intermediate magnitudes, or
conditioning. Thus an exact operation-count saving need not yield an accurate
or fast floating-point implementation. A CUDA discrepancy can expose numerical
instability or a translation bug without contradicting this theorem.

The earlier CUDA diagnostic tested the explicit intermediate factorization
`F=N diag(N)^(-1) N.T`, using ordinary transpose. Constants and references used
300 decimal digits. All16 matrix entries at n=4 were also verified exactly in
Gaussian rationals. At every tested length, the high precision factor and
direct DFT agreed to better than1e-269 on six dyadic input vectors.

| n | Factor FP32 | Factor FP64 | cuFFT FP64 |
|---:|---:|---:|---:|
| 8 | 8.63e-7 | 2.71e-15 | 1.12e-16 |
| 16 | 5.47e-5 | 1.17e-13 | 1.15e-16 |
| 32 | 0.826 | 1.73e-9 | 1.42e-16 |
| 64 | 1.69e8 | 0.164 | 1.79e-16 |
| 128 | 1.03e24 | 2.24e15 | 1.76e-16 |

Entries are maximum relative L2 errors across those six vectors. At n=64,
rounding only the factor coefficients to FP64, followed by high precision
arithmetic, produced error0.0376; CPU FP64 produced0.201. These observations
support coefficient sensitivity and cancellation, including outside CUDA.
They test this factorization only, without a speed or saving-circuit claim.

The original completed receipt is `verification/newton-precision.json`.
`scripts/check-newton-precision.py` reproduces it with NumPy, CuPy, and mpmath;
run a copy of the script in a dedicated output directory, since it writes
`results.json` and `arrays-n*.npz` beside itself. Raw arrays from the original
run remain at `~/artifacts/math-130-cuda-20261007-01a11542`.

The new circuit-DAG CUDA check exercises the actual emitted small gate lists,
with exact rational reference outputs and FMA disabled. Its four circuit
identities have exhaustive exact basis certificates; CUDA uses all basis
vectors plus eight seeded dyadic complex vectors for each circuit. Maximum
scaled error means `max(abs(actual-exact))/max(1,max(abs(exact)))`, across all
vectors in that case. This metric differs from the earlier relative L2 metric.

The new check passed in0.65s after imports, on len's RTX4090 with CuPy13.3.0
and CUDA runtime12.6. Python PID505775 and launchPID505771 exited; the three
existing GPU services retained their PIDs. The reused Python environment emitted
an unrelated pre-existing pyannote namespace `.pth` warning at startup; the
CUDA execution and numerical checks completed successfully.
