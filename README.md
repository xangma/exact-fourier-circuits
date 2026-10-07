# Exact Fourier circuits

An exact-arithmetic circuit engine, a lazy constructive saving seed, and a
pinned Lean verification project for the result described in `math/lean/docs/130.md`.

The [investigation plan](PLAN.md) records completed work, next steps, and the
evidence required to connect the explicit construction to Lean and assess its
numerical stability.

The installed proof checks successfully with Lean **4.34.1** and the upstream
Mathlib revision. The 51 upstream modules are unchanged. The theorem, five
kernel/shear identities, and eleven projection/network identities have axiom
closures containing only `propext`,
`Classical.choice`, and `Quot.sound`.

## Run

The local checkout already has `.venv` and the Lean dependencies installed.

```sh
cd ~/repos/exact-fourier-circuits
.venv/bin/exact-fourier demo
.venv/bin/exact-fourier seed --h 100 --prefix 10 --output outputs/seed.json
.venv/bin/python -m unittest discover -s tests
./scripts/verify-lean.sh --skip-cache
./scripts/verify-projection.sh
```

For a fresh checkout, `./scripts/setup.sh` installs the Python environment,
the pinned Lean toolchain, and the pinned Mathlib dependencies/cache, then
verifies the proofs. Mathlib's cache requires several GB. CUDA is optional:
install `.venv/bin/python -m pip install -e '.[cuda]'` on a CUDA12 machine.

## What is implemented

| Component | Result |
|---|---|
| `scalars.py`, `circuit.py` | Gaussian rationals, chronological add/subtract/scale DAGs, exact basis certificates, JSON export |
| `words.py` | Fixed-kernel calls, invertible scalings, permutations, three-forward-call shear compiler, strict finite-win verifier |
| `gf2.py`, `directional.py` | Sparse binary orthonormal complements and bounded pairwise expansion of directional kernels |
| `network.py` | Complete lazy scalar/frame network, terminal corrections, padding and role axes; exact integer saving budget |
| `projection.py`, `dyadic.py` | Bounded binary projections of the complete network and fast exact checkpoint references |
| `lean/` | Original existence theorem and new exact matrix identity proofs |
| `scripts/check-cuda.py` | CUDA scalar-DAG evaluator in FP32/FP64 against exact references |
| `scripts/check-projected-cuda.py` | Complete projected-network CUDA execution, compiled/direct shear controls and stage diagnostics |

The constructive seed specializes to

```
C = [[(1+i)/2, (1-i)/2], [(1-i)/2, (1+i)/2]].
```

Its structured program represents a word computing `C` to the tensor power
`b`, with fewer than `b*2^(b-1)` forward C calls. For the companion paper's
`h=100`, the three-call shear implementation gives

```
f = 6544863
b = 6544863000071
width = 2^6544863000071
saved calls = 847159236000000 * 2^6544862999999
```

Counts retain their exponential factors symbolically. Even the smaller
`h=25` choice has `b=5951265671`. Neither instance can be materialized.
`seed --prefix` exports a bounded prefix of the actual lazy instruction stream,
alongside its budget; the prefix is explicitly incomplete.

The existing Lean existential proof is noncomputable. This Python construction
implements the companion paper's explicit witness, and has **not** been
formally connected to that proof. It also does not implement the entire
Toeplitz-to-Fourier compilation pipeline or a practical faster FFT. Small
examples are correctness checks and have no claimed call saving.
See [construction audit](docs/constructive-seed-audit.md) for formulas and scope.

## Exact and numerical checks

The Python suite has 73 passing tests. It checks all entries of small circuit
identities, dirty auxiliaries, directional inverse formulas, binary bases,
resource bounds, and frame cancellation on four exact Walsh modes of the
complete `h=4` network. Those modes cover selected invariant subspaces rather
than every possible array.

The complete projected network was also checked exactly on three dirty arrays
at each of two address widths, then executed in **48 CUDA cases on len**.
Worst final relative L2 errors were `1.59e-6` in FP32 and `2.06e-15` in FP64.
Compiled three-C shears produced roughly 2.2–2.3 times the error of direct
shears on stress inputs; FMA on/off arrays were identical. These projections
measure a bounded implementation, with no claim of a saving or full-width
stability. See the [report and checkpoint plot](docs/projected-stability.md)
and [projection contract](docs/projection-contract.md).

For fixture generation and plotting, install
`.venv/bin/python -m pip install -e '.[research]'`.

Four exported small circuits were executed on **len / RTX4090**, with 60 input
vectors per precision. The maximum scaled output errors were `8.58e-8` in FP32
and `1.60e-16` in FP64. Results and source/fixture hashes are recorded in
[verification/cuda-results.json](verification/cuda-results.json).

To reproduce with CuPy installed:

```sh
.venv/bin/python scripts/make-cuda-fixture.py outputs/cuda-fixture.json
CUPY_CACHE_DIR="$PWD/outputs/cupy-cache" .venv/bin/python scripts/check-cuda.py \
  outputs/cuda-fixture.json --output outputs/cuda-results.json
```

The [earlier Newton-factor precision diagnostic](docs/precision.md) is also
included. It shows severe floating-point instability in that particular
factorization at larger lengths. It does not refute an exact-complex theorem
or establish instability of every permitted circuit.

## Provenance

The upstream theorem is from [openai/math](https://github.com/openai/math),
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
[lean/UPSTREAM_MANIFEST.json](lean/UPSTREAM_MANIFEST.json) records all source
hashes and dependency pins; [lean/UPSTREAM.md](lean/UPSTREAM.md) records licensing.
The algorithm follows the companion preprint *An explicit power saving for the
exact discrete Fourier transform*, September 25, 2026, from the same checkout.
Original source headers are retained. Apache2.0: see [LICENSE](LICENSE).

Observed verification receipts live in `verification/`; generated circuits,
large caches, Python environments and execution logs are ignored by Git.
Codebase graph indexing timed out; the audit used bounded exact source reads.
