# Exact Fourier circuits

An exact-arithmetic circuit engine, a lazy constructive saving seed, and a
pinned Lean verification project for the result described in `math/lean/docs/130.md`.

The [conclusion](docs/conclusion.md) records the completed proof and numerical
assessment. The [investigation plan](PLAN.md) tracks their evidence and scope.
The [JAX investigation](docs/jax-investigation.md) adds fresh Lean replication,
CUDA execution on len, exact-reference checks, FFT comparisons and explanatory plots.

The [proof contract](docs/proof-contract.md) specifies the exact cost models,
coordinate conventions, admissible parameters and proved witness lemmas.

The installed proof checks successfully with Lean **4.34.1** and pinned
Mathlib. The 51 upstream modules are unchanged. The paper-derived literal
`h=100` word now has its exact tensor identity and strict forward-call saving
proved together. [ExplicitSeed.lean](lean/ExplicitSeed.lean) supplies a closed
finite-win witness and derives the Fourier theorem. All 1,101 registered
declarations have axiom closures containing only `propext`, `Classical.choice`,
and `Quot.sound`; see the [final receipt](verification/constructive-seed.json).

The stronger all-length theorem is now proved by
[`UniformFinalDFTExecution.uniformDFT`](lean/UniformFinalDFTExecution.lean), of type
`UniformMachine.UniformDFTStatement UniformExponent.theta`. One fixed finite
program computes the standard unnormalized DFT at every positive length. Its
actual 20-stage execution starts from empty heaps, prepares all caches, executes
three complete Fourier clocks, performs the convolution/CRT transfers, and
emits the final outputs. The same run has one specified root request,
polynomially bounded integer words and a proved charged runtime.

The asymptotic bound is `O(n*(log n)^theta*(log log n)^(4-theta))`, with
`0<theta<1` and `theta<1-2/10^13`. Complex arithmetic is exact and has unit cost
per allowed operation; preparation, scheduling, indexing and heap movement
are charged. The integer/address word bound does not bound complex precision.
This gives no floating-point stability guarantee or measured FFT speedup.
The existing [JAX/CUDA experiments](docs/jax-investigation.md) retain their
bounded empirical scope and do not execute the full saving algorithm.

The [final normal verification](verification/uniform-final-algorithm.json)
passes **1,271 modules and 82,513 declaration closures**, including 3,483
private declarations, with only the three standard axioms and the exact
closed-statement guard. The [independent Main audit](verification/uniform-final-independent-main-audit.json)
also passes. The verifier freshly checks Main, the exact target and full
census, reusing earlier proof artifacts only when their compiler, sources,
bytes and complete dependency lineage match the certified audit.
See the [checkpoint](docs/uniform-closeout.md) and
[uniform machine contract](docs/uniform-proof-contract.md). Older component
receipts record their historical boundaries; their overlapping counts are not
an aggregate audit of this final source snapshot.

## Run

The local checkout already has `.venv` and the Lean dependencies installed.

```sh
cd ~/repos/exact-fourier-circuits
.venv/bin/exact-fourier demo
.venv/bin/exact-fourier seed --h 100 --prefix 10 --output outputs/seed.json
.venv/bin/python -m unittest discover -s tests
./scripts/verify-lean.sh --skip-cache
./scripts/verify-projection.sh
./scripts/verify-construction.sh
./scripts/verify-uniform.sh
python3 scripts/check-uniform-bytecode.py
```

`./scripts/verify-uniform.sh` is the current final-theorem check; add
`--rebuild-all` to freshly compile all 1,271 project modules. Historical
component proof entrypoints now forward to this final verifier. Earlier
bytecode counts below describe retained component diagnostics, which the
final proof audit did not rerun. Reproducing the original checkpoint receipts
requires the matching historical source/configuration snapshot.

The bytecode check exports the current Lean programs and runs 84 exact convolution
cases, three empty-heap startup cases and nine CRT-transfer cases, including
different and coincident CRT maps. It checks dependency tags and charged steps
with rational arithmetic. These bounded diagnostics complement the Lean proofs;
the native transform inputs in the transfer tests are explicit caller fixtures.
It also runs 180 exact zero-free diagonal cases and six guard controls from
explicit prepared coefficient/conjugate caller banks. Results are written to
`logs/uniform-bytecode/fixtures.json` and `logs/uniform-bytecode/zero-free-fixtures.json`.
Another 90 continuous 374-instruction cases start with the original master and
typed/rational tapes, checking derived conjugates, shifts, all dependency tags,
dirty-bank frames and seven expected guard failures. Their receipt is
`logs/uniform-bytecode/prepared-zero-free-fixtures.json`.
The contiguous power writer adds 126 exact cases and three guard controls, written
to `logs/uniform-bytecode/contiguous-power-fixtures.json`. Another 30 physical
metadata cases check all 92 PCs against Lean sector lists, and 24 exact kernel
cases check all 90 PCs against independent Gaussian-rational formulas. Their
receipts are `sector-metadata-fixtures.json` and `rank-kernel-fixtures.json`
in the same directory. A further 40 exact cyclotomic spectrum cases use canonical
roots of orders 4 through 64, and 54 corrected-cross cases compare the physical
tape against freshly exported typed Lean records. Their receipts are
`kernel-spectrum/cyclotomic-fixtures.json` and `cross-topology/runtime-receipt.json`.
The depth writer adds 76 cases (30 pinned typed examples and eight fresh small
examples, each in two layouts); packing adds 270 cases, including local
permutations whose inverse differs from the forward permutation. Their receipts
are `dag-depth/fixtures.json` and `sector-packing/bytecode-results.json`.
The complete command passed **15,613 exact diagnostic cases in 38 suites**. Receipts in
`color-layer`, `cross-depth` and `rank-cross-replay` add 1,665, 484 and 32 cases.
The last suite runs the continuous 799-instruction program from original
H/G/master cells with exact cyclotomic arithmetic and freshly exported formal
runtime budgets. It exercises 788 of 799 PCs, including every new caller
instruction; the 132-instruction bucket caller exercises 131 of 132 PCs.
`inverse-shear` adds 1,656 cases, every one of its 36 instructions, nine guard
checks and 1,602 exact dirty-array restoration checks. These tests execute the
actual signed-coefficient producer at its component boundary; continuous scalar
replay caller composition is checked separately by `dirty-replay`: 798 cases
exercise all 81 continuous instructions and exact tag changes. `scalar-replay`
adds 756 cases, `cross-height` 54, and `chunk-rows` 52. The 40 `seed-rank-cross`
cases consume banks produced by actual empty-state startup, including radix 3
and radix 4, using the true cyclotomic fields for master orders 128 and 24,576.
Its auxiliary arithmetic check independently constructs both cyclotomic
polynomials and compares 250 dyadic operations with the prior exact engine.
The [diagnostic manifest](verification/uniform-bytecode-components.json)
records source and receipt hashes; the portable main runner hashes its stable
inputs automatically. The new seed-chunk suite has 60 generic synthetic radix-256
H/G fixtures, not an actual giant selected-startup witness. The 408 packing
fixtures comprise 336 actual K0 typed-cross `Height.Processed` entry cases and
72 generic logical-layer cases; earlier Height/startup execution is not replayed
by that suite. The 21 conjugate fixtures include nine from actual 935-instruction
startup. These component diagnostics complement the universal Lean proofs.

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
| `lean/` | Original theorem and paper-derived finite saving word, with full action, residual totals, terminal correction, padding, count and closed Fourier conclusion |
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

The Lean word uses noncomputable finite coordinate and basis choices. Its
identity and count are proved without action or count assumptions. The Python
generator follows the same paper, but its equivalence to that Lean word has
**not** been proved; its metadata remains `kernel_verified=false`. The Python
code also does not implement the entire Toeplitz-to-Fourier compilation
pipeline or a practical faster FFT. Small examples are correctness checks
and have no claimed call saving.
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

A focused three-C diagnostic then found a source-restoration failure: with
`t=1`, source `1` becomes `0` beside target `2^24` in FP32 or `2^64` in FP64.
Direct shears preserve it. All 9,360 CUDA cases were independently checked
using exact rational references. Common normalization removes the observed
overflow but does not fix source loss. See [counterexamples and reproducible traces](docs/isolated-shear-stability.md).

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

The [paper playground](notebooks/paper-playground.ipynb) lets you change both
papers' parameters, numerical precision and transform sizes. See its
[launch notes](notebooks/README.md) and the [measured CUDA investigation](docs/jax-investigation.md).

The underlying mathematics and both preprints are by **OpenAI (2026)**:

- [Finite tensor savings and exact Fourier circuits](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf).
- [An explicit power saving for the exact discrete Fourier transform](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf).

The upstream source is [openai/math](https://github.com/openai/math) at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. [lean/UPSTREAM_MANIFEST.json](lean/UPSTREAM_MANIFEST.json)
records its source hashes and dependency pins;
[lean/UPSTREAM.md](lean/UPSTREAM.md) records licensing. Original source headers
are retained. This repository adds the further Lean formalization and
verification tooling, exact circuit software and bounded CUDA/JAX numerical
investigation. Development of those additions used AI assistance.

Use [CITATION.cff](CITATION.cff) to cite this software and
[REFERENCES.bib](REFERENCES.bib) for the two upstream papers. Their BibTeX
entries follow the upstream citation instructions, with links pinned to the
source revision above. Apache-2.0: see [LICENSE](LICENSE), [NOTICE](NOTICE)
and [lean/LICENSE.upstream](lean/LICENSE.upstream).

Observed verification receipts live in `verification/`; generated circuits,
large caches, Python environments and execution logs are ignored by Git.
The graph is now indexed; Lean's whole-file parser gaps require exact source
reads. [Initial foundation receipt](verification/constructive-foundations.json) and
[paper-component receipt](verification/paper-foundations.json) record earlier
snapshots. The [complete construction receipt](verification/constructive-seed.json)
records the final word, source hashes and closed theorem axiom checks.
