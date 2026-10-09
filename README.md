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

This verifies the subsequential circuit theorem described in `130.md` and the
explicit finite saving construction. The companion paper's stronger single
algorithm for every length, with preparation and indexing costs included, has
not yet been proved here. Work on that target is active on `codex/uniform-fourier`.
The [uniform proof contract](docs/uniform-proof-contract.md) distinguishes the
checked components from the remaining program and cost obligations. The
[component receipt](verification/uniform-components.json) explicitly records
`uniform_algorithm_verified=false`. The [latest checkpoint](docs/uniform-closeout.md)
records separate focused audits of 46 modules/4,720 declaration closures and
17 operational modules/1,798 closures. Their exact-bytecode suites pass 12,329
and 16,320 cases respectively; the new inverse tensor check covers 21,845 exact
matrix entries. The current registry contains 295 modules. Actual native
spectators, direct-leaf orientations and sector/tensor movement are checked.
The complete cache compiler, common recursive execution and global fast
program remain open.

The current uniform work includes one fixed 465-instruction startup program.
Lean proves that it constructs the chirped padded input, signed convolution
kernel, normalization factor and both CRT permutations, copies the complete
index metadata out of local workspace, gathers the input through alpha,
and constructs the inverse beta output table while preserving the prepared banks.
All startup work is charged and bounded by `O(n)`, with polynomial integer
words. Concrete local Fourier layers and the pointwise multiplication loop
are also checked. A literal FFT row printer, sparse prepared-power loop, local Newton/reciprocal
producer and one shared coefficient bank are verified components. Canonical
root extraction preserves the sole master-root request. A fixed 766-instruction program now joins startup to the first selected axis's
local preparation. The shifted FFT interpreter handles the actual mixed input
flags, including prepared padding. A fixed 199-instruction program now joins FFT row printing, canonical root
extraction, prepared powers and mixed-tag interpretation. The one-master-root
shared coefficient DAG and synchronized CRT Fourier identities are also checked.
A fixed 35-instruction program computes the dyadic root table from that master
root. A selected-axis copier retains the five actual Newton/reciprocal coefficient
lanes above every local workspace. A fixed 221-instruction assembly now gathers
strided inputs, writes prepared-zero padding and executes the FFT without
host-side phase writes.
A fixed 935-instruction program now prepares and retains every selected axis's
local seed bank from empty heaps. The 53-instruction selected DFS copies its
radices from protected metadata and enumerates all working addresses in at most
84*L+6 charged steps. A fixed 989-instruction program joins these phases from
empty heaps with charged transitions. A fixed 41-instruction transfer reads the independent beta
inverse and alpha banks between transforms in exactly 18*L+25 steps.
A fixed 769-instruction program now executes exact dyadic cyclic convolution,
including all three FFTs, prepared-kernel multiplication, normalization and index
reversal. All-axis preparation costs O(log^5 n)=o(n); the complete 989-instruction
startup and traversal costs O(n).
Printing the full balanced local compiler and executing the global fast scheduler
remain open.
A fixed 66-instruction tensor monomial interpreter now derives its action from
physical permutation and coefficient banks, with at most 153*L+10 selected-length
steps. A shifted 32-instruction scalar-DAG interpreter has certified divisions
and fresh leaf/result placement. A 49-instruction producer constructs signed
rational leaves from physical integer rows; a 70-instruction assembly copies
root leaves and constructs the complete prepared leaf bank. A 39-instruction
printer now builds interpreter rows from a physical typed DAG tape. One continuous
157-instruction program constructs leaves, prints those rows and evaluates the DAG,
charging every phase transition. A 17-instruction scan prints distinct borrowed
coordinates outside both block intervals; its selected-block theorem derives
capacity from the measured graph size. A 20-instruction producer constructs an
identity permutation and diagonal coefficient bank for the tensor interpreter.
Printing the actual balanced compiler tape remains an obligation.
A 58-instruction measured workspace search now computes the paper's largest
fitting ragged chunk, including the unit-width boundary. A 336-instruction program
prepares the inverse master root and evaluates the same coefficient tapes twice,
producing original and conjugate banks. A 30-instruction producer then constructs
the explicit zero-free shift and reciprocal differences from those physical banks.
The joined 374-instruction program derives those banks and division guards in one
continuous run from the original master root and physical typed/rational tapes.
An all-axis directory driver constructs complete diagonal banks; its continuous
108-instruction producer/tensor assembly derives its action from actual banks.
The joined 1084-instruction program derives its caller setup and gathered input
from the empty state and has a proved linear runtime budget. Converting CRT
coordinates to the complete tensor schedule and executing the fast scheduler remain open.
The 154-instruction convolution printer constructs every typed five-field graph
record from its integer height, with lossless coefficient decoding and bounded words.
An 11-instruction contiguous power writer produces a prepared bank in exactly
`6*N+6` steps from one physical prepared root. The 90-instruction kernel producer
constructs all six padded rank kernels from actual prepared H/G cells, including
zero coefficients, with a proved quadratic preparation bound. The 297-instruction spectrum
producer charges its six FFT/copy passes and root-power bank. The 271-instruction
corrected-cross printer derives all six remapped graphs and final additions from
height and ragged dimensions. A continuous 722-instruction caller now derives kernels, spectra, typed tape and
depth labels from original H/G/master cells, installing every helper header
through charged instructions. Its 799-instruction extension also derives the stable
order/directory and signed coefficient banks continuously. A 132-instruction
caller prepares and colors one actual depth bucket; a 30-instruction filter
prints each selected matching layer. The 186-instruction height caller prepares every actual depth bucket in
`8*K+7` iterations and records each row/color bank. The 835-instruction
seed caller reads the retained axis directory and actual compact inverse-H/G
lanes before executing the 799-instruction preparation; it retains those banks.
The 1046-instruction `UniformSeedHeightPreparation` joins retained-seed preparation
to all-height bucket production and computes the chunk exponent with charged
integer instructions. `UniformChunkMatchingPreparation` joins selection, borrowed
coordinate production, row mapping and matching-axis printing in 215 instructions.
The 1286-instruction `UniformSeedChunkPreparation` joins those phases continuously
from retained selected-axis banks and ordinary caller geometry. No generated
cross tape, selected-row table or ready matching axis is an entry premise.
The 35-instruction depth writer
derives every typed longest-path label from its physical tape in at most
`5*(N+1)+22*G+10` charged steps. A 24-instruction printer then constructs
a stable complete gate permutation and bucket directory from those actual labels;
its quadratic allocation and instruction cost are explicit. A 42-instruction
producer derives the signed coefficient bank and six normalization constants from
the original prepared positive bank in exactly `5*K+56*2^K+31` steps.
The mathematical block traversal now has an exact ordered-list identity with the
sector directory. Its 92-instruction physical metadata producer now derives that
ordered directory and suffix volumes from the original width rows in at most
`130*L+16` steps. The 137-instruction packing DFS derives inverse addresses and gathers exact tagged
values in at most `213*L+20` steps. A 60-instruction producer prints ordered forward shear triples from the actual
typed tape and gate-order bank. A 51-instruction program derives greedy colors
from actual endpoints; degree six implies eleven colors with disjoint same-color
rows. A 55-instruction producer converts actual matching rows into ordered
forward permutations, widths and a physical axis header in exactly
`17*r+8*M+21` steps. A 36-instruction inverse-table producer reverses the
actual rows and derives exact negative coefficient addresses in at most
`25*M+6` steps, including normalization aliases. A 20-instruction scalar interpreter reads actual physical rows and prepared
coefficients in `16*M+5` steps. Its 81-instruction caller executes inverse-table
production, forward replay and inverse replay continuously in at most
`57*M+21` steps, restoring all numeric cells while tracking possible tag growth.
A 14-instruction port mapper and 59-instruction row mapper connect logical
coordinates to the actual borrowed bank and source/target allocation.
`UniformMachineConjugation` is a semantic transport theorem. Actual fresh
five-lane conjugate preparation is proved by the 301-instruction
`UniformConjugateLocalPreparation` and its 466-instruction selected-axis caller,
`UniformSeedConjugatePreparation`. `UniformSeedConjugateRetention` supplies the high-bank frame needed by the 524-instruction all-axis driver; its 1460-instruction wrapper starts from empty heaps and retains both original and conjugate directories, operands and one root request.
The 361-instruction `UniformMatchingPackingPreparation` joins matching-table
production to physical packing, deriving inverse addresses and exact tagged pair
coordinates. `UniformSeedChunkPackingPreparation` consumes the actual seed/chunk
result in a 152-instruction continuation or derives it internally in 1438
instructions. It retains the produced coefficient banks and derives the physical
inverse addresses. `UniformScalarScatterMachine` executes inverse scatter in
12 instructions and exactly `9*L+4` steps. `UniformPackedPairRoundMachine` runs
one C round in 23 instructions and `17*M+7` steps; the 45-instruction
`UniformPackedPairScatterPreparation` joins charged header setup, that round
and inverse scatter in exactly `17*M+9*L+21` steps. Its native-coordinate
values, tail entries and actual OR flags are proved. Matching count remains
an ordinary caller input for that earlier C-round wrapper. The new 422-instruction
six-C matching loop instead reads generated Nat894 and derives its table and
inverse from actual packing. A 2669-instruction caller now joins seed/chunk,
conjugate preparation and matching with charged header setup. It consumes
ordinary physical input/layout headers. The new fixed5375 caller proves the
complete local cross replay; original tape/banks and compatible layout remain inputs.

The registry contains 295 modules. The [latest checkpoint](docs/uniform-closeout.md)
records full audits and exact entry boundaries. With the required rank-kernel
banks, size and displacement identities, the fixed5375 local program adds `M*x`
to the target and restores numeric source/workspace values. The fixed535
record loop executes actual scalar, translation, signed-exchange and padding
children. Fixed79 constructs matching tables across all selected CRT axes from
physical edge inputs; fixed124 derives their suffix volumes and sector directory.
A fixed4306 branch starts from empty heaps and supplies a direct small-length
fallback or single-axis matching preparation. Canonical selected seed/chunk
allocation fits the unchanged `(n+2)^19` budget.

Recursive residual C execution, the all-axis edge producer, compatible global
allocation/metadata retention, final Fourier routing and the fast runtime bound
remain open. The stronger uniform theorem is still unproved and has no registered
proof. Earlier CUDA/JAX experiments and plots keep their existing scope.


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

The upstream theorem is from [openai/math](https://github.com/openai/math),
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
[lean/UPSTREAM_MANIFEST.json](lean/UPSTREAM_MANIFEST.json) records all source
hashes and dependency pins; [lean/UPSTREAM.md](lean/UPSTREAM.md) records licensing.
The algorithm follows the companion preprint *An explicit power saving for the
exact discrete Fourier transform*, September 25, 2026, from the same checkout.
Original source headers are retained. Apache2.0: see [LICENSE](LICENSE).

Observed verification receipts live in `verification/`; generated circuits,
large caches, Python environments and execution logs are ignored by Git.
The graph is now indexed; Lean's whole-file parser gaps require exact source
reads. [Initial foundation receipt](verification/constructive-foundations.json) and
[paper-component receipt](verification/paper-foundations.json) record earlier
snapshots. The [complete construction receipt](verification/constructive-seed.json)
records the final word, source hashes and closed theorem axiom checks.
