# Exact Fourier circuits

An exact-arithmetic circuit engine, a lazy constructive saving seed, and a
pinned Lean verification project for the result described in `math/lean/docs/130.md`.

The [conclusion](docs/conclusion.md) records the completed proof and numerical
assessment. The [investigation plan](PLAN.md) tracks their evidence and scope.

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
`uniform_algorithm_verified=false`.

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
An all-axis directory driver constructs complete diagonal banks; its continuous
108-instruction producer/tensor assembly derives its action from actual banks.
Caller setup for that global pass and the complete fast scheduler remain open.


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
