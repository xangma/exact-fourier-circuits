# Fourier circuit investigation plan

We are investigating the result described in `math/lean/docs/130.md`: why its
exact circuit saving is valid, how an explicit saving circuit realizes it,
and whether that construction remains accurate in floating-point arithmetic.
The deliverables are a checked constructive argument and a reproducible
numerical assessment, with their remaining limitations stated explicitly.

The current replication and plotting work follows the
[JAX experiment contract](docs/jax-investigation.md). It checks the original
Lean theorem afresh, executes feasible projected components in JAX/CUDA,
compares true DFTs with standard FFT methods, and plots exact saving scale,
numerical error and synchronized runtime. The enormous saving witness remains
symbolic; the stronger uniform proof is a separate unfinished milestone.

Lean's theorem concerns exact mathematical operations and a particular cost
model. CUDA tests concrete finite-precision implementations. Our specialized
kernel is `C = [[(1+i)/2,(1-i)/2],[(1-i)/2,(1+i)/2]]`; its tensor-power saving
seed is one part of the broader Fourier argument. We must connect those parts
explicitly before claiming an executable faster DFT.

1. **Establish the baseline — completed.**
   The original theorem checks with pinned Lean/Mathlib and 51 unchanged
   upstream modules. The exact Python engine, lazy construction, and bounded
   projections are implemented. All 73 Python tests and eleven new Lean
   projection/network identities pass. Forty-eight CUDA cases on len compared
   compiled three-C shears with direct shears, in FP32/FP64 with FMA on/off.
   Worst relative errors were `1.59e-6` and `2.06e-15`; compiled shears produced
   roughly 2.3 times the stress-input error. Raw outputs were independently
   checked. See the [experiment report](docs/projected-stability.md).

2. **Write the precise proof contract — completed.**
   Identify the exact theorem statements, circuit semantics, allowed free
   operations, charged calls, tensor coordinate convention, and parameter
   assumptions. Map the paper's explicit construction and Python objects to
   those definitions. Include the tensor-power-to-Fourier bridge and distinguish
   what is already proved from what the implementation still assumes.
   **Deliverable:** a dependency map and an explicit list of missing lemmas.
   **Completion:** every claimed output identity and saving count has a named
   statement and specified hypotheses.
   See [proof contract](docs/proof-contract.md). Its dependency map records the
   scalar/call-cost distinction, coordinate transport, admissible parameter
   range and completed action/count proofs. The q=2 bridge now receives the
   actual word and reuses the upstream Fourier transfer.

3. **Prove the specific binary frame construction — completed.**
   Formalize the incidence/complement identities, residual subspaces, signed
   weights, and orthonormal bases over GF(2). Instantiate the existing general
   dirty-auxiliary and frame-telescoping proofs with this construction. Prove
   the terminal correction and arbitrary auxiliary-data behavior.
   **Deliverable:** Lean modules proving the actual network's exact action.
   **Completion:** the proofs cover the required parameter family, rather than
   only sampled inputs or generic algebra with an unproved frame hypothesis.
   Checked components now include triple-incidence cancellation, successful
   triple/pair pivots and actual complement bases, tensor weights, signed Walsh
   operators and terminal correction, all eleven symbolic residual table shapes,
   and the three-axis scalar network with the actual stage-two reversal.
   Actual per-invocation frame labels, concrete consecutive-stage coordinate
   identities, column lifts and a literal free terminal correction now compile.
   `TripleSchedule` now assembles the actual chronology and physical role
   embeddings. `TripleStageAction`, `TripleColumnAction` and
   `ColumnTerminalFlat` prove the endpoint and correction for every array;
   `InvocationBudget` totals the actual residual ranks.

4. **Connect the construction to a saving word and its cost — completed.**
   Translate directional layers, compiled shears, padding, permutations and
   scalings into Lean's chronological word model. Prove the coordinate
   identification, output tensor identity, and forward-call count. Derive the
   strict saving inequality for an explicit valid parameter choice. Keep the
   construction symbolic: even the current smaller saving choice has billions
   of address bits and cannot be materialized.
   **Deliverable:** a kernel-checked constructive finite-win statement with
   the paper's budget. **Completion:** correct action and strict saving are
   proved together, without `sorry`, custom axioms, or native decision shortcuts.
   Literal three-C shears, directional layers, signed frame words, pointwise
   role lifts and the ordinary tensor compiler now have exact action/count
   proofs. Actual neighbor, edge and physical role cardinalities are checked.
   `MasterBudget` connects the actual count, correction and padding to the
   h=100 saving. `ExplicitSeed.word_matrix` and `word_saves` prove identity and
   saving for the same literal word. Its `witness`, `finiteWin` and `main` are
   closed proofs. Integrated verification passed all 1,101 registered axiom
   checks, using only standard Lean foundations and 51 unchanged upstream
   modules. [Final receipt](verification/constructive-seed.json).

5. **Investigate numerical stability — completed within the stated bounds.**
   First isolate the three-C shear: measure target error and failure to restore
   its source on cancellation-sensitive and wide-range inputs. Use exact or
   higher-precision references and compare arithmetic orderings and equivalent
   scaling choices. Then vary projection maps, address width and construction
   height where resource sizing permits; otherwise test bounded stage blocks.
   Track stage errors, small-output accuracy, intermediate growth, norm drift
   and nonfinite events. Set the accuracy criterion before judging a variant.
   **Deliverable:** retained counterexamples or an error-growth characterization,
   with controls that identify the responsible operations. **Completion:** we
   can explain the observed failure using exact references and chronological
   rounding traces. The 48 projected-network cases and 9,360 isolated-shear
   cases are retained and independently checked. Normal finite inputs expose
   complete source loss in the literal three-C implementation in FP32/FP64;
   direct shears preserve the source. Common normalization removes observed
   overflow but retains source loss. Passing small projections does not
   establish full-width stability, and a full-width characterization remains
   unavailable. [Numerical report](docs/isolated-shear-stability.md).

6. **Assess practical meaning — completed.**
   Once the exact bridge and numerical behavior are understood, identify any
   feasible DFT instance and compare its accuracy, memory and runtime with an
   ordinary FFT under equivalent conditions. If the saving construction remains
   infeasible, document its symbolic saving and numerical limits instead.
   **Deliverable:** a supported conclusion about exact validity, stability and
   practical usefulness, each backed by its own evidence.
   The selected seed has 6,544,863,000,071 address bits and cannot be
   materialized. It provides an exact asymptotic saving through the verified
   bridge, with no feasible FFT benchmark or finite-precision accuracy claim.
   [Conclusion](docs/conclusion.md).

The planned investigation is complete at these scopes. Formal equivalence of
the Python producer to the Lean word remains unproved, and Python's
`kernel_verified` flag remains false. A producer translation proof or a
numerically safer compiler would be separate follow-up work; neither is
needed for the completed exact Lean witness and bounded CUDA assessment.

The next investigation is to formalize the explicit construction paper's
stronger single algorithm at every length, including its scalar preparation,
schedule construction and address-work bounds. That theorem is not implied
by the currently checked subsequential `MainStatement`.

Work is active on `codex/uniform-fourier`; the [uniform proof contract](docs/uniform-proof-contract.md)
records the stronger operational statement, completed components and remaining
links. The full uniform theorem is not yet proved.

The tensor monomial interpreter now has a physical-bank-to-action proof with a
linear selected-length instruction bound. The shifted scalar-DAG interpreter,
signed-rational leaf producer and assembled root/rational leaf preparation are
checked. Actual topology printing, DAG execution and integer workspace search
now have component proofs. Connecting their physical local layers to the global
saving scheduler remains; generic topology/rational tapes are entry premises
until the corresponding producer is joined.

The fixed global startup has a composed 465-instruction execution proof;
a 766-instruction extension now prepares the first axis from the empty state. It initializes and protects the actual CRT permutations while retaining
all chirp operands and normalization, gathers the input through alpha and
constructs the inverse beta output table. A shared recursive coefficient DAG,
actual FFT row and prepared-power producers, a mixed-tag shifted interpreter
and tensor-fiber addresses are checked.
The complete 199-instruction dyadic FFT producer/interpreter and the closed
single-master-root typed coefficient schedule now check. Identity-padded slot
synchronization plus the generated alpha/beta CRT maps proves the working DFT
identity. Actual dyadic-root sizing/extraction, retained local coefficient lanes,
and strided input gathering plus prepared padding are now charged RAM programs.
All-axis seed preparation now runs from empty heaps in one fixed 935-instruction
program. Selected traversal and the beta-to-alpha array transfer have linear
charged instruction bounds. Actual all-axis preparation is O(log^5 n)=o(n), and
the joined 989-instruction startup/traversal is O(n). Dyadic cyclic convolution
now executes all three FFTs and normalization in one fixed 769-instruction
program. The next decisive link is the charged balanced local
topology/coefficient printer and global saving-network scheduler, followed
by three-transform assembly and its actual runtime bound. The proved larger
local layer constant is covered by a scaled reserve; realizing that reserve
operationally is still required.

Every experiment will have explicit memory/work limits, a deadline, input and
source hashes, retained logs and a stop command. Remote jobs will preserve
existing services. Each milestone will report implementation, exact checks,
Lean verification and observed CUDA results separately. A failed check will
trigger reproduction and competing-hypothesis tests before another patch.

The current local-compiler milestone closes row relocation and DAG execution:
a 39-instruction printer consumes a physical typed node tape, and a continuous
157-instruction assembly constructs leaves, prints rows and evaluates all nodes.
A 17-instruction scan realizes the paper's ascending borrowed-coordinate choice
under its actual measured capacity bound. A 20-instruction diagonal-bank producer
feeds the physical tensor interpreter. These components retain the master root,
protected metadata and unrelated banks. The typed/rational tape producer, complete balanced local compiler and recursive
global scheduler remain required before the stronger theorem can be claimed.

Measured workspace selection now executes all ragged pair checks with actual
integer instructions. Original/conjugate coefficient preparation and the explicit
zero-free shift now compose into one charged 374-instruction execution from the
original master root and typed/rational tapes. The next local
compiler milestone has a verified 154-instruction convolution topology printer
from integer height; corrected-cross topology, spectra and height preparation
now have charged joined callers. The all-axis diagonal pass installs its own caller headers from
actual empty startup in 1084 instructions and has a proved linear runtime bound.
An actual contiguous power writer charges every bank store, and the fixed
90-instruction kernel producer derives all six physical kernels from H/G. The
297-instruction FFT/copy spectrum assembly and 271-instruction corrected-cross
topology printer are verified. A 35-instruction physical depth writer now derives every typed label. Their
24-instruction bucket printer derives the complete stable gate order from those
labels. The 42-instruction signed coefficient producer computes negative entries
and reciprocal constants from the original positive bank. The continuous 722-instruction caller derives these intermediate banks, tape
and depth labels from original H/G/master cells through charged setup instructions.
A 60-instruction printer derives ordered forward shear triples from the actual
tape/order bank; a 51-instruction program produces physical greedy colors.
Degree six is scoped to one depth bucket. A 55-instruction program derives
matching permutations, width rows and physical axis headers in linear time.
The 799-instruction caller now also derives stable ordering and signed banks.
A 132-instruction caller derives and colors one actual depth bucket, and a
30-instruction filter prints selected matching rows without a supplied selected
table. The whole-height caller now runs all `8*K+7` actual buckets. Logical
ports and physical row relocation are proved from the actual borrowed bank.
The retained seed caller derives H/G from the compact directory, and continuous
scalar dirty replay proves numeric restoration with exact dependency tags.
The 1046-instruction `UniformSeedHeightPreparation` now joins retained-seed
preparation to all-height production with charged chunk sizing. The
215-instruction `UniformChunkMatchingPreparation` joins physical selection,
borrowed coordinates, mapped rows and matching-axis tables. Their continuous
1286-instruction `UniformSeedChunkPreparation` reads the actual selected radix
from the retained directory. `UniformMachineConjugation` supplies semantic
transport only; fresh five-lane conjugate banks are now produced by actual
301-instruction local preparation and the 466-instruction selected-axis caller.
The all-axis conjugate directory remains required.
The block traversal's reversed cons output is proved equal to the exact ordered
sector directory. Its physical 92-instruction metadata scan/DFS derives this
directory and every stack read from original width rows in linear time. The continuous
137-instruction scalar packing DFS/gather is verified, including inverse-address
production and exact dependency tags. Matching table production is now checked from actual matching rows. The
361-instruction `UniformMatchingPackingPreparation` now joins the matching
producer to packing with computed inverse addresses, exact tagged pair
coordinates and the C2 sector identity. It does not execute the six-C rounds
or unpack/restore the workspace.

This integration milestone adds eight modules, all with default normal
Lean builds; the complete fresh audit verified 168 modules and 19,540
permitted axiom closures. The fresh 38-suite diagnostic run passed 15,613 exact
cases. The portable runner hashes stable inputs.
The 60 seed-chunk fixtures use generic synthetic radix-256 H/G banks; the 408
packing cases include 336 actual K0 `Height.Processed` entries and 72 generic
logical layers. The 21 conjugate cases include nine actual startup935 origins.
These are component-boundary tests, not a complete selected-axis FFT run.

Canonical allocation now fits the original `(n+2)^19` word budget.
`UniformSeedChunkAllocation` proves the selected seed-height and chunk layouts,
including a genuine nonempty capacity witness. The 1317-instruction
`UniformCanonicalSeedChunkPreparation` calculates allocation headers from the
actual saved length, derives the helper arguments and executes SeedChunk
continuously; its cost is the old seed/chunk budget plus 31.

The actual seed/chunk result feeds a 152-instruction packing continuation,
including five address copies, a charged zero initialization, the existing
eight setup instructions, Packing137 and halt. Its 1438-instruction full caller
derives the seed/chunk result internally. Both retain actual coefficient banks
and compute the inverse addresses. An honest contiguous source below the
preserved seed prefix remains an input; tensor fibers still need charged gather
or stride-aware packing.

The fixed 23-instruction C-round loop executes every ordered destination/source
pair in `17*M+7` steps. Inverse scatter reads the generated table in 12
instructions and `9*L+4` steps. Their 45-instruction joined caller computes both
sets of helper headers and proves the native-coordinate C action, exact OR tags
and untouched tail, in `17*M+9*L+21` steps. It consumes the actual generated
inverse through a packing-result bridge. Matching count remains an ordinary
caller input. These proofs execute one C round, not the six-C shear.

The conjugate retention proof supplies the full high-bank frame of the unchanged
466-instruction producer. The 524-instruction all-axis driver writes a second
address/width directory and retains every earlier bank under `(n+2)^19`. Its
cost is `29 + sum_j(completeRuntime(r_j)+75*r_j+172)`. A charged
1460-instruction wrapper starts from empty heaps, retaining both directories,
metadata, operands and the single specified master-root request.

Physical conjugate spectra, row-pointer loading, internally prepared six-C
matching execution and complete tensor-fiber movement are now implemented in
separate fixed RAM programs. The spectrum producer uses the actual compact
inverse-H lane3, not Newton-H lane0, and proves every coefficient in all seven
blocks. The matching loop reads its count from actual Nat894 and consumes
producer-derived rows and inverse packing. The whole-fiber gather/scatter
computes axis products once, with linear movement cost and the same canonical
word bound. Fixed network coefficients have a five-value static codec.

The [latest checkpoint](docs/uniform-closeout.md) records exact interfaces,
entry boundaries, diagnostics and the aggregate audit. Seed/chunk, conjugate
preparation and high-data matching now compose in a fixed2669 caller. Actual
inverse matching and per-layer numeric cancellation are proved, as are a
complete fixed42 ordinary binary C tensor loop, its explicit coordinate bridge,
fixed20 output-broadcast tables, and runtime fixed-network record decoding.

Next are the complete six-phase local schedule, saving-network child dispatch,
recursive batches and all-axis/chirp/output routing. The registered instruction
decoder does not execute its children. Per-layer cancellation does not perform
the cross update. Ordinary header/layout entry conditions still need a complete
charged startup. The final cost proof must bound the instructions actually
executed; the older ordinary-base charge is smaller than the new measured
addressing cost and needs a constant-factor allowance. All phases must retain
one common polynomial word bound and root request before an unconditional
`UniformDFTStatement` can close. `uniform_algorithm_verified` remains false.
