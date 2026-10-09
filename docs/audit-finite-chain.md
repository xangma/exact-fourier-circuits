# Finite saving, recursion, and local compiler audit

Audit date: 2026-10-09. Baseline: `29fad6d4d3a68fbd806525034e8d07cd373f3d4c`.
This is a bounded review of the finite certificate, the recursive execution
closure, and selected local compiler/preparation arguments. It is not a claim
that every imported proof or every machine retention lemma was independently
reproved. No confirmed contradiction was found in the interfaces reviewed here.
Fresh compilation, axiom reports, and final theorem checks are reported
separately in [audit-verification.md](audit-verification.md).

## Paper identity and evidence

The references below use the September 25, 2026 versions of:

* **E**: *An explicit power saving for the exact discrete Fourier transform*.
* **F**: *Finite tensor savings and exact Fourier circuits*.

The 24 local paper source/PDF blobs were independently checked against the
SHA256 and Git-blob identities in the audit receipt and against the pinned
OpenAI math object `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
See [paper-source-identity.json](../verification/paper-source-identity.json).
Page numbers below are one-based PDF pages, checked against the formfeed page
boundaries in `logs/paper-audit/{explicit,finite}.txt`; they are not guesses from
LaTeX line numbers. The complete E §2 and §3 source arguments, E Appendix A.1,
and F §2 generation/amplification argument were read. F §3 is cited as the
upstream transfer interface; its entire imported formal proof was not reaudited.

Graph evidence used Verify tier, project `exact-fourier-circuits`, generation
`2026-10-07T17:50:28Z` (ready, 4174 nodes, 11147 edges, main-checkout root).
The graph is older than the strong uniform modules. Relevant searches were
fully paginated, but `UniformRecursive*`, the selected local/preparation
modules, and the additional zero-free producers returned `not_tracked` coverage.
`ExplicitSeed`/`ExplicitSeedBudget` have recorded partial ranges;
`MasterBudget` and `TripleColumnAction` have whole-file `parse_unusable`
coverage. Claims about these files therefore use direct source inspection,
not graph absence or inherited exhaustive claims.

## Finite certificate and its operational boundary

`ExactFourierCircuits.ExplicitSeedBudget.parameter_formulas`, `.padding`,
`.residual_balance`, `.strict_margin`, and `.proposed_count_saves` match the
fixed network arithmetic in E §2.1–2.3: (2.2), (2.4), (2.8), (2.9), PDF
pp. 5–9; padding is (2.10), p. 11; the column choice uses Lemma A.1, p. 25.
In particular, `residuals` denotes the **padded** coefficient
`S = W* m − Δ`, not the unpadded `s` in (2.8). The closed arithmetic alone
does not establish a circuit action or count an actual word.

That missing connection is supplied at the reviewed endpoint by
`ExactFourierCircuits.ExplicitSeed.word_matrix` and `.word_calls`/`.word_saves`:
the correctness identity and strict call saving refer to the **same**
`ExplicitSeed.word f`. This word includes the chronological master network,
terminal correction, canonicalization, padded roles, and role axes. The matrix
proof explicitly uses `TripleColumnAction.corrected_stages_endpoint` and the
packed master endpoint before applying the padding theorem. The paper
counterparts are Proposition 2.4, E p. 10 (arbitrary auxiliary roles and
spectators), and Lemma A.1, p. 25 (finite certificate). The complete scalar
network argument is E Lemma 2.1, p. 6; nested Walsh residual cancellation is
Lemma 2.2 and (2.5)–(2.6), pp. 6–7; binary chronology, including reversed
second stage, is Lemma 2.3 and (2.7)–(2.9), pp. 8–9.

`ExactFourierCircuits.ExplicitSeed.witness` and `.finiteWin` have no
circuit-action or call-count hypothesis left for a caller. They provide the
finite-win interface of F Definition 2.1 and (2.1), p. 6.
`ExactFourierCircuits.ExplicitSeed.main` then applies the imported
`OAI.ExactFourier.win_to_fourier`. F Lemma 2.2 (positive generation),
pp. 6–8, and Lemma 2.3 with (2.5)–(2.7) (tensor amplification), pp. 8–9,
explain that existence-transfer framework.

This is a symbolic finite `List` construction and existential theorem. No
astronomical word was evaluated, exported, or executed by this audit.
`ExplicitSeed.main` is a nonuniform circuit-existence result; it does not by
itself prove a running uniform machine. The separate uniform route below is
essential. A definition in a `noncomputable section` can still denote a fixed
finite Nat bytecode list, but that fact does not establish that a practical
executable artifact has been extracted or run.

## Recursive execution and the child premise

E Theorem 2.6, PDF pp. 11–12, writes `k = m f + r`, applies all fixed network
rows in complete batches, recursively computes each residual direction at
`f = floor(k/m) < k`, and finishes the remaining `r` axes. Lemma 2.5,
pp. 10–11, supplies integer index enumeration. The normalized recurrence is
`t(k) ≤ A + λ t(floor(k/m))`; (2.10), p. 11, specifies the same saving
coefficient and exponent used for its geometric unrolling on p. 12.

The reviewed operational chain is:

1. `ExactFourierCircuits.UniformRecursiveSavingProgram.program`: a finite
   instruction list assembled from a fixed part order, literal piece lists,
   and Nat program-counter relocation. This is the actual program subsequently
   used in the execution theorems.
2. `ExactFourierCircuits.UniformRecursiveCoreSchedule.execution` and
   `UniformRecursivePrintedBody.execution`: connect the printed fixed network
   and residual direction schedule to its action, with `SmallerBodies` still
   explicit. `UniformRecursiveWholeValues.suffix_values` connects the residual
   suffix and remaining axes to the full tensor output. These register,
   frontier, and stack contracts are implementation details of E's serial
   recursive batches, not separate paper assumptions.
3. `ExactFourierCircuits.UniformRecursiveLargeNode.execution` and
   `UniformRecursiveLargeChild.execution`: consume that explicit smaller-call
   contract. These lemmas considered alone are conditional; they must not be
   reported as a closed recursive algorithm.
4. `ExactFourierCircuits.UniformRecursiveChildInduction.execution` uses
   `Nat.strong_induction_on`. Its local `childIH : SmallerBodies ...` is
   constructed from `ih j hj`; it is not supplied externally.
   `.smaller` packages the discharged induction motive. The prepared analogue
   is `.execution_prepared`/`.smaller_prepared` in
   `UniformRecursivePreparedChildInduction.lean`.
5. `ExactFourierCircuits.UniformRecursiveRootExecution.execution` and
   `.execution_prepared` pass those closed child theorems to the root branch.
   Neither endpoint asks the caller for a child circuit, child matrix action,
   child execution oracle, or a separately chosen child result.

The root endpoints still require ordinary machine-entry conditions: present
input data, code and address bounds, stack/frontier room, fixed constants, and
the specified register header. This bounded review does not replace the final
empty-start producer chain that discharges those entry conditions.

`ExactFourierCircuits.UniformRecursiveRootExecution.prepared_of_execution`
constructs the prepared run and uses execution determinism to identify its
terminal state with **any actual halted run of the same program and initial
state**. Thus later preparation can use the prepared-tag invariant of the
actual run, rather than silently switching to a different witness state.
Unrelated heap cells are allowed to have dependent tags.

There is a conservative cutoff difference. E Theorem 2.6 uses
`K = m(71+1) = 72,000,000`, whereas
`UniformRecursiveSavingProgram.threshold = ExplicitSeedBudget.bits =
6,544,863,000,071`. The latter is a much larger fixed base regime.
`ExactFourierCircuits.UniformRecursiveRuntimeBridge.chargedCost_recurrence`
handles the intermediate range by enlarging the base constant; its
`.nat_critical_bound` and
`ExactFourierCircuits.UniformRecursiveActualRuntime.actual_critical_bound`
recover the same critical exponent. The program has not been audited as a
literal implementation of the paper's smaller cutoff.

`ExactFourierCircuits.UniformRecursiveTypedLargeCost.large_node_bound`
charges printed body work and call/return control against that recurrence.
The reviewed source includes actual group call/return structure, not only an
abstract tensor-cost formula. Detailed correctness of every residual
gather/scatter and every group-loop retention proof remains outside the
independent leaf review below.

## Local layers and preparation

The following selected correspondences were checked against the complete
local argument in E Proposition 3.1 and Lemmas 3.2–3.5, pp. 12–18.

| Reviewed declarations | Paper argument and qualification |
| --- | --- |
| `ExactFourierCircuits.UniformNewton.fourier_factorization`; `UniformNewton.Preparation.productProgram`, `.inverseProgram_admissible`, `.table_run` | Lemma 3.2, (3.1)–(3.2), p. 13: `F = N D⁻¹ Nᵀ`, with shared product and inverse tables. Products can include `H_r = 0`, but the inverse program only divides by `H_j` for `j < r`; primitive-root hypotheses prove those denominators nonzero. The `r = 1` endpoint does not divide by `H_1`. |
| `ExactFourierCircuits.UniformRadixTwoDAG.run_fft`, `.fanout_bound` | §3.2, (3.3), p. 14: radix-two convolution DAG with bounded depth and fanout. Selected construction/action/count endpoints were inspected; the entire serialization and fanout proof was not reread. |
| `ExactFourierCircuits.UniformToeplitzCrossDAG.toeplitz_cross_eval`, `.crossReplay_spec` | Lemma 3.4, (3.4)–(3.10), pp. 15–16: reciprocal series, cross block `BT_p⁻¹`, rank-three displacement, finite shift sum, and two convolutions per outer product. The three terms are retained even when coefficients vanish; no complex rank test is used. |
| `ExactFourierCircuits.UniformToeplitzChunkWord.Placement`; `UniformWorkspacePlanner.selected_fit` and `.fallback_below_196` | (3.11), pp. 16–17: integer gate/borrowed/end-point fit, largest admissible chunk, bounded direct fallback. Placement separates data and borrowed coordinates. Exact-width operation is a restored-workspace requirement, not permission to assume zero scratch. |
| `ExactFourierCircuits.UniformLocalFourierLayers.schedule_matrix`, `.preparedSchedule_matrix`, `.specifiedSchedule_matrix`; `UniformLocalFourierWord.word_matrix` | Lemmas 3.4–3.5, pp. 17–18: balanced lower/upper Toeplitz schedules and diagonal scaling compose to the specified Fourier matrix. The selected schedule proof and its preparation interfaces were checked; not every rendering/matching proof was independently audited. |
| `ExactFourierCircuits.UniformLocalPreparationDAG.finish_scales_ne_zero`; `UniformLocalPreparationReferences.fourierSchedule_matrix`, `.canonical_fourier_action` | Lemma 3.4 preparation discussion, p. 17, and §3.4, p. 18: one shared arithmetic DAG supplies coefficient references and nonzero scales. Structural choices depend on integer metadata. |
| `ExactFourierCircuits.UniformLocalShear.word_matrix`, `.word_calls` | (3.12)–(3.14), pp. 17–18: two fixed three-forward-`C` blocks for every coefficient, including zero. The nonzero split is `κ = 1 + μ conjugate(μ)` and `μ − κ`; the schedule always has six `C` calls. |

E Lemma 3.3, pp. 14–15, explains the dirty replay needed by these schedules:
compute/copy/reverse, then a source-suppressed negative replay; arbitrary
borrowed contents are restored. Output uses count toward fanout, so greedy
edge coloring uses `2δ−1` colors. These premises matter when reading a
`Placement` or replay endpoint. This audit checked the paper's full argument
and the selected implementation interfaces, not the complete transitive
formal proof of every replay implementation.

`ExactFourierCircuits.UniformScalarPreparation.Program` has only rational
constants, root references, and arithmetic operations referencing earlier
nodes. There are no array-input leaves or scalar-test branches in that syntax.
Its admissibility predicate requires nonzero divisors; it is a mathematical
side condition proved for the constructed table, not a runtime zero test or a
fallback oracle. Inverse-root evaluation provides coefficient conjugates
without conjugating array inputs.

`ExactFourierCircuits.UniformLocalFactorDispatchMachine.execution` is an
intermediate physical producer with three Nat-metadata branches. It still
requires `Processed` and coefficient `Sources` from earlier producers.
Its conclusion provides the requested factor result without a supplied row,
permutation, count, or factor-pool result, but its entry bank facts must not be
omitted when reporting its theorem strength.

## Actual zero-free route in the final import cone

`UniformDiagonal.lean` was annotated as supporting algebra: its common
sum-of-squares shift is a finite-family variation of (3.14), not the literal
single-coefficient choice in E. **It is outside the final theorem's import
closure.** The legacy `UniformZeroFreeDiagonalMachine` /
`UniformPreparedZeroFreeDAGMachine` route must not be presented as the
substantive final execution dependency.

The actual route was checked further by direct inspection of program
definitions, key contracts, and producer composition; these files were not
changed after the Lean annotation freeze:

* `ExactFourierCircuits.UniformZeroFreePairShearMachine.prep` has 18 literal
  operations. It loads `μ` and its prepared conjugate, computes `κ` and
  `μ−κ`, and computes the four variable scales by field operations.
  `.prep_scales`/`.prep_bounded` use the proved nonzero identities;
  `.complete_action`, `.execution_result`, and `.six_kernel_calls` connect
  the actual two-block execution to the arbitrary shear and its six calls.
  No branch tests a complex coefficient, including `μ = 0`.
* `ExactFourierCircuits.UniformConjugateLocalPreparation.setup` physically
  inverts the already selected unit root. Its
  `.preparation_execution_budget`, `.outputs_conjugate`, and `.g_conjugate`
  identify the Newton/reciprocal outputs at the inverse root with coefficient
  conjugates. `UniformSeedConjugatePreparation.execution` compacts these
  outputs. `UniformAllAxisConjugatePreparation.initial_execution` is a closed
  empty-start run with the retained original compact banks and one master-root
  request; the conjugate driver introduces no additional input/root request.
* `ExactFourierCircuits.UniformConjugateRankSpectrumPreparation.execution`
  selects the produced conjugate `H/G` lanes, runs the six kernel-spectrum
  producer, and physically reverses seven frequency blocks.
  `.kernels_conjugate` and `.bankValue_reverse` establish coefficientwise
  conjugation. `UniformConjugatePackedMatchingPreparation.produced_sources`
  derives the decoder's `Sources` from retained original banks plus this
  newly executed spectrum producer.
* `ExactFourierCircuits.UniformMatchingConjugateLoadMachine.execution_from_row`
  decodes positive, negative, and real-constant coefficient addresses using
  Nat branches. Negation and loads are charged. Its `Sources` remain an
  explicit earlier-stage contract.
  `UniformGlobalMatchingScaleMachine.row_loaded`, `.prepared_tail`, and
  `.row_complete_execution` then compute and store the nine physical
  diagonal lanes through the actual zero-free `prep`; inactive factors are
  one and the matching endpoints are distinct. This is the physical factor
  producer used by the final local-dispatch route.

This establishes the inspected producer path and avoids attributing final
strength to a legacy helper. It is not an independent full review of all
allocation/register/frame proofs in those producer modules, or of the final
caller composition that transports their contracts into every invocation.

## Changed sources, preservation, and limits

Only comments were added in this subtask. All 25 changed Lean files have the
same noncomment token stream as baseline, checked with a nested Lean-comment
stripper. Original SHA256 values are recorded in
`logs/paper-audit/finite-chain-original-sha256.json`. The annotated modules are:

```
ExplicitSeed                 ExplicitSeedBudget
UniformRecursiveSavingProgram
UniformRecursiveChildInduction
UniformRecursivePreparedChildInduction
UniformRecursiveRootExecution
UniformRecursivePreparedRootExecution
UniformRecursivePreparedExecution
UniformRecursiveActualRuntime
UniformRecursiveTypedLargeCost
UniformRecursiveLargeNode    UniformRecursivePrintedBody
UniformRecursiveCoreSchedule UniformRecursiveWholeValues
UniformNewton                UniformDiagonal
UniformRadixTwoDAG            UniformToeplitzCrossDAG
UniformLocalFourierLayers     UniformLocalPreparationDAG
UniformLocalPreparationReferences
UniformLocalFourierWord       UniformLocalShear
UniformToeplitzChunkWord      UniformLocalFactorDispatchExecution
```

The seven historical source-limit files were independently checked byte for
byte against baseline and preserved: `GateFrames`, `TripleInvocationFrames`,
`TripleSchedule`, `UniformAllAxisSeedPreparation`,
`UniformGlobalLocalPreparation`, `UniformLocalSeedTableMachine`, and
`UniformNewtonTableMachine`. Their exact hashes are bound by existing verifier
whitelists; surrounding comments supply citations without changing them.
No `OAI` file, generated checker, theorem statement, proof term, program, or
numeric parameter was changed in this subtask. No builds were started by this
subtask; the parent audit owns fresh canonical verification.

Unreviewed scope includes a full leaf audit of the Walsh/Gray/binary frame
proofs and terminal canonicalization underlying `TripleSchedule`; the entire
`MasterBudget` proof (its selected seed/count endpoint was inspected); every
residual direction/gather/scatter and group-loop retention proof; the full
radix-two and Toeplitz fanout/serialization proofs; all local rendering,
coloring, workspace asymptotics, and frame proofs; the complete physical
factor-allocation/caller cone; the upstream `OAI` transfer proof; and the final
all-length CRT/chirp/synchronization/axis/cache/asymptotic closure, which is
covered by other audit parts. Annotation of a module is not a claim that all
its dependencies received an independent mathematical review.
