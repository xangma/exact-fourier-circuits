# All-length construction: paper and source audit

This is a bounded manual audit of the working-length, CRT, chirp, master-root,
three-transform and final cost-composition interfaces. It is not a semantic
audit of all 1,271 modules in the final theorem's dependency closure. The
full-file, partial-file and unaudited supporting-file lists below define the
review boundary. Reading a complete file does not mean independently
re-deriving every tactic proof or every imported result.

All declaration names below have the prefix `ExactFourierCircuits.`. Source
locations refer to the paper-audit worktree; the coverage appendix instead
uses baseline revision `29fad6d4d3a68fbd806525034e8d07cd373f3d4c` so that added
comments cannot shift the stated reviewed and unreviewed ranges.

## Paper identity and evidence

The reference is *An explicit power saving for the exact discrete Fourier
transform*, in `math/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/`,
pinned to OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The parent audit records identity for all 24 paper blobs. This audit also
independently compared these four local files with `git show` at that revision:

| File | SHA-256 |
|---|---|
| `main.pdf` | `670d0115ea2553e65f22167c176d2f31218d4d41726fe4e5702e2b149cad0896` |
| `build/sections/all-lengths.tex` | `9dfb302812971062af2990918c4b02190e3ad0ca8f271dc207241976b23c45c7` |
| `build/sections/synthesis.tex` | `601067c49c2d61c56d0d42ab4a35d4c3d4b2c95d5428e61e44fda71c3dce1d39` |
| `build/sections/introduction.tex` | `341e2b3f2fad1db94305d7b5efc4eb29cc7bd3c6ec69ea68cf9775840ebc3523` |

The complete all-lengths and synthesis TeX sections were read, together with
the model and theorem statements in the introduction. Page references were
checked against the page-separated PDF extraction
`logs/paper-audit/explicit.txt`; PDF page 23 was also rendered and visually
checked (`logs/paper-audit/explicit-page-23.png`). The page numbers below are
PDF pages and agree with the printed numbers at these locations. Appendix A's
finite-algebra/bounded-printer synthesis route was read as an alternative
argument. It is not identified with the implementation's explicit network,
local compiler and synchronized-transform route.

Graph evidence used Verify tier, project `exact-fourier-circuits`, generation
`2026-10-07T17:50:28Z`, 4,174 nodes and 11,147 edges. Targeted final/working/root
symbol search returned zero symbols with complete pagination. Coverage for
the relevant candidate paths was `not_tracked`; other queried Lean paths had
parse/index limitations. Exact source was therefore the evidence for the
claims here. A zero-symbol graph response or a clean recorded-gap result is
not treated as a completeness proof.

## Verified paper locations

| Location | Content and TeX label |
|---|---|
| §1.1, p.2 | Arithmetic model `sec:model`; Theorem 1.1 `thm:main`; constants (1.1) `eq:main-constants`; main cost (1.2) `eq:main-bound`; Corollary 1.2 `cor:decimal`. |
| §4.1, p.18 | Prefix traversal and fewer than `2R` prefixes, (4.1) `eq:prefix-nodes`. |
| §4.2, p.19 | Lemma 4.1 `lem:sector-address`, sector starting address (4.2), incremental address updates (4.3). |
| §4.3, pp.19–20 | Proposition 4.2 `prop:tensor-fourier` (statement p.19, proof p.20); transform cost (4.4); tensor multiplication identity (4.5), `eq:tensor-multiply`. |
| §5.1, p.21 | Lemma 5.1 `lem:prime-lengths`; axis estimate (5.1) `eq:axis-count`; binomial estimate (5.2) `eq:binomial-primes`; selected length (5.3) `eq:working-length`; bounds (5.4) `eq:working-bounds`. |
| §5.2, p.22 | CRT phase identity (5.5) `eq:crt-fourier`; working-transform cost (5.6) `eq:working-transform`; inverse as `L⁻¹ J F_L`. |
| §5.3, pp.22–23 | Chirp identity (5.7) `eq:chirp` (p.22); signed support, three charged transforms and ratio progressions; master root (5.8) `eq:master-root`, strict size bound (5.9) `eq:root-size` (p.23). |
| §5.4, pp.23–24 | Proof of Theorem 1.1 and Corollary 1.2, including logarithmic absorption; polynomial integer/address words and absolute fixed tables continue on p.24. |

## Declaration map and material conclusions

### Selected working length and actual root request

| Qualified declaration | Paper correspondence and qualification |
|---|---|
| `UniformWorkingLength.maximal_product` | §5.1, p.21, maximal odd-prime prefix preceding (5.3). `oddPrime j` is the zero-based enumeration of odd primes, so its first value is 3. |
| `UniformWorkingLength.workingLength_lower`, `.workingLength_upper`, `.binaryFactor_upper`, `.doublingExponent_log_bound` | (5.3)–(5.4), p.21: least doubling gives `2n ≤ L < 4n`, binary factor below twice the next prime, logarithmic doubling exponent. Upper bounds require positive `n`. |
| `UniformWorkingLength.primeCounting_quadratic`, `.oddPrime_upper`, `.binaryFactor_quadratic` | Lemma 5.1, p.21, with an alternative library Chebyshev proof and explicit slack: odd prime at most `64(j+2)²`, binary factor below `128(ell+2)²`. These constants are implementation constants. |
| `UniformWorkingPreparation.selectPrefix_spec`, `.prepare_spec`, `.preparation_isLittleO_input` | §5.1, p.21: counted selection/doubling algorithm and negligible preparation. These functional counted procedures are not themselves the machine-execution theorem. |
| `UniformWorkingCompletion.preparation_execution` | Actual fixed integer program selects the same prime prefix and least doubling from `initial`, with charged ticks and polynomial words. The mathematical `Nat.find` definitions specify the result; they are not uncharged machine instructions. |
| `UniformMasterRootMachine.order_paper_formula`, `.order_bounds` | Exact (5.8)–(5.9), p.23: `D*=(2n)L 2^ceil(log₂(16L))`, positive and strictly below `1024 n³`. `selectedLcm_eq` identifies the selected least common multiple with `L`. |
| `UniformMasterRootMachine.master_execution`, `.divisor_orders`, `.localPowerOrder_dvd`, `.specified_divisor_root` | §5.3, p.23: actual initial-state preparation requests exactly `[D*]`, before input scalars are read. The divisor theorem gives the specified phase, not merely some primitive root; actual exponentiation is a separate charged preparation phase. |
| `UniformRoots.specifiedRoot_divisor_power` | Canonical phase extraction in §5.3, p.23. This algebraic identity alone makes no operational cost claim. |

The machine's proof-only induction/fuel parameters do not occur in its
literal instruction list. The doubling and root-factor loops stop on their
actual integer guards. No extra prime-distribution hypothesis is introduced:
`primeCounting_quadratic` uses Mathlib's `Chebyshev.pi_ge`, rather than
reproducing the paper's binomial argument (5.2) line for line.

### CRT order, signed chirp, and normalization

| Qualified declaration | Paper correspondence and qualification |
|---|---|
| `UniformCRT.fourier_phase`, `.matrix_factorization` | §5.2, (5.5), p.22: CRT idempotents produce local inverse-unit output phases. The canonical local output permutation is explicit. |
| `UniformSelectedCRT.radices_pairwise`, `.radices_product`, `.matrix_factorization` | (5.3) and (5.5), pp.21–22: instantiate CRT with all selected odd-prime factors and the binary fill. |
| `UniformCRTTraversalCycle.alphaPermutation`, `.betaPermutation`, `.crt_standard_phase`, `.permutation_fourier_entry` | §5.2, p.22: the output permutation cancels the inverse unit so each local transform uses its specified standard root. The older traversal machine's whole operational proof was not independently audited; see ranges below. |
| `UniformSelectedPhysicalCRT.producedOrdinal_eq`, `.physical_fourier`, `.physical_action` | §4.1–§4.2, pp.18–19, and (5.5), p.22: reconcile the actual most-significant-digit physical order with the CRT input/output permutations. Address-directory and heap bookkeeping do not have separate paper lemmas. |
| `UniformFastPhysicalCRTCycle.execution` | §4.1, (4.1), p.18, and §5.2, p.22: real table generation with a geometric bound on carry visits gives at most `60(L+a+1)` ticks, rather than a per-element full axis rescan. Its source-directory, table, disjointness and word-fit hypotheses are explicit. |
| `UniformFinalPhysicalTablePrefix.execution` | §5.1–§5.3, pp.21–23: joins actual initial preparation, allocation/cache setup, table headers and fast physical producer. Its result supplies the table caller hypotheses for the subsequent run. |
| `UniformChirp.chirp_identity`, `.specified_chirp` | (5.7), p.22: algebraic quadratic chirp identity. |
| `UniformCyclic.positiveDFT`, `.inversePositiveDFT`, `.signed_interval_injective`, `.support_disjoint`, `.bluestein_positive_transforms` | §5.2–§5.3, pp.22–23: bridge Mathlib's transform convention to the positive exponent convention; use `L ≥ 2n` to separate the signed kernel support; express convolution by three forward transforms with reversal and scaling. |
| `UniformChirpTableMachine.specified_table_execution`, `.linear_cost` | §5.3, p.23: actual ratio updates generate chirp and inverse-chirp banks in `11n+10` ticks; no separate exponentiation per entry. |
| `UniformChirpKernelMachine.kernelScalar_fin`, `.signed_kernel_execution`, `.specified_kernel_execution` | §5.3, pp.22–23: actual prepared scalar values agree with the signed cyclic kernel. The middle loop/frame proof bodies remain partially unaudited below. |
| `UniformChirpPreparation.preparation_execution`, `UniformChirpKernelPreparation.preparation_execution` | §5.3, pp.22–23: charge extraction, progression tables and padded fixed operand; retain one root request and the required prepared banks. |
| `UniformChirpOutputMachine.negativeIndex`, `.value_fourier`, `.output_execution_dft` | Inverse formula in §5.2, p.22, and chirp in §5.3: existing loop reads `(L-j)%L`, applies the prepared `1/L`, then the final chirp, and emits the requested `j`th DFT value. `FinalSpectrum` is a premise at this lower interface and is derived by the actual caller below. |

The physical synchronized schedule tensor-products local schedules over **all**
selected axes, including the binary fill
(`UniformAllAxisSeedPreparation.axisCount` and `.radix`,
`UniformPhysicalSynchronizedSchedule.product`). The paper §5.2 describes an
odd-prime tensor transform followed by a separate radix-two FFT. This is an
implementation variation, not an additional theorem premise. The binary
factor's quadratic axis bound is available, and the actual all-axis cost is
included in `UniformFinalClockCost.clockEnvelope_isBigO_paper`. For positive
`n`, the selected binary radix is at least 2: an odd prime product cannot
equal `2n`. General definitions retain an order-one case, but it is not an
unproved width-one branch in the positive-length final run.

### Same-state three-transform and cost composition

The semantic interface is deliberately separated from execution:
`UniformFinalNumericJoin.physicalFourier` is the usual Fourier matrix
reindexed by `BP` on outputs and `AP` on inputs;
`UniformFinalNumericJoin.HeapTransform` describes its action on real heap
cells. `UniformFinalClockHeapTransform.matrix_eq` and `.heap_transform`
convert a complete actual clock's source and numeric-output postconditions
into that interface. They do not replace the clock with a supplied transform
oracle.

`UniformFinalNumericJoin.three_transform_heaps` receives the actual
`kernelIn`, `kernelOut`, `dataIn`, `dataOut`, `productOut`, `thirdIn`,
`thirdOut`, and `finalOut` states. It derives both the saved prepared kernel
spectrum and `UniformChirpOutputMachine.FinalSpectrum` from the three heap
transforms and the real copies. In particular, its conclusion is not assumed
as its input. Its source permutation before the third transform is
`BP.symm (AP i)`; the final CRT copy uses `BP.symm i`.

The executable chain is:

1. `UniformFinalPhysicalTablePrefix.execution` produces an actual prefix
   run from empty `initial` state to the physical-table boundary, with its
   own preparation, cache and table counts.
2. `UniformFinalKernelAndDataEntry.execution` loads the prepared fixed
   operand into active roles, runs the first actual complete clock, copies
   its prepared spectrum to the saved bank, then loads and gathers the
   padded input into data roles. It returns the first clock's real heap
   transform, tag facts and retained data-entry state.
3. `UniformFinalDFTExecution.execution` calls
   `UniformActualCompleteClockExecution.execution` on that exact data-entry
   state, changing only its program counter for the local call.
   `UniformFinalDataClockProduct.execution` (defined in
   `UniformFinalDataClockProductExecution.lean`) joins that real data run,
   prepared pointwise multiplication and charged CRT movement, producing
   the actual third-clock entry while preserving the saved spectrum/cache.
4. The third complete clock uses this produced entry. Then
   `UniformFinalThirdClockOutput.execution` joins its numeric result, the
   final CRT movement and the concrete chirp-output tail to obtain
   `ComputesDFT n x u` for the same final state `u`.
5. `LocalStages.append` composes those exact intermediate endpoints.
   `UniformFinalOuterSuffix.execution` joins the produced prefix at its
   actual program-counter boundary (6316) and charges the final halt.
   `UniformFinalOuterCostJoin.bound` sums these exact prefix/suffix counts.

`UniformFinalOuterProgram.stagesFor` is one fixed list of twenty stages,
independent of `n` and the input. Stages 9, 14 and 17 use the identical
`UniformActualGlobalClockProgram.program`. Every embedded helper halt becomes
a charged continuation; the outer halt is separately charged. The fixed
kernel transform is therefore charged in full.

Cost declarations refine (4.4), (5.6) and §5.4, pp.19–24; the explicit
register/cache/continuation budgets are implementation bookkeeping, rather
than separately numbered paper assertions:

| Qualified declaration | Role in the closed bound |
|---|---|
| `UniformFinalActualClockCost.child_cost_eq` | Definitional equality between `UniformRecursiveChildInduction.cost` and `UniformActualSectorCost.actualCost`; the operational child cost is the one bounded. |
| `UniformFinalActualClockCost.actual_tick_bound`, `.actual_loop_bound` | Bound actual kernel/diagonal work and independently measured axis counts by the complete-clock envelope. Lower interfaces are conditional on geometry, links and axis facts. |
| `UniformFinalClockCost.clockEnvelope`, `.clockEnvelope_isBigO_paper` | Sum actual axis scan, recursive kernel and diagonal majorants, and establish the paper asymptotic cost. Supporting recursive/axis proof bodies belong to the other audit scopes. |
| `UniformFinalLinearTableCost.tableBudget`, `.tableBudget_bound` | Fast table allowance `60(L+a+1) ≤ 480n` for positive `n`. The final path uses `UniformFastPhysicalCRTMachine`, not the legacy transfer producer. |
| `UniformFinalLinearTableCost.finalBudget`, `.finalBudget_isBigO_paper` | Closed majorant `overhead + 3*clockEnvelope + tableBudget + 20`, including actual continuations. |
| `UniformFinalOuterCostJoin.bound` | The actual prefix count plus actual three-stage suffix count plus the final halt are bounded by `finalBudget`. |
| `UniformFinalStatementBridge.eventual_runtime_bound`, `.of_majorized_execution` | Convert a proved Big-O bound to a positive constant and threshold at least 3, with a polynomial word envelope. This is a conditional adapter, not an algorithm-construction theorem. |
| `UniformFinalOuterEnvelope.of_execution` | Actual final adapter: receives the true initial-state run, output, one-root list and charged majorant; uses proved root and polynomial-envelope bounds. Read here, annotated by the semantics audit. |
| `UniformFinalDFTExecution.execution`, `.uniformDFT` | Caller discharges the operational premises and exports the closed theorem `UniformDFTStatement UniformExponent.theta`. Read here, annotated by the semantics audit. |

The final caller supplies the real complete-clock runs and their numeric,
prepared-tag, frame and cost results. The bridge's root order is fixed from
`n` before quantifying over input arrays, and the actual state records exactly
`[UniformMasterRootMachine.order n]`. The polynomial-envelope conversion
enlarges the same execution's word bound; it does not alter the code or ticks.
Thus the inspected final interface is closed, despite the deliberately
conditional lower adapters. This conclusion is about source composition at
this boundary, not an independent re-audit of every imported leaf theorem.

## Findings and qualifications

1. **Documentation error corrected.** The old
   `UniformFinalOuterProgram.stagesFor` comment said that the fixed kernel
   spectrum was saved before input data were loaded. Startup already reads
   the padded input through `UniformAllAxisConjugatePreparation.fullProgram`
   → `UniformAllAxisSeedPreparation.fullProgram` → `UniformInitialPreparation`
   → normalization/kernel preparation → padded-input preparation.
   `UniformInitialPreparation.Operands.input` records those loaded cells.
   The corrected comment says “before input data enter the active role bank”.
   The first clock's active kernel roles are still prepared; no logical
   change was required.
2. **Paper/implementation variations documented.** The Chebyshev-based
   quadratic prime bound and the all-axis synchronized binary transform are
   described above. Neither introduces an external hypothesis or a theorem
   mismatch at the inspected boundary.
3. **Decimal corollary has an additional analytic step.**
   `UniformAsymptotics.paperCost_isLittleO_decimal`,
   `.paperCost_isBigO_decimal` and `.cost_bound_transfer` formalize the
   logarithmic absorption in §5.4, p.23. Composing `cost_bound_transfer` with
   `finalBudget_isBigO_paper` gives an eventual numerical decimal majorant
   for the proved budget. The inspected public `uniformDFT` declaration
   itself has type `UniformDFTStatement theta`; it is not a separately
   exported pure-decimal machine theorem. Do not omit the analytic
   composition when describing Corollary 1.2.
4. **Legacy module distinction.** `UniformCRTTransferMachine.lean` is
   annotated as supporting CRT bookkeeping but is outside the final
   1,271-module theorem closure, according to the parent source inventory.
   It is not evidence for the final actual fast-table execution path.
5. **No logical defect established in the inspected interface.** This does
   not certify the unaudited supporting bodies listed below. In particular,
   module-level paper references were also added to bookkeeping leaves;
   these references are correspondence annotations, not claims that every
   leaf's semantics was manually audited.

## Edit and verification boundary

This audit changed comments in 113 Lean modules and inserted 81 substantive
stage comments in selected proof bodies. The comment correction above is
included. A nested-comment-aware comparison against the baseline removed
comments and whitespace and found **113/113 unchanged noncomment token
streams**. Receipts and exact annotated paths are in
`logs/paper-audit/all-lengths-comment-only.json` and
`logs/paper-audit/all-lengths-annotated.txt`. No Lean logic, options or limits
were changed by this subtask. Lean comments were frozen before the parent's
fresh build. Build, axiom and canonical registry verification are parent
audit responsibilities; this report does not substitute a static comparison
for those checks.

## Manual source coverage

The following is exhaustive for this subtask's annotated file set. Names
stand for `lean/<name>.lean`. “Full-file read” means the complete source text
was inspected, including executable construction and theorem bodies, subject
to the imported-result limitation stated at the start. Remaining supporting
files had their module purpose/declaration inventory inspected for the
annotation, but no complete independent body review is claimed.

### Full-file reads in the annotated set

- `UniformCRT` (baseline 1–250).
- `UniformChirp` (baseline 1–63).
- `UniformChirpKernelPreparation` (baseline 1–296).
- `UniformChirpOutputMachine` (baseline 1–290).
- `UniformChirpPreparation` (baseline 1–364).
- `UniformChirpTableMachine` (baseline 1–255).
- `UniformCyclic` (baseline 1–223).
- `UniformFastPhysicalCRTArithmetic` (baseline 1–124).
- `UniformFastPhysicalCRTCycle` (baseline 1–135).
- `UniformFastPhysicalCRTMachine` (baseline 1–94).
- `UniformFastPhysicalCRTVisits` (baseline 1–38).
- `UniformFinalActualClockCost` (baseline 1–47).
- `UniformFinalClockCost` (baseline 1–129).
- `UniformFinalClockHeapTransform` (baseline 1–86).
- `UniformFinalDataClockProductExecution` (baseline 1–86).
- `UniformFinalDataClockProductResult` (baseline 1–55).
- `UniformFinalKernelAndDataEntry` (baseline 1–78).
- `UniformFinalKernelClockSave` (baseline 1–110).
- `UniformFinalLinearTableCost` (baseline 1–59).
- `UniformFinalMovementCaller` (baseline 1–107).
- `UniformFinalNumericJoin` (baseline 1–333).
- `UniformFinalOuterCost` (baseline 1–67).
- `UniformFinalOuterCostJoin` (baseline 1–36).
- `UniformFinalOuterProgram` (baseline 1–92).
- `UniformFinalOuterStartup` (baseline 1–66).
- `UniformFinalOuterSuffix` (baseline 1–65).
- `UniformFinalOutputTail` (baseline 1–59).
- `UniformFinalPhysicalTableExecution` (baseline 1–99).
- `UniformFinalPhysicalTablePrefix` (baseline 1–142).
- `UniformFinalPointwiseExecution` (baseline 1–34).
- `UniformFinalRoleExecution` (baseline 1–122).
- `UniformFinalRoleModel` (baseline 1–39).
- `UniformFinalStatementBridge` (baseline 1–62).
- `UniformFinalThirdClockOutput` (baseline 1–82).
- `UniformMasterRootMachine` (baseline 1–457).
- `UniformRoots` (baseline 1–36).
- `UniformSelectedCRT` (baseline 1–78).
- `UniformSelectedPhysicalCRT` (baseline 1–63).
- `UniformWorkingCompletion` (baseline 1–288).
- `UniformWorkingLength` (baseline 1–252).
- `UniformWorkingPreparation` (baseline 1–380).

### Partial-file reads and explicit remaining ranges

All line numbers here refer to baseline
`29fad6d4d3a68fbd806525034e8d07cd373f3d4c`.

| Module | Reviewed baseline ranges | Remaining unaudited baseline ranges |
|---|---|---|
| `UniformWorkingMachine` | 1–150 | 151–509: remaining primality/selection execution, retention and cost proofs. |
| `UniformCRTMachine` | 1–160 | 161–321: remaining machine-loop/aggregate operational proof bodies. |
| `UniformCRTTraversalCycle` | 1–120, 698–938 | 121–697, 939–987: most digit-carry execution/amortization and final presence/transfer support. |
| `UniformChirpKernelMachine` | 1–145, 358–457 | 146–357: result/row/frame/loop and aggregate execution proof bodies. Its semantic kernel identification and interface were inspected; the whole operational loop was not. |

### Annotated supporting modules without a complete manual body audit

These whole baseline ranges remain unaudited here. They include the address,
cache, frame and caller-fact leaves supporting the actual composition. No
negative or completeness claim about their correctness follows from this
list.

- `UniformCRTHeaderMachine`: 1–921.
- `UniformCRTTransferMachine`: 1–227. Legacy supporting module outside the final theorem closure.
- `UniformCRTTraversalMachine`: 1–785.
- `UniformChirpPointwiseMachine`: 1–182.
- `UniformFastPhysicalCRTCarry`: 1–155.
- `UniformFastPhysicalCRTCarryLoop`: 1–107.
- `UniformFastPhysicalCRTEmission`: 1–82.
- `UniformFastPhysicalCRTInitialization`: 1–187.
- `UniformFastPhysicalCRTProgress`: 1–105.
- `UniformFinalAllocationStride`: 1–23.
- `UniformFinalAxisCacheBundle`: 1–128.
- `UniformFinalAxisCacheIntervalRetention`: 1–138.
- `UniformFinalAxisCacheRectangle`: 1–100.
- `UniformFinalAxisCacheRetention`: 1–152.
- `UniformFinalAxisCacheSource`: 1–69.
- `UniformFinalAxisCacheTransfer`: 1–89.
- `UniformFinalAxisDispatchOutside`: 1–101.
- `UniformFinalAxisIterationOutside`: 1–75.
- `UniformFinalAxisPrinted`: 1–58.
- `UniformFinalAxisReadyTransport`: 1–55.
- `UniformFinalAxisRetention`: 1–90.
- `UniformFinalAxisStartupFrame`: 1–43.
- `UniformFinalAxisSuffix`: 1–161.
- `UniformFinalCRTMovement`: 1–44.
- `UniformFinalCRTRoleSource`: 1–51.
- `UniformFinalCacheAsymptotics`: 1–97.
- `UniformFinalCacheRegisters`: 1–54.
- `UniformFinalCacheRuntime`: 1–237.
- `UniformFinalCacheSource`: 1–31.
- `UniformFinalCacheSourceLoop`: 1–56.
- `UniformFinalCallerFacts`: 1–33.
- `UniformFinalClockCache`: 1–51.
- `UniformFinalClockCaller`: 1–90.
- `UniformFinalClockEntries`: 1–64.
- `UniformFinalClockLength`: 1–22.
- `UniformFinalClockOuterCore`: 1–72.
- `UniformFinalClockOuterDerivations`: 1–42.
- `UniformFinalClockOuterFrame`: 1–72.
- `UniformFinalClockOuterRuntime`: 1–41.
- `UniformFinalClockOuterTable`: 1–74.
- `UniformFinalClockOverhead`: 1–135.
- `UniformFinalClockRuntime`: 1–72.
- `UniformFinalDataClockProductLocal`: 1–41.
- `UniformFinalFiniteAxes`: 1–91.
- `UniformFinalFiniteAxisAdvance`: 1–119.
- `UniformFinalFiniteAxisState`: 1–85.
- `UniformFinalMovementFrame`: 1–103.
- `UniformFinalMovementGeometry`: 1–54.
- `UniformFinalOuterHeaders`: 1–151.
- `UniformFinalPhysicalTableGeometry`: 1–75.
- `UniformFinalPhysicalTableInputs`: 1–60.
- `UniformFinalPointwiseCRTCaller`: 1–66.
- `UniformFinalPreparedCellValue`: 1–28.
- `UniformFinalPreparedSpectrumSave`: 1–27.
- `UniformFinalRoleAlpha`: 1–84.
- `UniformFinalRoleCaller`: 1–85.
- `UniformFinalRoleClockValues`: 1–43.
- `UniformFinalRoleGeometry`: 1–53.
- `UniformFinalRoleRetention`: 1–56.
- `UniformFinalRoleStorageAlpha`: 1–34.
- `UniformFinalRoleStorageCaller`: 1–58.
- `UniformFinalRoleStorageEntries`: 1–61.
- `UniformFinalRoleTableEntries`: 1–56.
- `UniformFinalStartupCode`: 1–36.
- `UniformFinalStartupData`: 1–24.
- `UniformFinalStartupFrames`: 1–25.
- `UniformFinalStartupPrefix`: 1–73.
- `UniformFinalStartupSource`: 1–59.

### Additional read-only source evidence

`UniformFinalDFTExecution`, `UniformFinalOuterEnvelope` and
`UniformPhysicalSynchronizedSchedule` were read in full but belong to other
annotation scopes. `UniformAsymptotics` was read through its original first
160 lines, including all three decimal-transfer helpers; the rest was not
independently audited here. `UniformAllAxisSeedPreparation` was read in
targeted sections for axis count/radix definitions, literal startup program
and retained operands; the complete large module was not audited.
`UniformAllAxisConjugatePreparation` was inspected at its full-program
composition, and `UniformInitialPreparation` at the input-operand and
startup composition interfaces. Their other body ranges remain unaudited
here. The selected-radix-at-least-two interface from
`UniformMultiAxisSectorMetadataPreparation.selected_radix_two` was used;
its proof body was not independently audited in this subtask. Recursive,
axis, calendar, OAI and generated-checker bodies outside the stated file
list remain outside this review; see the other scope reports.
