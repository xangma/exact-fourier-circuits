# Pinned-paper proof map and independent review

Review baseline: `29fad6d4d3a68fbd806525034e8d07cd373f3d4c`, branch
`codex/paper-proof-audit`, isolated worktree `paper-audit`. This report separates
statement adequacy, substantive proof correspondence, and kernel verification.
A clean kernel check cannot establish that a definition matches a paper.

## Sources and identity

**E:** [An explicit power saving for the exact discrete Fourier transform](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf).
**F:** [Finite tensor savings and exact Fourier circuits](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf).
Both are pinned to OpenAI math revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All 24 local paper/source files
were checked against the Git tree and blob identities before use; SHA256s
are preserved in [paper-source-identity.json](../verification/paper-source-identity.json).
Printed page numbers equal PDF page numbers (E: 31 pages; F: 49 pages).
Numbered statements/equations were checked in the PDFs, including a rendered
inspection of E p. 2. TeX labels below identify source arguments; they were
not used to guess numbering. The math checkout remained read only.

The quantitative all-length theorem is E Theorem 1.1, **not** F's nonuniform
subsequence theorem. F supplies background and shared exact-width mechanisms;
E Appendix A is an alternative synthesis route, not a substitute for charged
execution of E's quantitative network construction.

## Literal public statement

The exact closed target is
`ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT :
UniformMachine.UniformDFTStatement UniformExponent.theta`.
Its actual-execution declaration is `.execution` in the same namespace.

- The finite program, positive runtime constant, eventual threshold and
  positive word degree are fixed before the length and input are quantified.
- Every positive length and every complex input have a successful terminating
  execution from zero registers and empty heaps. Correctness is all-length;
  the time inequality alone is eventual.
- Outputs are the positive-exponent **unnormalized** DFT in the original
  index order, using the canonical `zeta n = exp(2*pi*i/n)` definition.
- Exactly one specified root is requested; its order depends on n before x,
  is computed by charged instructions, and satisfies `0<D<1024*n^3`.
- Every instruction, including preparation, heap access, movement, branches,
  indexing and halt, contributes to the tick count. Every intermediate
  integer/address value fits one fixed polynomial envelope.
- The exponent is exactly (1.1): `m=10^6`, `W_*=2^71`,
  `Delta=6871402692000000`, `theta=log_m(m-Delta/W_*)`.

These obligations agree with E §1.1, Theorem 1.1 and (1.1)–(1.2), p. 2
(`sec:model`, `thm:main`, `eq:main-constants`, `eq:main-bound`), within the
source-review limits below. See the [literal semantics audit](audit-semantics.md)
for the quantifier comparison, exact source lines, failure guards and same-state
joins. No vacuity or hidden algorithm/output oracle was identified there.

The finite instruction syntax carries only fixed natural/rational literals,
not arbitrary complex constants or functions. Complex division's nonzero test
is a validity/failure guard, not a program-visible complex branch. Taint is
introduced only by input reads and preserved conservatively; natural control
cannot depend on complex data. These features justify the relation between
noncomputable complex denotations and a deterministic exact-arithmetic RAM
algorithm. This is not a claim of native code extraction, unit bit complexity,
floating-point stability, or practical speedup.

## Substantive paper-to-Lean map

All names in this table have prefix `ExactFourierCircuits.`. Each scope report
below gives additional qualified declarations, source lines and review ranges.
The annotated Lean modules carry the pinned title/revision and precise paper
anchors. Explicit offsets, headers, heap regions, tag invariants, continuations
and envelope enlargement are identified as implementation bookkeeping rather
than invented one-to-one paper lemmas.

| Lean declaration or module | Exact paper argument | Obligation / boundary |
|---|---|---|
| `UniformMachine.{Instruction,step,BoundedExecution,ComputesDFT,UniformDFTStatement}` | E §1.1, Theorem 1.1, p. 2; DFT convention p. 1 | Defines the charged finite machine and literal target; does not itself prove an algorithm. |
| `ExplicitSeedBudget`; `UniformExponent.{lambda_eq_sub,theta_explicit_gap,critical_depth_bound}` | E (1.1), p. 2; §2.6, (2.10), Theorem 2.6, pp. 11–12; §5.4 p. 23 | Exact saving, recurrence multiplier and exponent, without floating-point approximations. |
| `UniformRecursiveRootExecution.execution`; prepared child induction and runtime bridge modules | E Proposition 2.4 p. 10; Lemma 2.5 pp. 10–11; Theorem 2.6 pp. 11–12 | Role-preserving finite network, genuine smaller executions and charged quotient recurrence. Internal child premises are discharged by induction. |
| Local Fourier/Newton/Toeplitz and actual zero-free pair preparation modules | E Proposition 3.1 p. 12; §3.1–§3.5 pp. 13–18, especially (3.12)–(3.14) pp. 17–18; shared mechanism F §3 | Deterministic exact-width layers, restored borrowed data and charged scalar/DAG preparation; see finite-chain report for actual versus legacy routes. |
| `UniformSynchronizedLayers.tensorSchedule_product`; `UniformPhysicalSynchronizedSchedule.product` | E §4.3, (4.5), p. 20 (`eq:tensor-multiply`) | Chronological tensor of padded local slots, in the actual fixed physical order. Matrix identity is not yet a machine run. |
| `UniformSectorPacking.sectorStart_paper_sum`; `UniformSectorPackingMachine.execution`; `UniformSectorMetadataMachine.execution_cost` | E §4.1 (4.1) p. 18; Lemma 4.1, (4.2)–(4.3), p. 19 | Explicit sector addresses and literal linear traversal/packing; no full-axis scan per entry. |
| `UniformProducedClockTick.execution`; `UniformActualCompleteClockTick.execution`; `UniformActualCompleteClockExecution.execution` | E Proposition 4.2, (4.4)–(4.5), pp. 19–20 | Produced bank actions, same-state child execution and complete synchronized clock, including retained caches and charged printing. |
| `UniformWorkingLength`; `UniformWorkingMachine`; `UniformAsymptotics.axisCount_isTheta` | E §5.1, Lemma 5.1, (5.1)–(5.4), p. 21 (`lem:prime-lengths`, `eq:working-length`, `eq:working-bounds`) | Actual selected odd primes and binary fill, `2n<=L<4n`, and the critical axis-count shape. |
| `UniformSelectedPhysicalCRT`; actual fast CRT traversal/emission/cost modules | E §5.2, (5.5), p. 22 (`eq:crt-fourier`); §4.1 (4.1), p. 18 | Separate input alpha/output beta permutations and amortized linear physical table production. |
| `UniformMasterRootMachine.order_paper_formula`, `.master_execution`; chirp/cyclic modules | E §5.3, (5.7)–(5.9), pp. 22–23 (`eq:chirp`, `eq:master-root`, `eq:root-size`) | Canonical root powers, nonzero prepared normalization, no circular wraparound and three-transform identity. |
| `UniformFinalKernelAndDataEntry.execution`; `UniformFinalDataClockProduct.execution`; `UniformFinalThirdClockOutput.execution` | E §5.2–§5.3 pp. 22–23 | Actual prepared-kernel clock and spectrum, variable clock, prepared pointwise multiplication, third forward clock, reversal/scaling/chirp/output. |
| `UniformFinalDFTExecution.execution`; `UniformFinalOuterCostJoin.bound` | E §5.3–§5.4 pp. 23–24 | Joins the actual prefix and all three actual transform endpoints through the same physical states and sums their actual costs. |
| `UniformJointAllocation.{actualConstants,polynomial,recursion_word_bound}`; `UniformGlobalEnvelope.execution_mono` | E §5.4 p. 24 | Conservative fixed slabs/stack bounds and polynomial word envelope. Layout formulas alone do not assert execution. |
| `UniformFinalLinearTableCost.finalBudget_isBigO_paper`; `UniformFinalOuterEnvelope.of_execution`; `UniformFinalDFTExecution.uniformDFT` | E Theorem 1.1, (1.2), p. 2; proof §5.4 pp. 23–24 | Supplies absolute constants and word degree from the closed actual run and proved numerical budget. |
| `UniformAsymptotics.{paperCost_isLittleO_decimal,cost_bound_transfer}` | E Corollary 1.2, p. 2; proof §5.4 p. 23 (`cor:decimal`) | **Formalized** log-log absorption. Composes with the final budget; the public machine target itself still states the sharper theta/log-log bound. |

The decimal consequence is therefore supported by proved numerical helpers,
not an unproved asymptotic assumption. The inspected public target does not
literally have a pure-decimal machine statement as its type. Likewise,
`UniformMasterSynchronizedLayers` is an auxiliary algebraic master-root bridge,
not the literal clock's dependency supplying its physical schedule. Annotated
`UniformDiagonal` and `UniformCRTTransferMachine` are legacy supporting modules
outside the final 1,271-module import closure; neither is used as evidence for
an actual final-stage execution.

## Comparison with the October 8 upstream formalization

The later [actual upstream solution](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Computability/FourierTransform/Main.lean)
is pinned separately to `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
It was introduced in `301488868beec11bfd897168433b0a64f5258559`, timestamp
`2026-10-07T22:03:50-07:00` (October 8 in London). It predates this review's
October 9 downstream proof baseline. No priority claim is made.

**The same mathematical all-length DFT result is addressed; these are different
formalizations and algorithms. No formal equivalence or machine translation
has been proved by this comparison.** Both reuse byte-identical upstream Core
root/Fourier definitions. The two paper subtrees are also byte-identical between
the original pinned paper revision and the new release; the smaller seed is
a Lean implementation variation, not a changed paper constant.

| Aspect | Reviewed branch | New actual upstream release |
|---|---|---|
| Closed result | `UniformFinalDFTExecution.uniformDFT` with actual `.execution` | `OAI.PowerSaving.transform_main`, `.transform_main_order`; also `.convolution_main` and `._order` |
| Mathematical output | Positive canonical, unnormalized DFT in original order | Same Core definition; `matrix_definition` is `rfl` |
| Concrete seed | Literal paper-scale `m=10^6`, `W_*=2^71` saving route | 32-coordinate factors, 4060 triples, `2^50` role envelope, stronger intermediate `alpha=1-2/10^11` |
| Final exponent | Exact paper theta/log-log majorant | Same paper theta bound, implied by its stronger intermediate bound |
| Decimal/little-o | Formal numerical absorption helpers; not separate fields of the literal closed target | Explicitly bundled with the paper bound in `TimeBounds` |
| Local depth | Selected schedule bound retains fourth logarithmic power | Quadratic logarithmic layer score; see structural comparison |
| Root formula | Paper master-root formula `(2n)*L*2^ceil(log2(16L))`, cap `<1024n^3` | Conditional smaller receipt formula with small-range direct fallback; `_order` proves `<8n^3` |
| Three-transform identity | Three forward transforms followed by reversal/scaling | Two forward transforms and one inverse-root transform/scaling |
| Order/root charging | Integer computation and exactly one recorded root instruction inside the actual run | Separate fixed order/solve programs; goal charges `order.work+1+solve.work` |
| Execution/storage | Explicit partial heap/register transitions and intermediate physical address bound | Finite typed compositional programs with validity/work/peak bounds, charged fresh arrays and a polynomial work-based arena interpretation |
| Arithmetic restrictions | Bool-taint input linearity; invalid reads/divisors fail | Static input paints, no cross product in DFT mode; convolution mode permits left-right products; some invalid Nat/Tape operations use total defaults |

See [upstream theorem/machine comparison](audit-upstream-semantics.md) and
[upstream seed/architecture comparison](audit-upstream-structure.md) for exact
qualified declarations, source lines, formulas and limits. The public challenge's
intentional `sorry` statements are not the solution: its JSON points to the
actual Main module. Static policy scanning found no admissions/custom axioms/
raised-limit tokens in the 88 new solution sources. That scan is not a kernel
or axiom-closure receipt for upstream.

[Snapshot identity](../verification/upstream-comparison-source-identity.json)
records 92 checked files, both unchanged paper-tree identities, and the explicit
fact that no upstream kernel build was performed here. This comparison did not
alter the frozen Lean tree or interrupt the downstream rebuild.

Follow-up: the [separate unchanged upstream reproduction](upstream-dft-reproduction.md)
now freshly builds the solution's 89-module import cone and checks all 4,247
declaration closures. The snapshot identity above remains the historical
source-comparison receipt.

## Findings, variations and coverage

No confirmed blocking theorem/model mismatch was found at the inspected
substantive boundaries. This is a bounded independent source audit, not a
claim that every proof body in all 1,271 modules was manually rederived.

- **Informational implementation differences:** enlarged finite base range;
  Chebyshev library prime estimate in place of E's binomial proof;
  synchronized local treatment of the binary factor; conservative RAM bank
  geometry and word degree. Scope reports explain why these preserve the
  relevant obligations and where the proofs establish their cost.
- **Documentation correction:** the kernel spectrum is prepared before input
  is loaded into the active role bank, not before any input read anywhere.
  Startup already constructs padded input in a separate bank. Prepared tags
  and retained-state proofs, rather than that misleading temporal wording,
  justify input independence. The contract also now identifies the actual zero-free pair-preparation route and labels the earlier `UniformDiagonal` route as legacy.
- **Literal-statement boundary:** the decimal asymptotic helper exists, but
  should not be described as the literal type of `uniformDFT`.
- **Review limits:** low-level generated/calendar/cache/stack and register
  helper bodies not explicitly inspected remain outside the human audit;
  kernel/census coverage does not erase this limitation. Vendored OAI bodies
  and generated checkers were left unchanged. Optional E Appendix A synthesis,
  unrelated F pricing/pivot/reflection results and two-input convolution are
  not claimed newly formalized or exhaustively audited here.

Detailed coverage and exact remaining scopes:
[semantics](audit-semantics.md), [finite network/local compiler](audit-finite-chain.md),
[synchronization/packing/clock](audit-synchronization.md),
[all lengths/CRT/chirps/cost](audit-all-lengths.md),
[verification trust model](audit-verification.md).
The [complete module inventory](../verification/paper-review-coverage.json) distinguishes annotations from human proof inspection;
an annotation alone is not evidence of exhaustive review.

The graph's Verify-tier generation `2026-10-07T17:50:28Z` points at the primary
checkout and predates these strong-result files. Final symbols returned no
matches; cited new files had freshness `not_tracked`, with additional Lean
parse gaps and scripts/docs excluded. No negative or exhaustive claim rests
on this graph. Exact-source fallback and the canonical source import inventory
supply the evidence. Review reports disclose their own read ranges.

## Changes and verification

175 Lean modules received comments; 173 are in the final import closure.
[Edit integrity](../verification/paper-audit-edit-integrity.json) records baseline
and annotated hashes and equality of normalized non-comment source. No proof
term, definition, import, theorem statement or option changed. All 51 vendored
sources, generated checkers and seven historical source-limit files remain
byte-identical. Only the registered source hashes were refreshed; historical
certification receipts were not relabeled as evidence for the new tree.

The old algorithm receipt is preserved byte-for-byte at
[historical receipt](../verification/history/uniform-final-algorithm-pre-paper-audit.json).
Focused baseline exact-target/axiom checking passed. A negative stale-registry
control rejected the annotated `UniformMachine` before compilation.

**Annotated-tree verification passed.** The canonical `--rebuild-all --jobs 4`
run freshly compiled all 1,271 project modules with **zero project-artifact
reuse**, then passed a fresh normal Main compile, the exact closed-target guard
and all 82,513 defining-module axiom closures (79,030 public/generated; 3,483
private). Only `propext`, `Classical.choice`, `Quot.sound` occur. The driver uses
default limits with the seven unchanged historical source exceptions.

The [new canonical receipt](../verification/uniform-final-algorithm.json) binds
the annotated source/configuration and fresh artifacts. Independent rehashing
checked 1,271 sources, 13 configuration entries, 1,271 normal project artifacts,
11,265 external artifacts and eight check artifacts, and revalidated the held
source inventory; see the [cross-check receipt](../verification/paper-audit-crosscheck.json).
The two outside-closure legacy modules also compiled freshly and passed all
146 defining-module closures, with standard axioms only and no private
declarations; see the [legacy receipt](../verification/paper-legacy-check.json)
and its [preserved harness](../scripts/paper-audit/check-legacy.py).

These are kernel/receipt checks of the stated semantics, not materialized
execution of the enormous algorithm or exhaustive human proof review.
Nothing was deployed, merged or published.
