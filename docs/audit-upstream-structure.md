# Comparison with OpenAI's October uniform formalization

Audit date: 2026-10-09. Local proof baseline:
`29fad6d4d3a68fbd806525034e8d07cd373f3d4c`, with the review branch's
comment-only annotations. Upstream comparison revision:
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**The constructions match the same mathematical DFT and broad paper route,
but are different formalizations and different concrete implementations.**
Upstream uses a smaller finite network, a different local depth bound and
root-order formula, and bundles decimal, little-o and convolution conclusions.
This review establishes neither an equivalence theorem between the machine
models nor equality of their programs. It does not establish priority or a
fresh upstream kernel check. The separate semantics comparison and local
verification report remain necessary.

Follow-up: the [separate unchanged upstream reproduction](upstream-dft-reproduction.md)
now supplies the fresh 89-module kernel check and complete declaration audit.
The historical comparison below retains its original source-review scope.

## Source identity and chronology

The solution is
[`OAI.Computability.FourierTransform.Main`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Computability/FourierTransform/Main.lean),
specifically `OAI.PowerSaving.transform_main[_order]` and
`convolution_main[_order]`. `lean/ComparatorChallenges/UniformFourier.json`
names this solution and its two main theorems. The challenge's intentional
placeholders are not the solution proof.

The introducing commit is
`301488868beec11bfd897168433b0a64f5258559`. Its Git timestamp is
2026-10-07 22:03:50 -07:00, or **2026-10-08 06:03:50 Europe/London**.
This is a commit timestamp, not independent evidence of the exact publication
time. All 37 upstream evidence files listed below have identical Git blobs at
that commit and the comparison revision. For each, `git show` bytes were
hashed with `git hash-object --stdin` and compared with `git rev-parse
<revision>:<path>`; every available sparse-checkout file was also compared
byte-for-byte and hashed directly. Key identities:

| Path | Git blob |
|---|---|
| `lean/OAI/Computability/FourierTransform/Main.lean` | `86ef40a7050feddb8de005b7a2f96fd9fcc2f24c` |
| `lean/OAI/Computability/FourierTransform/Goal.lean` | `888326d1feb3380476f893314324019a474a681e` |
| `lean/docs/130.md` | `c4419a9add293ab5f0fd51c72a193238875affb3` |
| `lean/ComparatorChallenges/UniformFourier.json` | `1979fcdcaa71194fc71859229091d9fd96deee51` |

Additionally, the entire shared `lean/OAI/Computability/FourierCircuit/Core.lean`
was read and verified byte-identical between local vendored source and both
upstream commits, blob `60a4af2dae8058e57961ec9b7978b8535e5b5c9b`.

The SHA-256 of the 37-entry manifest, encoded as `path + " " + blob + "\n"`
in the evidence-list order below, is
`88e6f5475c365c596df32e58ebe78e99f0a724d72a586ee5876b3585ba18b43f`.

The original paper pin remains
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. **Both relevant paper subtrees
are unchanged between that pin and the new release**, verified by Git tree
identity, not merely their titles:

| Paper | Tree at both revisions |
|---|---|
| E: *An explicit power saving for the exact discrete Fourier transform* | `69f756a26a852adb062cd57b2faa4050c289cb14` |
| F: *Finite tensor savings and exact Fourier circuits* | `b82e5bb07e8dbb1815d4f812533b84caadada905` |

Consequently the smaller network is an implementation variant in the new Lean
release; it is not a replacement of E's printed constants. Paper locations
below use the original pin. E PDF p.2 was directly checked in the
page-separated extraction; the detailed paper/source maps and other verified
PDF locations are in [audit-finite-chain.md](audit-finite-chain.md),
[audit-synchronization.md](audit-synchronization.md), and
[audit-all-lengths.md](audit-all-lengths.md).

## Certificate and exponent differences

Upstream names below are relative to `OAI.PowerSaving`; local names are relative
to `ExactFourierCircuits`. Upstream file names are relative to
`lean/OAI/Computability/FourierTransform/`; local files are in `lean/`.
Line numbers refer to the inspected source, including review annotations in
local files.

| Quantity | Local paper-scale construction | Upstream October construction |
|---|---|---|
| Binary coordinate set per factor | `h = 100` | `H = Fin 32` |
| Triple family | `v = choose 100 3 = 161700` | Three-subsets avoiding pivots 0 and 1: `choose 30 3 = 4060` |
| Block coordinate count | `m = 1000000` | `mcol = 32^3 = 32768` |
| Physical role count before padding | `1873807244643542670000` | `2*4060^3 + 3*4060^2*(4060^2+33) = 815262685588400` |
| Padded roles | `2^71` | `2^50` |
| Saving | `6871402692000000` | `bankSave = 2*4060^2*(4060-3*32*33) = 29406742400` |
| Recursive residual coefficient | `S = 2^71*1000000 - 6871402692000000` | `nMoves = 2^50*32768 - 29406742400` |
| Exponent used for implementation bounds | Exact paper `theta = log_m(S/2^71)` | `alpha = 1-2/10^11`, with `nMoves/2^50 < mcol^alpha` |

Sources: local `ExplicitSeedBudget.lean:15–38`,
`UniformFixedNetwork.lean:12–23,74–86,121–138`,
`UniformExponent.lean:25–29,35–45,109–119`; upstream
`NetworkRoles.lean:7–35`, `NetworkStages.lean:9–20,34–56`,
`TensorCertificate.lean:180–204`, `TensorSaving.lean:81–111`.
The small integer calculations above use ordinary exact arithmetic; no
network arrays or astronomical powers were expanded.

This is not simply substituting 32 for the paper's 100: upstream's triples
omit two pivots and its auxiliary `Side = Trip × Trip` assigns storage to
inactive ordered pairs too (`ScalarNetwork.lean:10–13`). Local
`ExplicitSeedBudget.parameter_formulas` instead uses the paper's active
degree in its role formula. Both use three chronological shear stages with
the middle stage reversed and then terminal correction; upstream
`TensorCertificate.all_stages` and `.certificate` are at lines 87–95 and
189–204. Local `UniformFixedNetwork.correctedWord_chronology` and
`.correctedWord_matrix` are at lines 34–54. The paper argument is E §2.1–2.6,
PDF pp.5–12, especially Lemmas 2.1–2.3, Proposition 2.4 and Theorem 2.6.
This comparison checked these composition boundaries, not every internal
network identity.

The two finite counts are not complete running times. Upstream's
`certificate` explicitly counts only kernel calls and leaves fixed-size
point moves to the operational compiler (`TensorCertificate.lean:186–192`);
`rec_body` / `recurse_run` then charge a constant overhead and actual child
work. Local `simultaneousWord_calls` separately displays its pointwise term
`2*pointwiseCalls`, and its recursive execution has additional printing,
stack and instruction costs. Comparing only `S` with `nMoves` would omit
these obligations.

The **reported paper theta is mathematically the same**: upstream
`Goal.lean:25–29` defines `log(m-Delta/W)/log(m)` using the exact printed
`m`, `W`, `Delta`; local defines `logb m (S/W)`, and
`UniformExponent.lambda_eq_sub` proves `S/W = m-Delta/W`.
Upstream separately proves `alpha < theta` (`Main.lean:39–57`). Thus it
derives the paper exponent from a stronger seed bound; it does not implement
the literal paper-scale recurrence multiplier.

## Substantive construction map

| Stage and paper location | Local checked boundary | Upstream checked boundary | Correspondence and limit |
|---|---|---|---|
| Finite saving and quotient recursion: E Theorem 2.6, pp.11–12 | `UniformFixedNetwork.simultaneousWord_matrix/calls`; `UniformRecursiveChildInduction.execution` (lines 33–62); `UniformRecursiveRootExecution.execution` (113–130) | `Cluster.certificate`; `RAM.recurse_run` (`RecursionBounds.lean:112–193`); `RAM.hills_all/hills_program` (`TensorProgram.lean:11–25,95–104`) | Same `k = m*q + r` batching idea. Upstream closes a typed recursive handler by a finite `descend` program with depth `k+1`; local closes executions of a literal jump/register program by strong induction and physical stack/heap contracts. Certificate sizes and residuals differ. |
| Exact-width local Fourier layers: E Proposition 3.1, pp.12,17–18; (3.1)–(3.2), p.13 | `UniformLocalFourierLayers.Nschedule/schedule` (560–593), `specifiedSchedule_matrix/length_bound` (801–834) | `Spectral.winds_reduction` (`NewtonFactorization.lean:185`); `Slant.ballad/creates_ballad` (`FourierWords.lean:60–62,105–108`) | Both factor Fourier through Newton diagonals and a Toeplitz operation, with a transpose/reversal construction, on the exact axis width. The inspected bounds are different: local depth is at most a constant times `(clog2 n+1)^4`; upstream `score e ≤ 20000000*(e+1)^2+7` (`FourierWords.lean:117–119`, `ToeplitzLayers.lean:54–88`). |
| Charged scalar and schedule preparation: E Lemma 3.4, p.17; §3.4, p.18 | `UniformLocalPreparationDAG.compileRequests_*` (213–258), plus the final initialized execution prefix | `RAM.Bench.publish` (`LocalCompiler.lean:113–138`); `Neaps.kilnP` (`WorkingPreparation.lean:139–175`); `Bench.effuse` (`WorkingCompiler.lean:113–147`) | Both build Newton/reciprocal/root data and local layer information, then charge preparation. A mathematical cache/DAG or `Foundry.prepared` interface alone is not a complete initial-state algorithm; the checked outer compositions supply it. Full producer implementations were not reaudited here. |
| Synchronized axes and contiguous sectors: E Lemma 4.1 and Proposition 4.2, pp.19–20, (4.2)–(4.5) | `UniformSynchronizedLayers.tensorSchedule_product` (65–76); `UniformSectorPacking.packedEquiv_value/packingPermutation` (299–308); `UniformSectorPhysicalBinaryAction.sectorTensor_physical` (80–102); `UniformActualCompleteClockExecution.execution` (24–77) | `Bench.Matting.packT` (`SectorAlgorithm.lean:76–88`); `Bough.water/swell` and `Thicket.conduct/stream` (`SynchronizedAlgorithm.lean:23–58,90–119`) | Both pack tensor sectors, invoke the saved binary kernel on sector widths, and synchronize axis layers instead of charging a separate full-array pass for each axis. Local proves literal heap permutations and tick/state retention; upstream uses typed tapes, scatter/gather and composition judgments. No cross-model simulation was proved. |
| Working length and CRT: E §5.1–5.2, pp.21–22, (5.3)–(5.6) | `UniformWorkingLength.workingLength` and bounds (138–158); final physical CRT prefix | `Selection.barge_spec` (`LengthSelection.lean:202–254`); `Bench.Thicket.traverse` (`WorkingTransform.lean:96–111`) | Same odd-prime product plus power-of-two fill idea, and the same `2n ≤ L < 4n` volume guarantee. Upstream scans a bounded prime range and appends the binary factor. Equality of the two computed length functions was not proved. CRT gathering, synchronized transform and scattering are charged by upstream `traverse`; local uses actual table/traversal instructions. |
| Chirp reduction and three transforms: E §5.3, pp.22–23, (5.7) | `UniformFinalDFTExecution.execution` (32–87) | `Bench.Cruise.pyramid/singing` (`ArbitraryLength.lean:156–196`) | Both transform the fixed chirp kernel and the chirped input, multiply the prepared spectrum into the data, transform back, scale and apply the output chirp. Upstream calls two forward and one inverse-root working transforms; local uses three forward clocks plus actual reversal/scaling. This is the mathematical `F_L^{-1}=L^{-1}JF_L` alternative in E §5.2, p.22. |
| Small lengths and total program | The same final assembled program is used for every positive length; recursive binary base cases are explicit | `Bench.Neaps.course` (`TransformProgram.lean:97–120`) chooses the fast branch when `Ports n`, otherwise direct Fourier evaluation | Different program organization. Upstream proves the direct branch eventually disappears (`Asymptotics.docks_ev`, lines 128–137). |
| Final allowance and asymptotics: E §5.4, pp.23–24 | `UniformFinalLinearTableCost.finalBudget/finalBudget_isBigO_paper` (41–47), `UniformFinalOuterEnvelope.of_execution` (22–44) | `flagshipOne` (`UniformBounds.lean:142–158`), `Skies.lunch_big` (`Asymptotics.lean:169–181`), `Skies.time_bound` (`Main.lean:111–117`) | Both include preparation, transform work and index/movement work in an input-independent allowance. Local sums three complete clock envelopes. Upstream extracts fixed typed programs and their constants, with an allowance including the order program and one root. This table does not independently certify their complete semantics. |

The source-level staged route corresponds to E's network/local/synchronization
proof. Upstream expressly excludes the synthesis appendix's general
rational-algebra extraction, symbolic search and bounded-printer
uniformization (`Main.lean:19–23`); the compared local final theorem follows
the explicit network route too. Neither the common paper title nor an
existential fixed-program theorem proves that the entire synthesis appendix
was formalized.

## Actual root orders

Local `UniformMasterRootMachine.order` (line 312) is always

```
D_local(n) = (2*n) * L_local(n) * 2^clog2(16*L_local(n)).
```

`order_paper_formula` (318–321) identifies the lcm and exact ceiling-log
formula; `order_bounds` (314–316) proves `0 < D_local(n) < 1024*n^3`.
This follows E (5.8)–(5.9), PDF p.23. The literal root instruction and order
calculation are in `UniformMasterRootMachine.suffix` (53–58), with the
initial execution at `master_execution` (335–338).

Upstream `Selection.receipt` (`LengthSelection.lean:256–260`) is instead

```
K(n) = floor(log2(2*n)) + 1
H(n) = (16*(K(n)+4))^2
e(n) = floor(log2(2*H(n))) + 2
D_upstream(n) = if 2^e(n) <= n then (2*n)*L_upstream(n)*2^e(n) else n.
```

The root envelope depends on the bound for the individual radices, not
`16*L`. `receipt_bound` (262–282) proves `0 < D_upstream(n) < 8*n^3`.
`RootPreparation.receiptG/planOrder` (197–201,215–218) constructs the order
within the charged preparation judgment; `UniformBounds.orders1` (84–87)
extracts the fixed length-only program. `Main.transform_main_order`
(122–127) exposes this exact formula and stronger cubic bound.

As a small exact check of nonidentity, at `n=1` the upstream direct branch
selects 1 (`K=2`, `H=9216`, `e=16`), whereas local selection gives
`L=2` and order `2*2*32=128`. No huge expression was evaluated.
Different specified roots are compatible with the paper's one-root model;
this comparison alone is not a formal proof translating one model into the
other. The literal paper root formula belongs to the local implementation;
upstream proves another explicitly computed polynomial-order root suffices.

## Final mathematical conclusions and reporting findings

The positive-exponent, unnormalized DFT agrees at the mathematical boundary:
upstream `Goal.dft` (18–19) sums `zeta_n^(j*k)*x_k`, and
`Main.matrix_definition` (145–146) identifies it with `fourierMatrix.mulVec`;
local `UniformMachine.ComputesDFT` (248–249) uses the same matrix operation.
The shared, byte-identical `FourierCircuit/Core.lean:40–42` defines
`zeta n = exp(2*pi*i/n)` and the matrix entries `zeta n^(j*k)`.
This does not identify intermediate physical layouts or their machine
representations.

**[P2, reporting] Do not describe the compared closed theorem types as
identical or fully proved equivalent.** Local
`UniformMachine.UniformDFTStatement` (263–269), proved by
`UniformFinalDFTExecution.uniformDFT` (91–95), contains the all-positive-length
DFT, one root, polynomial word envelope and eventual
`O(n*(log n)^theta*(loglog n)^(4-theta))` time condition. Upstream
`Goal.DFTGoal/TimeBounds` (75–79), proved by `Main.transform_main` (137–139),
also includes `O(n*(log n)^(1-10^-13))` and `o(n*log n)` as explicit
conjuncts. `Main.convolution_main` (141–143) additionally proves a separate
two-input convolution goal. The local DFT endpoint being compared contains
no convolution conjunct. This is a scope/packaging difference, not a
counterexample to local DFT correctness. Paper counterparts: E Theorem 1.1
and Corollary 1.2, PDF p.2, and §5.4, pp.23–24.

**[P3, reporting] The local decimal implication already has a formal analytic
proof; it should not be described as an unproved analytic gap.**
`UniformAsymptotics.paperCost_isLittleO_decimal` (58–60) and
`.cost_bound_transfer` (68–70), together with
`UniformFinalLinearTableCost.finalBudget_isBigO_paper`, show that the
input-independent allowance bounding the actual execution is even little-o
of the decimal bound. The final `uniformDFT` type does not bundle that
corollary. This comparison did not add or kernel-check a new packaged machine
corollary. Paper counterpart: Corollary 1.2, p.2, proof §5.4, p.23.

Upstream proves the stronger intermediate bound
`lunch = O(n*(log n)^alpha*(loglog n)^2)`:
`Asymptotics.flight/lunch_big` (86,169–181). `Main.alpha_theta` (39–57),
`decimal_range` (59–60) and `flight_little` (64–77) absorb the remaining
log-log factors before building `TimeBounds`. Hence its proof also derives
little-o of `n*(log n)^theta` and of the decimal bound, even though only the
three stated `TimeBounds` conjuncts are exposed. The inspected local final
budget proves the printed paper-shaped estimate; this review establishes
no local bound at upstream's stronger `alpha`.

No confirmed contradiction was found in the construction boundaries checked
here. Counts of source modules, Main's 151-line length, or the local
dependency closure size are not measures of equivalence, correctness or
proof strength.

## Bounded coverage and checks

Graph evidence used Verify tier. The upstream graph project
`Users-xangma-repos-math` is dated `2026-10-07T11:10:24Z`; the relevant symbol
search was fully paginated and did not locate the new solution. Coverage
checks for all 37 evidence paths returned missing coverage for new Lean
sources/JSON and excluded coverage for `lean/docs/130.md`. Local project
`exact-fourier-circuits` is dated `2026-10-07T17:50:28Z` (4,174 nodes,
11,147 edges). Eighteen initial paths plus three added supporting paths were
checked: the strong files were not tracked, and `ExplicitSeed` /
`ExplicitSeedBudget` had partial recorded ranges. Those ranges were read
from baseline source as well as the relevant annotated source. Exact source
inspection, rather than graph absence, supports this report. No graph was
reindexed during the frozen build. The additional shared Core path had
whole-file unusable coverage (lines 1–55); the complete source was read.

Upstream identity manifest order (all 35 names below mean the `.lean` file
under `lean/OAI/Computability/FourierTransform/`, followed by the two complete
paths):

```
Main Goal NetworkRoles ScalarNetwork NetworkLabels NetworkInvocation NetworkStages
TensorCertificate TensorRecursion TensorAlgorithm RecursionBounds TensorSaving
TensorProgram LengthSelection PrimeSelection RootPreparation LocalCompiler
FourierWords NewtonFactorization ToeplitzLayers LayerCompilation WorkingCompiler
WorkingPreparation WorkingTransform SynchronizedAlgorithm SectorAlgorithm
ProgramConstruction RegisterBounds Asymptotics UniformBounds TransformProgram
FourierCompilation BinaryFrames BinaryBasis ArbitraryLength
lean/docs/130.md
lean/ComparatorChallenges/UniformFourier.json
```

Full-file reads were made for upstream Main, Goal and TensorSaving.
The additional shared Core file was also read throughout.
NetworkRoles was read through line 47; the other evidence files were read in
the targeted definitions/boundaries displayed in the table, not all
proof bodies: in particular the full local compiler, recursive/open-code
compiler, network internal identities, sector traversal, physical cache
producers and machine preservation proofs were **not** independently
rederived. Local direct reads covered the displayed finite constants and
exponent, batching/root selection, local layer boundaries, DAG request
contracts, synchronized tensor identity, packing and physical matrix
boundaries, recursive execution boundary and induction, complete clock and
final three-transform/cost joins. Other audit reports give their broader
local coverage; they are not substituted for source evidence here.

Explicitly outside this comparison: exhaustive audit of either dependency
closure; cross-model simulation; all upstream instruction/taint and array
semantics; upstream toolchain, artifact freshness and axiom closure; a new
upstream compilation; proof extraction to a host executable; the full
synthesis appendix; performance measurements; numerical stability and bit
complexity. The separate semantics review handles the compared machine
goals. Parent verification handles the annotated local tree's fresh build.

This assignment added only this report. No Lean, generated checker, toolchain,
registry, artifact receipt or upstream snapshot was changed; the existing
full local build was left running. Source identity checks passed for the 37
listed upstream files, the shared Core file and both paper subtrees. Focused
formatting checks found no whitespace errors or unclosed code fences in this
new report; this is not a kernel-verification receipt.
