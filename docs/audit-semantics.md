# Semantics and final-statement audit

Scope: `UniformMachine`, `UniformFinalOuterEnvelope`,
`UniformFinalDFTExecution`, and `UniformExponent`, with targeted inspection of
the root machine, final output join, sequential linker, constants/allocation,
upstream Fourier definition, and decimal absorption/final-budget interface.
This is a source-level adequacy review;
fresh kernel/dependency/axiom verification is recorded by the main audit.

Paper: [An explicit power saving for the exact discrete Fourier transform,
pinned PDF](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf),
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently compared
the local PDF and complete introduction, all-lengths, and synthesis TeX blobs
byte-for-byte with that Git revision. PDF SHA-256:
`670d0115ea2553e65f22167c176d2f31218d4d41726fe4e5702e2b149cad0896`.
Page references below were checked against extracted PDF pages and printed
page footers, not inferred from TeX labels. Here PDF and printed numbering
coincide.

## Findings and limits

No theorem/model mismatch or vacuity was found in this bounded scope. This
does not certify the full substantive dependency chain or its cost estimates.

**Informational — literal statement/packaging boundary:** the exact final
target states the main bound (1.2), while numerical helpers already formalize
the absorption supporting Corollary 1.2. `UniformMachine.lean:251–269`
defines the log-log majorant; `UniformFinalDFTExecution.lean:91–95` concludes
that target. `UniformExponent.lean:109–119` proves
`theta < 1 - 2/10^13`. Crucially,
`UniformAsymptotics.paperCost_isLittleO_decimal` (`UniformAsymptotics.lean:58–60`)
proves the paper majorant is **little-o** of
`n*(log n)^(1-1/10^13)`, and `cost_bound_transfer` (lines 68–70) transfers
any Big-O paper bound to that little-o bound. Applying it to
`UniformFinalLinearTableCost.finalBudget_isBigO_paper`
(`UniformFinalLinearTableCost.lean:43–48`) therefore gives the final charged
majorant the decimal bound. Combined with the actual execution's tick bound,
this supports the same machine's decimal corollary uniformly in its inputs.
The paper's log-log absorption (§5.4, PDF p. 23) is thus formalized numerical
mathematics, not a missing analytic proof. No separately packaged, closed
pure-decimal machine statement was located within this bounded inspected
scope; producing one is short logical composition. The distinction matters
only when quoting the *literal type* of `uniformDFT`, not as an algorithmic
or mathematical defect.

**Verification boundary:** `noncomputable section` does not establish
executability, and kernel success alone does not establish paper
correspondence. Here the relevant witness is a closed finite `List
Instruction`, whose allowed transitions explicitly model the paper's exact
arithmetic RAM. This supports a deterministic algorithm **in that model**;
it does not provide a materialized native executable, numerical algorithm,
bit-complexity bound, or measured speedup. The giant fixed printer/role data
were not evaluated. The actual reserve's private opaque witness
(`UniformRecursiveReserve.lean:11–14`) has a concrete finite natural-number
body; it is not an arbitrary complex constant or a runtime oracle. The
existential finite program is sufficient for the paper's model-level
algorithm claim, even though the complex denotations and validity guards are
noncomputable Lean definitions. No extraction theorem identifying an
efficient native evaluator is asserted here; `noncomputable` alone would
not justify the algorithm claim without the finite syntax and actual run.

## Literal target versus Theorem 1.1

| Obligation | Lean evidence | Paper location / result |
|---|---|---|
| One program and absolute constants | `UniformMachine.UniformDFTStatement`, lines 263–269: `p,K,N,degree` precede `n,x`; `UniformFinalOuterEnvelope.of_execution`, lines 30–44, supplies fixed `UniformFinalOuterProgram.program` | §1.1, Theorem 1.1, PDF p. 2 (`thm:main`) |
| Every positive length and every complex input | `0<n` then `∀ x : Fin n → ℂ`; only the time inequality is restricted by `N≤n` | Theorem 1.1, p. 2; finite-range discussion p. 3 |
| Positive sign, no normalization, original output order | `UniformMachine.ComputesDFT`, lines 248–249; `OAI.ExactFourier.zeta` / `fourierMatrix`, `Core.lean:40–43`, use `exp(2*pi*i/n)` and `zeta n^(j*k)` | Introduction, PDF p. 1 |
| Successful finite run from empty heaps | `initial`, lines 76–77; `BoundedExecution`, lines 180–186; final `execution`, lines 32–35 | §1.1, p. 2; §5.4, pp. 23–24 |
| One specified root, independent of x | `D` precedes `∀x`; final root log is exactly `[UniformMasterRootMachine.order n]`; `UniformMasterRootMachine.order_paper_formula` identifies the expression | §5.3, (5.8)–(5.9), p. 23 (`eq:master-root`, `eq:root-size`) |
| Explicitly computed order | `UniformMasterRootMachine.master_execution` constructs the order through the charged integer program and requests the canonical root | §5.3, (5.8), p. 23; the existential `D` alone would not specify a formula |
| Polynomially bounded integer/address values | `WordBound`, lines 168–173, applies at every intermediate state; the envelope adapter preserves the same run and supplies fixed positive degree | §5.4, p. 24 |
| Exact exponent | `ExplicitSeedBudget.paddedRoles=2361183241434822606848=2^71`, `margin=6871402692000000`; residual balance; `UniformExponent.lambda_eq_sub` | (1.1), p. 2; (2.10), p. 11 |
| Charged final asymptotic majorant | actual `execution`, lines 75–87, joins prefix and suffix and bounds their ticks; envelope adapter calls the proved Big-O estimate | (1.2), p. 2; §5.4, pp. 23–24; underlying cost proof reviewed separately |
| Decimal corollary support | `UniformAsymptotics.paperCost_isLittleO_decimal`, `cost_bound_transfer`, and `UniformFinalLinearTableCost.finalBudget_isBigO_paper` compose to a decimal little-o bound for the charged majorant; actual ticks are bounded by that majorant | Corollary 1.2, p. 2; §5.4, p. 23; distinct from the literal `uniformDFT` type |

The theorem does not merely assert a family of circuits with free output
permutations. Its final `ComputesDFT` concerns physical output writes of the
actual terminating RAM run. The supplied root is the precise canonical phase,
not an arbitrarily chosen primitive root.

## Operational semantics checks

- **No free preparation/output oracle.** `Instruction` contains only fixed
  natural/rational literals and elementary arithmetic, input/root provision,
  individual heap access/output, integer branches, jumps and halt. It cannot
  carry arbitrary complex values, array transforms, handlers or functions.
  A fixed program has finitely many fixed register identifiers. Roots append
  to `rootOrders`; no instruction erases that history.
- **Initialized reads.** All heaps and outputs start `none`. Loads from
  unwritten heap cells fail. Registers start at zero; this is a fixed
  initialization convention, not a supplied table or input-dependent cache.
  Each actual memory read/write is an instruction. `BoundedExecution`
  excludes `failed` steps and includes the final halt in the tick count.
- **Input independence and linearity.** Input reads introduce taint;
  addition/subtraction propagate OR, multiplication rejects two tainted
  operands, and division rejects either tainted operand. Stores/loads
  preserve the entire tagged scalar. Natural registers/control cannot be
  assigned from complex data. Thus no instruction can forge an untainted
  value from input data starting at `initial`. This is direct semantic
  reasoning; these four modules do not additionally package a relational
  taint-soundness theorem over pairs of inputs.
- **Division and complex zero.** The semantic denominator test only permits
  a successful prepared division or returns failure; it cannot choose a
  program continuation. `evalField_div_prepared` (lines 230–243) extracts
  both false flags and the nonzero denominator from a successful transition.
  The final all-input success witness must discharge these conditions; it
  cannot exploit a complex branch. This models the paper's proved-valid
  divisions (§1.1, p. 2; Proposition 3.1, p. 12).
- **Determinism.** `step` is a function and
  `Executes.deterministic` (lines 206–221) proves uniqueness of tick count
  and final state for a starting state. There is no nondeterministic
  transition choosing a desired output.
- **Word interpretation.** The bound constrains integer contents, program
  counter, allocated addresses and root orders, not complex magnitudes.
  An unbounded type `ℕ` is therefore not an uncharged large-integer oracle
  along the bounded runs. Exact complex field operations and the supplied
  canonical root remain unit-cost primitives, as explicitly assumed by
  the paper; they are not claimed computable at unit bit cost.

## Same-state joins and paper map

`UniformFinalDFTExecution.execution` obtains the real prefix endpoint,
passes it into kernel/data entry, passes the data clock's own output into
pointwise multiplication, and passes the resulting reindexed state into the
third clock. Its saved-spectrum equality (lines 57–60) relates the very
kernel endpoint to the retained data-state heap. The final output helper
receives those same endpoint states and their proved numeric/heap facts.

`LocalStages.append` joins an identical intermediate state. The apparent
`pc:=0` resets are local helper coordinates: `LocalStages.runs` relocates
the code and turns each charged helper halt into a real continuation jump.
`UniformFinalOuterSuffix.execution` joins the actual prefix to that relocated
suffix and performs the sole final halt. The final proof therefore has no
residual conditional action/cache/child premise at its public boundary.
The correctness of each substantive helper remains part of the wider audit.

| Logical block | Paper argument |
|---|---|
| Prefix / working length / master root / local and CRT tables, final execution lines 36–41 | §5.1–§5.3, (5.3)–(5.9), PDF pp. 21–23 |
| Kernel transform and saved spectrum, lines 42–47 | §5.3, p. 23: fixed convolution operand costs one full transform |
| Variable clock, prepared pointwise product and input-order movement, lines 48–60 | §5.2, (5.5), p. 22; §5.3, (5.7), pp. 22–23 |
| Third forward transform, reversal/scaling/output chirp, lines 61–70 | §5.2, p. 22: `F_L^-1=L^-1 J F_L`; §5.3, pp. 22–23 |
| Actual suffix/prefix/cost join, lines 71–87 | §5.3–§5.4, pp. 23–24; explicit headers, banks and relocation are implementation bookkeeping |
| Final quantifier/envelope adapter | Theorem 1.1, p. 2; §5.4, pp. 23–24 |
| Generic affine recurrence and depth estimates | §2.6, Theorem 2.6, unnumbered recurrence calculation, pp. 11–12; callers must supply actual recurrence/depth facts |
| Exact epsilon and theta gap | §5.4, p. 23; the proof uses an equivalent logarithmic inequality |
| Formal decimal absorption (`UniformAsymptotics.realCost_isLittleO`, `asymptoticCost_isLittleO`, `paperCost_isLittleO_decimal`, `cost_bound_transfer`) | §5.4, p. 23: a positive log-power gap absorbs every fixed log-log power; the generic helper proves this as little-o |

The full synthesis appendix was read to distinguish the alternative route.
Lemma A.2's rational-algebra search and Theorem A.4's bounded printer
(PDF pp. 25–30) supply a separate qualitative `o(n log n)` construction;
they are not a justification for silently treating the main quantitative
algorithm's compilation as free.

## Review procedure and unreviewed scope

Graph Verify-tier generation `2026-10-07T17:50:28Z` still points to the
primary checkout. Assigned new files and targeted new helpers returned
`freshness=not_tracked`; upstream `Core.lean` is wholly `parse_unusable`,
and `ExplicitSeedBudget` has recorded partial ranges 58, 66–67. All cited
files/ranges were read directly. No completeness claim is based on that
stale graph.

Only comments were added to the four assigned Lean files: nested-comment
stripping and whitespace normalization match their pre-edit token streams.
No proof terms, definitions, options, vendored sources or checkers changed.
No build was launched by this subtask; the parent owns the fresh build and
source/artifact-bound receipt.

Not independently reviewed here: the entire finite-network certificate,
every local compiler denominator/schedule, complete synchronization and
physical-packing proof, all prime estimates, all recursive charged-cost
lemmas, canonical verifier trust model, toolchain/Mathlib pins, full public
and private axiom closures, or `UniformAsymptotics` beyond the targeted
decimal-decay helpers and final-budget interface.
Those require the other audit scopes and the final verification record.
