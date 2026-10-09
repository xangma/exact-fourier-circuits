# Upstream uniform theorem and machine comparison

This is a source-level comparison with OpenAI math revision
[`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Computability/FourierTransform).
It does not prove a translation or equivalence between the two machines,
and no upstream build or axiom-closure check was run here. All downstream
Lean sources remained frozen; the existing full build was not disturbed.

The upstream uniform result is present in the **actual solution**:
`OAI.Computability.FourierTransform.Main`, whose 151 lines contain
`OAI.PowerSaving.transform_main_order` (122–127), `convolution_main_order`
(129–135), `transform_main` (137–139), and `convolution_main` (141–143).
`ComparatorChallenges/UniformFourier.json:2–6` selects that solution module.
The two `sorry` bodies in `ComparatorChallenges/UniformFourier.lean:326–331`
are the challenge statements, not the actual solution proof bodies.
The permitted-axiom list in the JSON is a policy, not a measured closure.
`lean/docs/130.md:12` explicitly describes the separate uniform formalization;
its earlier subsequential description at line 10 does not describe this new
uniform theorem. Git history identifies introduction commit
`301488868beec11bfd897168433b0a64f5258559` for the actual Main file.

## Outcome

Both formulations require fixed finite programs, every positive length,
all complex inputs, exact positive-sign unnormalized DFT output, charged
scalar/index/array work, a specified canonical root determined from length,
and polynomial integer/address sizes. No arbitrary-complex-constant or
external-handler oracle was found in either closed machine interface.

Upstream's literal public package covers more conclusions: it includes the
paper bound, decimal bound and `o(n log n)` together, adds two-input
convolution, and its `_order` theorems state the tighter root cap `8*n^3`.
Our literal `uniformDFT` packages the paper bound; existing numerical
absorption helpers support the decimal corollary by composition. Our model
records more concrete operational facts: explicit instruction transitions,
empty initial heaps, intermediate physical addresses and the history of
exactly one root instruction. These differences do not establish that one
whole formal theorem implies the other; a semantics-preserving translation
with cost/storage bounds would be needed for that claim.

## Literal targets

Here `U/` means upstream `lean/OAI/Computability/FourierTransform/`.
Downstream references are relative to this review tree.

| Aspect | Actual upstream evidence | Downstream evidence / comparison |
|---|---|---|
| Fixed program independence | `OAI.PowerSaving.DFTGoal`, `U/Goal.lean:79`, quantifies `order,solve,W` before lengths/inputs; `DFTProgram`, lines 48–58, then quantifies one `cBound` before all positive `n` and all `x` | `UniformMachine.UniformDFTStatement`, `lean/UniformMachine.lean:263–269`, quantifies one program, constant, threshold and degree before `n,x` |
| Canonical DFT/order | `OAI.PowerSaving.dft`, `U/Goal.lean:18–19`, and final Tape equality at line 58; `matrix_definition`, `U/Main.lean:145–146`, is proved by `rfl` | `UniformMachine.ComputesDFT`, lines 248–249, writes the same matrix product at each original output index; vendored Core is byte-identical to upstream Core |
| Exact exponent | `U/Goal.lean:25–33`: `m=10^6`, `W=2^71`, `Delta=6871402692000000`, logarithmic ratio | `UniformExponent.theta` uses `Real.logb` and residuals/W; `lambda_eq_sub` plus residual balance gives the same exact constants algebraically. No cross-project equality theorem was compiled |
| Timing package | `OAI.PowerSaving.TimeBounds`, `U/Goal.lean:75–77`, is the conjunction of paper Big-O, decimal Big-O and little-o of `nlogn`; actual Main supplies it | The exact public target states the paper majorant. `UniformAsymptotics.paperCost_isLittleO_decimal` (lines 58–60), `cost_bound_transfer` (68–70), and `UniformFinalLinearTableCost.finalBudget_isBigO_paper` (43–48) supply formal decimal support; this is packaging, not absent analytic mathematics |
| Explicit root formula/cap | `transform_main_order`, `U/Main.lean:122–127`, gives `(run order n).val=receipt n<8*n^3`; the unadorned goal retains `<1024*n^3` | `UniformFinalDFTExecution.execution`, lines 32–35, names `UniformMasterRootMachine.order n`; `order_paper_formula`, lines 318–321, gives `(2n)*L*2^ceil(log_2(16L))`; `order_bounds` gives `<1024*n^3` |
| Convolution | `OAI.PowerSaving.ConvProgram`, `U/Goal.lean:62–72`, returns all `2*n-1` coefficients for every pair of length-n inputs; actual `convolution_main_order` additionally gives `receipt(2*n-1)<8*(2*n-1)^3` | The audited downstream closed target is DFT only, and its scalar machine rejects two input-dependent factors; it does not itself package an operational bilinear convolution theorem |
| All-length success | Upstream `Code.run` is structurally total via finite loops and depth-bounded recursion; target requires `valid` and exact output for every positive n/all inputs | Downstream requires an inductive finite `BoundedExecution` from `initial` to an actual halt, with no failure steps |
| Polynomial storage words | `U/Goal.lean:53–57` bounds integer `peak`, root order and `W(n)+10(n+2)` by `(n+2)^cBound` | Downstream `WordBound` (lines 168–173) bounds contents and actual allocated addresses at every intermediate state of the same run; no scalar-magnitude bound in either model |

The two roots need not have identical orders. Upstream
`OAI.PowerSaving.Selection.receipt` (`U/LengthSelection.lean:257–260`)
selects `(2*n)*(barge n).vol*2^(orderE n)` when `2^(orderE n)≤n`, and n
otherwise. `orderE` is defined at line 180; `receipt_bound` (262–280)
proves positivity and the strict `8*n^3` cap. Our root implements the paper's
master-root formula directly. A smaller sufficient root does not change
the canonical Fourier output convention.

## Root computation is charged, not supplied as an integer oracle

Upstream `order : Prog false w w` takes only the natural input length.
`DFTProgram` evaluates `d := run order n`, proves `d.valid`, bounds its peak
and value, and uses **that same value** in `root d.val` supplied to solve.
It charges `d.work + 1 + result.work ≤ W n`: the middle unit is the single
root provision. Thus separate order and solve programs do not make order
selection free or input-dependent.

This is implemented in `OAI.PowerSaving.RAM.Bench.orders1` and `executeOne`
(`U/UniformBounds.lean:84–86`, 99–116), then joined by `flagshipOne`
(142–158). `lunch` (52–53) sums the order allowance, one root unit and the
solve allowance. `flagshipOne` uses the order execution's own output
equality to rewrite the root passed to solve, and sums its own time bound
with solve's time bound. `orders2`, `executeBoth` and `flagshipBoth` do
the analogous work for `2*n-1` (88–94, 122–140, 160–178).
`RootPreparation` constructs the finite integer selection program through
`Nick.planOrder`; arbitrary mathematical selection functions are not atoms
of the runtime syntax.

Downstream order selection is part of the one actual initial-state run,
and `.root` appends its computed register value to `rootOrders`. The final
singleton history proves exactly one provision. Upstream has no root atom
inside solve at all: its only supplied scalar is the one root input, whose
provision is charged outside solve. Reusing that scalar does not request
further roots.

## Primitive and control semantics

Upstream `OAI.PowerSaving.RAM.Atom` (`U/RAM.lean:156–171`) contains natural
literals/arithmetic, complex zero/one, same-paint addition/subtraction,
prepared scaling/inversion, typed projections and array access. It has no
arbitrary complex or rational literal and no complex-to-word conversion.
Downstream allows fixed rational literals; these remain finitely many
constants in one fixed program, not n-dependent coefficients supplied for
free. Upstream can build rational constants from 0, 1 and valid prepared
inversion. No constant-factor simulation was formally proved here.

Upstream's `Paint.scalar/left/right/both` types prevent input data from
becoming prepared scalars through the syntax. In transform mode
`allow=false`, `cross` cannot be constructed; in convolution mode it
multiplies a left value by a right value and returns paint `both`.
`inv` accepts only prepared scalars. Its semantic value is total field
inversion, but `valid` requires the operand nonzero (`RAM.lean:189`);
this side condition is not a runtime branch. Downstream uses conservative
Bool taints, rejects two-tainted multiplication, and treats invalid division
as failure. Successful downstream transitions extract a nonzero denominator.
Both use integer-only control and require validity for their final runs.

Upstream `Code` (`RAM.lean:202–216`) is finite first-order syntax even though
its mathematical evaluator uses functions. `Prog` fixes its port to `none`
(247–250), whose handler is `Unit`; there is no external function supplied
to a closed program. The `call` constructor is available only at an open
port and is discharged internally by `descend`, whose handler recursively
evaluates the finite body with decreasing natural fuel (222–245).
Loops, recursion, stack operations and both branches' test computation have
explicit work charges; only the selected branch is evaluated.

Some primitive conventions differ: upstream natural division/modulo by zero
use Lean's total defaults (`RAM.lean:177–178`), and out-of-range Tape reads
return typed blank values while writes during construction are ignored
(59–71, 195). Downstream zero integer divisors and unwritten heap reads
fail. These are genuine semantic differences, not demonstrated defects in
the particular successful algorithms and not a proof of model equivalence.

## Arrays, work and addresses

Upstream Tape functions denote already materialized random-access cells;
they are not callable function closures in the instruction syntax.
`Code.tab` and `Code.sow` invoke charged builders (`RAM.lean:236–241`).
`Bill.sow` initializes len blank cells with an explicit `1+len` charge,
then charges each body and individual write (`143–149`). `Tape.set` is used
by that fresh-array construction, not exposed as a constant-cost instruction
that replaces an arbitrary published array. Identity/projection can share
an existing array address; copying/building entries is charged.

`Bill.peak` propagates maxima of produced integers, loop counters, lengths
and recursion fuel. It does not enumerate physical arena base addresses.
The model's RAM interpretation uses no-reuse allocation: O(work+input size)
cells suffice, and the goal separately bounds that quantity polynomially.
`Ty.fits` and `Code.run_pres` / `prog_pres`
(`U/RegisterBounds.lean:11–15`, 122–182, 184–188) connect peak bounds to
typed integer contents and array sizes. This supports the stated word
interpretation, but is not a step-by-step simulation into our explicit
nat/scalar heaps. Our model represents allocation formulas and intermediate
physical heap addresses directly; its execution joins retain the same states.
The two approaches require different storage justifications.

Both use noncomputable complex denotations and ideal exact-field primitives.
Finite syntax plus the valid closed evaluations supports the respective
model-level algorithm claim. Neither source comparison is a native code
extraction theorem, measured execution or finite-precision result.

## Source identity and verification limits

Read-only snapshot:
`/Users/xangma/repos/exact-fourier-circuits/logs/upstream-comparison-20261009/upstream`.
For every used snapshot source, `git hash-object` of its bytes equalled
`git rev-parse fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:<path>`.
Core, omitted by sparse checkout, was read using `git show` at the exact
revision and its bytes were hash-checked the same way. The verified blobs
are listed below; the last two were only searched, not substantively audited.

| Path (U/ prefix as above) | Git blob |
|---|---|
| U/Main.lean | `86ef40a7050feddb8de005b7a2f96fd9fcc2f24c` |
| U/Goal.lean | `888326d1feb3380476f893314324019a474a681e` |
| U/RAM.lean | `f106bdd1f34d25cc0a5135366c333e19a8efb78f` |
| U/RegisterBounds.lean | `a7566ca0d991491c7e7d9b1b09553ec2599a7856` |
| U/RootPreparation.lean | `2177c2fb0d7ee4ae99a1adfe5ec4301dec3c93be` |
| U/LengthSelection.lean | `4f5b37ae709aaa6f67758409add711c355df0a63` |
| U/TransformProgram.lean | `103d2ddc1e5e40fab6a29b0b93d222a81472d893` |
| U/ProgramConstruction.lean | `6bd3c60cd544b30b783b8e6f5a035b93caa17958` |
| U/UniformBounds.lean | `64fdef464e495da775a2ddadfc65c02367f1c117` |
| U/ProgramBounds.lean | `40f52fe59bf9160ec19ca1241b6622b7017d24d7` |
| U/Cost.lean | `dbf3a08e521887a0d89525c4023490cbc86941be` |
| lean/OAI/Computability/FourierCircuit/Core.lean | `60a4af2dae8058e57961ec9b7978b8535e5b5c9b` |
| lean/ComparatorChallenges/UniformFourier.lean | `5f9657e76f7cfdbba065921d95444ef0bc08ceba` |
| lean/ComparatorChallenges/UniformFourier.json | `1979fcdcaa71194fc71859229091d9fd96deee51` |
| lean/docs/130.md | `c4419a9add293ab5f0fd51c72a193238875affb3` |
| U/WorkBounds.lean | `1677146c634a1553be088e69dec4d3c2e2c53f8e` |
| U/PolynomialBounds.lean | `e63a928a309c3f54577df54fd4a2ccab031a07d3` |

Graph Verify-tier generation `2026-10-07T11:10:24Z` belongs to the older
math checkout. Exact new module/challenge paths had missing freshness,
Core was recorded wholly parse-unusable and documentation was excluded;
all evidence therefore comes from bounded direct source inspection.
Not audited here: the full upstream network/local/tensor/prime/cost chain,
the stronger concrete network stated in Main's module comment, dependency
pins, actual public/private axiom closures, a fresh upstream kernel build,
or any formal simulation between the models. The read sources show actual
proof bodies and precise public statements, not independent kernel success.
