# Uniform proof checkpoint

The original selected-length theorem is verified. The stronger single-program,
every-positive-length theorem is **still open**. There is no registered closed
proof of `UniformDFTStatement`; verification receipts keep
`uniform_algorithm_verified=false`.

Final audits passed on 2026-10-08: **177 modules and 21,585 distinct permitted
axiom closures**, with all 51 upstream sources and toolchain pins unchanged;
**44 exact-bytecode suites and 23,197 cases**. The source-stable receipts hash
451 Lean inputs and 268 bytecode inputs. The original theorem/kernel checks and
all 1,101 original construction closures also passed again. Both aggregate
receipts still record `uniform_algorithm_verified=false`.

## Implemented and checked in this checkpoint

| Component | Actual program and proved behavior |
|---|---|
| Conjugate spectrum | `UniformConjugateRankSpectrumPreparation`: 763 instructions load actual retained compact **inverse-H lane 3** and G lane 4, run the rank-spectrum producer, and reverse frequencies in each of seven blocks. Its 18-instruction reversal helper costs `91*N+6`. The full producer costs at most `RankCross.runtimeBudget(selected parameters)+91*N+29`. It preserves original and conjugate seed directories, metadata, operands and the master root. `seedHeight_sources_retained` connects the actual old and new coefficient banks to the coefficient loader. |
| Physical coefficient load | `UniformMatchingConjugateLoadMachine`: 18 instructions load the coefficient and its conjugate from prepared banks, including a charged negation for signed coefficients. The 25-instruction row caller reads the actual generated coefficient pointer. Real normalization constants retain the existing pointer policy; this does not prove arbitrary rational leaves have that policy. |
| Zero-free six-C shear | `UniformZeroFreePairShearMachine`: 359 instructions derive the shift and all four scales internally, certify prepared divisions, and execute the actual six-C pattern. It preserves the numeric source and produces `left+mu*right`, including `mu=0`; both dependency flags become their OR. |
| Generated matching loop | `UniformPackedMatchingShearMachine`: 422 instructions read the count from generated Nat register 894, load each row's actual coefficient, run six-C shears, and scatter through the generated inverse. Its producer adapter consumes genuine SeedChunk and Packed postconditions. Runtime is at most `388*M+9*L+21`; count, table and inverse are derived. Ordinary caller headers and physical conjugate-bank sources remain entry requirements. |
| One tensor fiber | `UniformSelectedAxisFiberPreparation`: fixed 49-instruction gather/scatter derives P/r/Q from actual metadata and copies complete Scalar values, including dependency flags. Cost `9*r+7*axis+35`. Its 12-instruction copy helper costs `9*r+4`. |
| All tensor fibers | `UniformAllTensorFibersCopyMachine`: fixed 55-instruction gather/scatter computes P/r/Q once and visits every fiber, preserving exact Scalar values and their flags. It proves the complete permutation and inverse, retains metadata, and costs `F*(9*r+27)+7*axis+14 <= 36*L+7*axis+14`. Canonical and actual-Operands corollaries retain the same `(n+2)^19` bound. |
| Fixed network scalar encoding | `UniformFixedCoefficientCodec` proves every actual forward/reverse fixed-block shear coefficient is in `{0,+/-1,+/-1/2}`. Finite scalar codes preserve the complete block chronology and compiled word. This is static metadata, not a RAM execution of the saving network. |

The conjugate diagnostics execute real 1460 startup, original 835 preparation
and the new 763 producer as separate phases, with only ordinary caller headers
installed between phases. All 40 producer cases distinguish inverse-H from the
wrong Newton-H lane. Together with eight reversal cases they give 48 exact
successes, 200 genuine runtime-guard failures and 80 separately classified
invalid-source controls. They visit 752 of 763 producer PCs and all 18 helper
PCs; the remaining inherited branches are disclosed.

Six-C pair, row-loader and packed-loop diagnostics use exact cyclotomic/rational
arithmetic and generic physical bank/table fixtures. They do not assert that
those fixtures execute the complete selected-axis producer or the global fast
algorithm. No new floating-point CUDA/JAX validation was performed in this
checkpoint.

## Required before the stronger theorem can close

1. Join the actual conjugate producer to the generated packing/matching
   execution with charged caller setup. Prove preservation of packed values,
   inverse/table cells and Nat894 through the producer; ordinary original-only
   allocation does not by itself preserve later conjugate banks.
2. Prove coefficient-value equality for actual forward leaves `{+/-1,1/N}`;
   the current generated adapter proves physical pointer equality. Its
   `seedWord` is forward-only. The inverse extension must use `P+3` for
   `-1/N` when `N>1` (`P+1` when `N=1`); reusing `fromReference` would
   incorrectly select positive `P+2`. Execute the full forward/inverse dirty
   local schedule, restore numeric workspaces, and connect it to Fourier action.
3. Implement the corrected fixed saving network and recursive batches, with
   actual monomial movement, all-axis scheduling and the small-case fallback.
   The proved count majorant must bound this same program's instruction count.
4. Join chirp/convolution/output routing and prove one common polynomial word
   bound, one root request and the claimed fast runtime for the final fixed
   program. Register and kernel-check its unconditional `UniformDFTStatement`.

The [proof contract](uniform-proof-contract.md) and source-bound
[Lean](../verification/uniform-components.json) and
[exact-bytecode](../verification/uniform-bytecode-components.json) receipts
separate these outstanding obligations from verified components.
