# Uniform proof checkpoint

The original selected-length theorem is verified. The stronger single-program,
every-positive-length theorem is **still open**. There is no registered closed
proof of `UniformDFTStatement`; aggregate receipts retain
`uniform_algorithm_verified=false`.

Final source-stable audits passed on 2026-10-08: **232 modules and 30,079 distinct declaration axiom closures**, plus **66 exact-bytecode suites and 48,870 cases**. The receipts bind 561 Lean inputs and 366 bytecode inputs; every hash was independently checked again after both runs completed.

The component audit permits only `propext`, `Quot.sound` and `Classical.choice`,
checks the 51 unchanged upstream sources and pinned toolchain, and includes
public, generated and private declarations. The 21 new modules have a fresh
combined environment census: **2,925 declarations**, including two equation
lemmas created when the translation caller is imported. Counts describe checked
components, not completed global algorithm obligations. The original three
theorem checks, five kernel identities and all 1,101 construction declaration
checks retain their previously verified baseline receipts.

## Implemented and checked

This checkpoint adds 21 registered modules to the previous 211-module checkpoint.
Their normal Lake build and complete declaration checks passed under default
proof limits. The six new suites also passed from their normal repository paths
before the aggregate audits.

| Component | Actual behavior and entry boundary |
|---|---|
| Complete local cross replay | `UniformSixCWholeReplay.execution` executes one fixed **5,375-instruction** program: true Height generation, ascending traversal, positive broadcast, descending traversal, false Height generation, ascending traversal, negative broadcast and descending traversal. It internally produces rows, colors, matching tables, permutations and inverse phases. Actual original typed tape/order/directory, physical coefficient/data banks, compatible allocation and word bounds remain entry requirements. |
| Corrected physical cross action | `UniformSixCPhysicalAction.fullWord_action` identifies the literal physical six-phase word with the logical replay. `UniformSixCCorrectedReplay.execution_cross_matrix` proves the actual program adds `M*x` to the target, restores every numeric source/gate value and leaves non-port coordinates unchanged. This matrix conclusion requires nonempty dimensions, `2*(a+e)<=2^K`, the stated displacement recurrence and coefficient banks equal to `sharedBank(rankKernels)`. Generic coefficient banks establish the literal-word action, not an arbitrary matrix update. Dependency flags remain conservative; numeric restoration does not imply flag restoration. Formal frames retain coefficient sources, constants, data presence, outputs, roots, Nat3001..3020 and scalar cells outside both child footprints. Saved Nat100..106 and the global CRT prefix are not formal frames of this caller. |
| Charged translation | `UniformPreparedYTranslationMachine` is a fixed **116-instruction** program. From original q, width, data and binary direction it constructs the ordinary-integer XOR table and repeated mask, then performs exact translation. It assumes no produced table, mask or action postcondition. Its cost is `tableCost(q)+9*q*width+(17*width+25)*2^(q*width)+31`, at most `(17*width+90)*2^(q*width)` when original width is at least3. Four modules prove the actual block XOR, translation, mask and combined caller. |
| Translation records and mixed chronology | `UniformFixedNetworkYRecordMachine` fixed **197** reads an actual opcode3 tape record, computes sizes/role offsets, executes the 116 child for every row and returns the cursor. `UniformFixedNetworkYRecordLoopMachine` fixed **535** continuously executes arbitrary chronological opcode1/3/4/5 scalar, translation, signed-exchange and padding records, with actual values, tags, frames and charged transitions. Original printed tape, arbitrary-tag role data, prepared C constants and ordinary disjoint layout remain inputs. Opcode0/2/6 and recursive calls remain open. |
| All-axis matching tables | `UniformAllAxisMatchingTablePreparation` fixed **79** reads actual retained selected CRT radices and a physical per-axis matching-edge directory. It executes Matching55 for each axis and derives `SectorPacking.Rows`, `Widths` and forward `Permutations` across every axis. It retains metadata, operands, scalar state, outputs, roots and the protected prefix. Exact cost is `8+sum_j(17*r_j+8*M_j+38)`, at most `axisCount*(21*L+38)+8`. The input matching edges, physical layout and word envelope remain honest entry requirements. This program does not produce the edge directory or prove global tensor action. |
| Multi-axis sector metadata | `UniformMultiAxisSectorMetadataPreparation` fixed **124** reads the saved axis count, executes the actual four-field to three-field projection, computes its own headers and runs SectorMetadata92. Suffix volumes and the complete sector directory follow from real rows; no ready directory or execution result is an input. Cost is `treeCost(counts)+43*axisCount+31 <= 163*volume+31`. Original matching rows/widths/forward permutations and a fresh physical layout remain inputs. All scalar state, saved Nat100..106, source tables, outputs and roots are formally retained. |

The earlier checkpoint verified empty startup and its direct small-length
fallback, scalar/exchange/padding records, charged XOR construction, actual
forward/inverse matching, a complete ordinary binary C tensor, and the physical
matching/broadcast action bridges. Those modules remain registered and checked.

## Exact diagnostic evidence

All diagnostics use freshly exported current Lean programs and exact arithmetic.
They exercise actual instruction guards and bounded words, including dirty
scratch/data and tagged scalar values. No host writes occur between child phases.

| New suite | Successful diagnostic cases | Separate negative controls |
|---|---:|---:|
| Continuous six-phase5375 | 13, totaling 92,013,084 charged steps | 6 |
| Prepared translation116 | 114, totaling 372,873 charged steps | 5 |
| Translation record197 | 241, totaling 1,086,094 charged steps | 5 |
| Mixed record535 | 1,326, totaling 2,823,930 charged steps | 9 |
| Multi-axis metadata124 | 38 | 7 |
| All-axis matching79 | 160 | 9 |

The aggregate case count includes guards for the metadata and all-axis suites;
the other new suites report guards separately. The full replay visits 5,288 of its
5,375 PCs. Twelve K0/K1 cases consume actual typed cross tapes and disclosed
generic coefficient banks; one K2 case consumes the actual rank-kernel shared
bank for `M=[2+i]`, with the required size inequality, and independently checks
that cross-matrix identity. Its typed rows use the proved `crossRows_typed` export
and cached depth array. These are local execution diagnostics, not an
empty-startup/global DFT trace. They check saved Nat100..106 retention empirically;
the formal replay theorem does not yet export that frame.

No new floating-point CUDA/JAX or FFT performance validation was performed in
this checkpoint. Earlier notebook/plot results keep their existing scope.

## Required before the stronger theorem can close

1. Execute the remaining saving-network operations. Copied opcode0 residual C
has q orthogonal column directions; one repeated-mask direction implements Y,
not this C transform. It needs actual q-bit C fibers and recursive calls, plus
opcode2 boundaries, opcode6 layout movement and recursive batching, composed
with the completed scalar/translation/exchange/padding children.
2. Produce genuine matching edges across all selected CRT axes and connect the
actual79 and124 producers to physical tensor packing and the saving action.
The selected startup currently packs one axis with two-slot sectors, so its
sector exponent is `k=1` and `q=floor(k/1000000)=0`. Its convolution FFT exponent
is not that sector exponent. The positive-length selection already guarantees
radix at least2 on every axis, including the binary factor; radix1 is not an
obstruction.
3. Derive one compatible global allocation and the missing retained metadata
frames. Then assemble every axis, chirp/convolution, transfer and output routing
from empty initial state in one fixed program, with one root request and a common
polynomial word bound.
4. Prove the claimed fast runtime for that same actual program. The new ordinary
addressing cost needs a constant-factor allowance in the final majorant;
a mathematical saving word alone does not bound the executed RAM program.
5. Register the unconditional `UniformDFTStatement`. Only then may
`uniform_algorithm_verified` become true.

The [proof contract](uniform-proof-contract.md) and source-bound
[Lean](../verification/uniform-components.json) and
[exact-bytecode](../verification/uniform-bytecode-components.json) receipts
keep these obligations separate from verified components. Agent proof sources were
promoted byte-for-byte from frozen packets; all normal-path checks were repeated.
Graph generation `2026-10-07T17:50:28Z` does not cover the new Lean symbols;
material claims use exact source, complete declaration inventories and kernel
checks, with no graph completeness claim.

To reproduce the audits on this Mac, explicitly use macOS Bash. Homebrew
Bash5.3.9 reproducibly stalls on a large embedded Python heredoc; the scripts run
with `/bin/bash`.

```sh
/bin/bash scripts/verify-lean.sh --skip-cache
/bin/bash scripts/verify-construction.sh
UNIFORM_AXIOM_JOBS=4 /bin/bash scripts/verify-uniform.sh
python3 scripts/check-uniform-bytecode.py
```
