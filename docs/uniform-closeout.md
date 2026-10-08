# Uniform proof checkpoint

The original selected-length theorem is verified. The stronger single-program,
every-positive-length theorem is **still open**. There is no registered closed
proof of `UniformDFTStatement`; aggregate receipts retain
`uniform_algorithm_verified=false`.

Final source-stable audits passed on 2026-10-08: **193 modules and 24,644 distinct
declaration axiom closures**, plus **57 exact-bytecode suites and 24,592 cases**.
The receipts bind 483 Lean inputs and 310 bytecode inputs; every hash was checked
again after both runs completed. The original three theorem checks, five kernel
identities and all 1,101 construction declaration checks also passed again.
The component audit includes generated and private declarations, permits only `propext`,
`Quot.sound` and `Classical.choice`, and checks the 51 unchanged upstream sources
and pinned toolchain. Counts describe verified components, not completed global
algorithm obligations.

## Implemented and checked

This checkpoint adds 16 registered modules to the previous 177-module checkpoint.
Every new registered module passed a normal Lake build under default proof limits
and a complete declaration census matched to its versioned checker.

| Component | Actual behavior and entry boundary |
|---|---|
| Seed-to-matching caller | `UniformSeedHighDataMatchingPreparation`: fixed2669 executes SeedChunk1286, 16 charged ordinary header copies and HighDataConjugateMatching1366. It derives generated rows/count/packing/action internally and retains both coefficient directories, metadata, operands and root. Ordinary physical input, compatible allocation and future caller headers remain inputs; this is not a complete empty-startup matching program. |
| Conjugate retention and high data | `UniformSeedConjugatePreservation` proves exact retention through the real producer chain. `UniformHighDataPackingPreparation` fixed167 copies low physical data above protected coefficient banks before packing. `UniformHighDataConjugateMatchingPreparation` fixed1366 joins that copy to ConjugatePacked1198. `UniformConjugatePackedMatchingPreparation` joins the actual spectrum producer to matching with charged setup; its retained seed, layout and physical data remain stated entry requirements. |
| Actual coefficient values | `UniformMatchingCoefficientValueBridge` links generated forward leaves to their exact values. Inverse references use the negative reciprocal bank for `-1/N`, including the `N=1` pointer exception. Physical pointer equality alone is not used as coefficient-value equality. |
| Inverse matching | `UniformSixCInverseMatchingPreparation`: fixed683 generates inverse rows, matching/packing tables and inverse permutation, then executes the actual six-C/scatter loop. It proves native values `left-mu*right,right`, full frames and conservative dependency flags. It consumes genuine forward rows and retained physical coefficient banks. |
| Per-layer cancellation | `UniformSixCDirtyReplayMachine`: fixed1136 runs forward matching followed by its generated inverse with charged setup. It restores every original numeric coordinate; dependency flags remain conservative ORs. This cancellation component alone performs no cross update. The complete six-phase schedule is open. |
| Explicit binary coordinates | `UniformBinaryTensorCoordinates` bridges least-axis-first physical bit addresses to the upstream tensor coordinates. It proves axis updates, actual stage execution and complete tensor semantics, accounting for the upstream abstract finite-index equivalence. |
| Ordinary C tensor | `UniformBinaryCStageMachine`: fixed30 executes a whole axis in `25*P*Q+6` steps. `UniformBinaryTensorCMachine`: fixed42 executes every axis of a `2^k` tensor, with full exact values, flags and outside frames, in `k*(25*2^(k-1)+11)+8` steps. Prepared physical C coefficients and power-of-two headers remain inputs. This implements the ordinary base transform, not the saving recursion. |
| Output broadcasts | `UniformCrossBroadcastTableMachine`: fixed20 reads the actual Borrowed17 coordinate bank and generates triples `(target+j,borrowed[gates-a+j],positivePointer)` in `14*a+7` steps. It proves the typed cross-output source and a disjoint physical matching, without a supplied matching certificate. Ordinary layout/count/positive-pointer headers remain inputs. |
| Runtime saving-network metadata | `UniformFixedNetworkScheduleMachine` prints the real static chronology and finite scalar codes. `UniformFixedNetworkLiteralDecoderMachine` patches runtime q with charged writes. `UniformFixedNetworkOpcodeMachine` reads and dispatches every actual record format, including ragged bodies, and proves cursor/cost/frame behavior. It decodes instructions; it does not execute their child transforms. Small fixtures use generic records, not a materialized giant fixed seed. |
| Recursive batch headers | `UniformRecursiveBatchHeaderMachine`: fixed25 computes actual quotient, batch/count and volume identities. It does not execute recursive child calls. Diagnostics distinguish genuine base entries from smaller arithmetic loop fragments; no astronomical-threshold recursive trace is claimed. |

Exact-bytecode diagnostics execute the programs exported from the current Lean
sources with exact cyclotomic/rational arithmetic, dependency guards and bounded
words. They disclose generic physical fixture banks, component header
installation, cached typed references and unvisited inherited branches. The
ordinary tensor fixtures independently compare direct full tensor matrices.
No new floating-point CUDA/JAX or FFT performance validation was performed in
this checkpoint.

## Retained follow-on work

The [prototype handoff](../research/uniform-prototypes/README.md) preserves three
byte-identical source snapshots outside normal-library and aggregate
certification: a physical fixed40 scalar-shear child, a fixed796 continuous
forward matching body, and selected-axis193 startup allocation geometry.
Their focused checks and remaining entry conditions are recorded separately.
They are not silently included in the 193-module certification.

## Required before the stronger theorem can close

1. Execute the full six-phase cross schedule: real ascending/descending
depth/color loops, true/false regeneration, both broadcasts, inverse phases,
Fourier action and numeric workspace restoration. Per-layer cancellation and a
forward body are insufficient.
2. Join actual saving-network child execution to the runtime decoder: residual
basis movement, scalar shears, translations, signed exchanges, ordinary padding,
returns and recursive batches. Metadata decoding alone is insufficient.
3. Complete charged startup and common compatible layouts through actual operand
input banks. The selected-axis193 prototype assumes `ell n >= 194`; it still
needs initialization and a smaller-radix fallback, and is not the universal
saving-network scheduler.
4. Assemble every axis, chirp/convolution and output routing in one fixed program,
with one root request and one common polynomial word bound. Bound this same
program's actual charged instructions by the claimed fast runtime. The old
ordinary-base reserve is smaller than the new addressing cost and needs a
constant-factor allowance in the final majorant argument.
5. Prove and register an unconditional `UniformDFTStatement`; only then may
`uniform_algorithm_verified` become true.

The [proof contract](uniform-proof-contract.md) and source-bound
[Lean](../verification/uniform-components.json) and
[exact-bytecode](../verification/uniform-bytecode-components.json) receipts
keep these outstanding obligations separate from verified components.

To reproduce the audits on this Mac, explicitly use macOS Bash. Homebrew
Bash5.3.9 reproducibly stalls on a large embedded Python heredoc; the unchanged
scripts run with `/bin/bash`.

```sh
/bin/bash scripts/verify-lean.sh --skip-cache
/bin/bash scripts/verify-construction.sh
UNIFORM_AXIOM_JOBS=4 /bin/bash scripts/verify-uniform.sh
python3 scripts/check-uniform-bytecode.py
```
