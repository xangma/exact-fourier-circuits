# Uniform theorem closeout

The stronger all-length theorem is closed:
[`UniformFinalDFTExecution.uniformDFT`](../lean/UniformFinalDFTExecution.lean)
proves `UniformMachine.UniformDFTStatement UniformExponent.theta` without
inputs or execution hypotheses. One fixed finite program computes the exact
standard unnormalized DFT at every positive length.

Its `execution hn x` theorem starts the actual 20-stage program from the empty
initial state. It prepares the real caches, runs three complete Fourier clocks,
retains the kernel spectrum, performs pointwise multiplication and CRT/output
routing, and emits the DFT. The same execution has exactly one specified
master-root request, a common polynomial integer/address bound and the
charged fast runtime. No child, advance, global action, selected-count or
cost-bound premise remains in the final theorem.

The bound is `O(n*(log n)^theta*(log log n)^(4-theta))`, with `0<theta<1` and
`theta<1-2/10^13`. Its exact complex unit-cost model and practical limits are
specified in the [uniform contract](uniform-proof-contract.md).

## Current verification status

The coherent frozen-source audit passes **1,271 modules and 82,513 declaration
closures**: **79,030 public/generated and 3,483 private**. Only `propext`,
`Quot.sound` and `Classical.choice` occur. The frozen hash checks and exact
`UniformDFTStatement UniformExponent.theta` guard pass. All six final theorem
modules pass fresh builds with default proof limits. Seven historical source
files retain their prior limit options; the default-limit claim does not
cover every source in the import cone.

The [normal final verification](../verification/uniform-final-algorithm.json)
and [independent Main audit](../verification/uniform-final-independent-main-audit.json)
also pass. The normal proof imports only the promoted project sources and
pinned dependencies, with no scratch proof imports. It freshly checks Main,
the exact target and the complete census. Its 1,270 reused project artifacts
are accepted only after compiler, source, artifact and complete import-lineage
checks against the coherent audit; one project Main is rebuilt, followed by
an additional fresh normal Main check.

Reproduce the current final proof from the repository root:

```sh
./scripts/verify-uniform.sh
# Force fresh compilation of all project modules:
./scripts/verify-uniform.sh --rebuild-all
```

The wrapper dispatches to `scripts/verify-uniform-final.py` for the closed
registry. The normal receipt records `uniform_algorithm_verified=true`.

The complete-clock component receipt covers five modules and 63 defining-module
closures, including three private declarations, with 1,235 frozen inputs. Its
literal program proves boot, every finite axis, every clock iteration and the
terminal branch/halt, with exact numeric values, prepared tags, retention and
the actual `clockEnvelope` bound. The outer theorem supplies that clock's real
entry conditions internally for all three transforms.

No new CUDA measurement or giant saving-array execution accompanies these
proofs. Existing [JAX/CUDA results](jax-investigation.md) keep their measured
implementation boundaries.

## Historical component audits

These receipts describe earlier source snapshots and component entry
conditions. Their overlapping declaration counts must not be added together,
and old `uniform_algorithm_verified=false` fields describe those historical
packets rather than the new closed theorem.

| Packet | Lean evidence | Exact diagnostics |
|---|---|---|
| Recursive foundations | 29 modules; 2,552 defining-module closures, 104 private; [receipt](../verification/uniform-recursive-foundations.json) | 5,640 cases, 5,547,308 steps and 45 adverse controls |
| Forward factors | 11 modules; 671 defining-module closures; [receipt](../verification/uniform-forward-factor-foundations.json) | 384 cases, 1,048,384 steps, all 415/430 instruction positions and seven negative controls |
| Operational foundations | 23 modules; 2,274 closures, 49 private; [receipt](../verification/uniform-operational-foundations.json) | 20,604 cases and 21,845 independent inverse entries; [bytecode receipt](../verification/uniform-operational-bytecode.json) |
| Earlier closeout foundations | 46 modules; 4,720 closures; [receipt](../verification/uniform-closeout-foundations.json) | 12,329 cases; [bytecode receipt](../verification/uniform-closeout-bytecode.json) |
| 2026-10-08 aggregate | 232 modules; 30,079 closures; [receipt](../verification/uniform-components.json) | 66 suites, 48,870 cases; [bytecode receipt](../verification/uniform-bytecode-components.json) |

Historical entrypoints, retained for compatibility:

```sh
python3 scripts/check-uniform-recursive-foundations.py
python3 scripts/check-uniform-forward-factor.py
python3 scripts/check-uniform-operational-foundations.py
python3 scripts/check-uniform-operational-bytecode.py
python3 scripts/check-uniform-closeout-foundations.py
python3 scripts/check-uniform-closeout-bytecode.py
```

The four foundation proof scripts now forward a closed registry to the
current final verifier; they do not regenerate the old checkpoint receipts.
The bytecode scripts remain focused component diagnostics and were not rerun
by final proof verification. Exact historical reproduction requires the
matching source/configuration commit or packet; archived inputs are under
`verification/historical-uniform-components-341`. Use the canonical command
above for the current complete theorem.

The prior operational suites intentionally exercised component boundaries:
prepared banks, supplied layouts, small exact cyclotomic roots and physical
role counts W=1/2/3/5. The fixed W=2^71 saving arrays were not allocated.
Diagnostics with synthetic larger-height data did not establish typed producer
executions at that height. These limitations remain facts about those tests;
the universal final Lean theorem is established by proof, not by extending
the fixtures to astronomical saving instances.
