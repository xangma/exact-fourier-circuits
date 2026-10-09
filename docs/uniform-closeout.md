# Uniform proof checkpoint

The original selected-length theorem is verified. The stronger single fixed
algorithm for every positive length is **still open**. The registry has 312
modules and `closed_uniform_algorithm=null`; receipts retain
`uniform_algorithm_verified=false`. The required final result is the
unconditional `UniformMachine.UniformDFTStatement UniformExponent.theta`.

## Current verified work

**Eleven forward-factor modules** pass a fresh normal-path audit of **671
defining-module declarations** with only the standard three axioms, default
proof limits and 283 frozen inputs. The actual 415/430-instruction producers
read stored forward slots, derive translated matching endpoints and selected
typed coefficients, and construct all nine diagonal pools for the tensor
consumer. Their earlier physical `Processed`, coefficient-source and startup
constant banks remain explicit entry conditions. This proves one factor
producer; the complete cache loop and global execution remain open.

Fresh exported bytecode passes **384 exact cases and 1,048,384 steps**, including
320 positive matchings and all 415/430 instruction positions. There are 368
typed K=0 cases and 16 generic K=1 diagnostics; the latter do not prove a typed
K=1 producer. Seven negative controls also pass. Reproduce with
`python3 scripts/check-uniform-forward-factor.py`; see the
[forward-factor receipt](../verification/uniform-forward-factor-foundations.json).

The preceding **23 operational modules** passed a separate source-stable audit
of **2,274 declarations**, inventoried using Lean's defining-module metadata
rather than namespace prefixes. This includes 49 private declarations and generated declarations outside the
anticipated namespaces. The audit binds 284 inputs, permits only the same three standard axioms, verifies all
51 upstream files and uses default proof limits. See the
[module list](../verification/uniform-operational-modules.json) and
[foundation receipt](../verification/uniform-operational-foundations.json).

**Ten operational exact-bytecode suites pass 20,604 cases**. A separate
physical inverse check verifies 21,845 exact matrix entries at q=0..7; the
produced sector-transpose suite also checks 1,360 matrix entries. These entry
checks are not additional execution cases. See the
[bytecode receipt](../verification/uniform-operational-bytecode.json).
Reproduce with `python3 scripts/check-uniform-operational-foundations.py` and
`python3 scripts/check-uniform-operational-bytecode.py`; both reject changes to
their frozen inputs. The new census is
`verification/UniformOperationalCensus.lean`.

| Operational component | Proved execution and boundary |
|---|---|
| Spectator suffix69 | Executes ordinary binary C only on the k-b suffix of all physical role arrays, retaining the low b coordinates. Its charged cost is linear when k-b<m. It does not replace the recursive low-q child. |
| Native scalar106 and exchange98 | Read the actual variable-width records and act on all 2^k cells for k=q*m+r, including nonzero r. Scalar codes and signed pair order are preserved. |
| Stored direct leaf orientations82 | Reads the genuine stored node width/offset and retained original [pool,radix] directory with charged instructions, then prints the real forward lower-Toeplitz word in descending row order, derives its count, and prints the reversed transposed word. Kernel addresses stay relative to the retained kernel prefix even at nonzero subtree offset. All retained coefficient lanes and directory cells survive in ordinary disjoint layouts. |
| Physical copied inverse | Proves the inverse of the actual numeric copied C tensor is one forward q-bit child followed by low-q XOR with 2^q-1, independently in every spectator slice. This is matrix algebra; actual common-child execution remains required. |
| Produced tensor diagonal131 | Reads the physical per-axis [radix,9r-pool] directory, constructs permutation/coefficient/axis-row banks, then traverses all W arrays. The full prepared pool family and complete synchronized schedule remain separate. |
| Sector transpose movement | Actual gathers, child-entry preparation, restoring scatter and all-sector traversal preserve tagged values and outside storage. The continuous produced permutation caller identifies the action with the physical binary tensor. Its child-action premise remains explicit. |

The earlier source-stable focused audit of **46 newly registered modules**
passed, including **4,720 public, generated and private declaration axiom
closures**. Only `propext`, `Quot.sound` and `Classical.choice` occur. The receipt
binds 381 inputs, verifies the 51 unchanged upstream files and pinned
Lean/Mathlib, and records default proof limits. See
[the module list](../verification/uniform-closeout-modules.json) and
[the foundation receipt](../verification/uniform-closeout-foundations.json).

**Nine new normal-path exact-bytecode suites passed 12,329 cases**. They execute
freshly exported literal Lean instructions with exact cyclotomic arithmetic,
checking guards, data tags, frames and bounded integer words. There are no
host-side writes between assembled phases. See
[the bytecode receipt](../verification/uniform-closeout-bytecode.json).

From the repository root, reproduce these focused checks with
`python3 scripts/check-uniform-closeout-foundations.py` and
`python3 scripts/check-uniform-closeout-bytecode.py`. Both freeze their relevant
inputs and reject source changes during verification. The combined environment
census is saved in `verification/UniformCloseoutCensus.lean`.

The previous 2026-10-08 aggregate audits remain historical evidence: 232 modules,
30,079 distinct declaration closures, and 66 bytecode suites with 48,870 cases.
Their [Lean](../verification/uniform-components.json) and
[bytecode](../verification/uniform-bytecode-components.json) receipts bind 561
and 366 inputs respectively. Neither is an aggregate audit of the current
312-module registry; overlapping declaration scopes must not be added together.

| Component | Proved execution and boundary |
|---|---|
| Small CRT axes | The actual fixed182 loop reads the retained CRT metadata and original935 root bank, executes every selected small axis through fixed161 gather/direct-transform/scatter, and preserves roots, metadata and external cells. Native mixed-radix address lemmas identify the output with the corresponding partial tensor of DFTs. For fixed threshold T, actual runtime is at most `(17+(T+1)*(8*T+165))*L`. Large-axis execution is separate. |
| Primitive transforms | Fixed22 computes a direct Fourier array from an actual prepared root; fixed34 batches it. Fixed54 batches the ordinary binary C tensor. These prove exact numeric output, tags, frames and charged costs, but the ordinary binary algorithm does not establish recursive power saving. |
| Physical matching preparation | Fixed23 translates actual row endpoints while retaining coefficient references. Fixed172 produces physical coefficient pools and diagonal banks from real rows and source coefficients. The native diagonal equals the proved matching-phase factor. The complete balanced cache and synchronized phase dispatcher are still required. |
| Sector padding | Fixed205 derives counts and directories from actual rows, then copies the tagged source into role0 and prepares zero cells in all other W roles. It retains startup metadata, roots and unrelated storage and charges all transitions. It does not execute a recursive child transform. |
| Residual movement | Fixed188 derives the residual permutation from the original nonzero direction descriptor. Fixed210 gathers through that produced permutation, with exact address coverage, value/tag preservation and outside frames. The general-k remainder controller and large-q recursive return are not part of this frozen bundle. |
| Edge prototype | Fixed1410 constructs one unit matching across retained axes. At r=196 its chosen depth1 matching is empty. It is not the complete Fourier schedule; actual nonempty depth2 chunks require the full balanced compiler. |

| Exact suite | Cases |
|---|---:|
| Direct Fourier22 | 1,008 |
| Binary batch54 | 480 |
| Direct batch34 | 1,152 |
| Translated rows23 | 208 |
| Small axis161 | 624 |
| Small axes182 | 384 |
| Matching preparation172 | 2,916 |
| Sector padding205 | 5,317 |
| Residual gather210 | 240 |

The small-axis suite uses genuine roots of orders3/5/8 in exact cyclotomic fields,
including Phi60/Phi120. Sector diagnostics use physical W=1/2/3/5; fixed W=2^71
is tested only through the Nat producers. They do not allocate the astronomical
saving arrays. Prepared local coefficient banks and layouts remain the stated
entry conditions. These are instruction-level diagnostics, not a full
empty-state all-length Fourier execution or a CUDA speedup measurement.

## What must close next

1. Finish the physical balanced-tree cache compiler, including every rectangle,
ragged chunk, depth, color, direct leaf and diagonal. Prove its complete schedule
and charge the local preparation once.
2. Finish the actual recursive return controller and opcode0/5 interpreter.
For k=q*m+r, each saving node must call the same fixed q-bit child entry on all
W arrays together, with q(m-1)+r spectator bits retained. W=2^71 and m=1,000,000
remain symbolic. Replacing a large child by the ordinary binary transform does
not yield the claimed exponent.
3. Assemble synchronized tensor phases across all axes, sector movement,
recursive calls, chirp/convolution, CRT transfer and output routing from the
empty initial state. Derive one compatible allocation, polynomial word bound,
exact DFT output and fast runtime for that same finite program.
4. Register and audit the unconditional `UniformDFTStatement`. Only then may
`uniform_algorithm_verified` become true.

No new CUDA/JAX or FFT timing result is claimed by this checkpoint. Earlier
numerical replication and plots keep their documented scope.
