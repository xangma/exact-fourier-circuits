# Uniform proof checkpoint

The original selected-length theorem is verified. The stronger single fixed
algorithm for every positive length is **still open**. The registry has 278
modules and `closed_uniform_algorithm=null`; receipts retain
`uniform_algorithm_verified=false`. The required final result is the
unconditional `UniformMachine.UniformDFTStatement UniformExponent.theta`.

## Current verified work

On 2026-10-09, a source-stable focused audit of **46 newly registered modules**
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
278-module registry; overlapping declaration scopes must not be added together.

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
