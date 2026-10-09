# Contract for the all-length uniform algorithm

The companion paper's all-length result is now proved by
[`UniformFinalDFTExecution.uniformDFT`](../lean/UniformFinalDFTExecution.lean):

```lean
UniformMachine.UniformDFTStatement UniformExponent.theta
```

This closed theorem has no execution, cache, action or cost hypotheses. The
original subsequential `ExplicitSeed.main` remains a separate verified result.
The [normal final verification](../verification/uniform-final-algorithm.json),
exact closed-statement guard and
[independent Main audit](../verification/uniform-final-independent-main-audit.json)
pass; see the [checkpoint](uniform-closeout.md).

## Operational statement

[UniformMachine.lean](../lean/UniformMachine.lean) defines the finite instruction
alphabet and the exact claim. One finite program is quantified before the
length n. For every positive n, a root order D is chosen before the input
vector, with `0<D<1024*n^3`. For every complex input vector, the program runs
from the empty initial state, emits the standard unnormalized DFT, and makes
exactly that one root request. All intermediate integer values and addresses
are at most `(n+2)^degree` for one fixed positive degree.

For sufficiently large n, the charged instruction count is at most a fixed
constant times

```text
n * (log n)^theta * (log log n)^(4-theta).
```

[`UniformExponent`](../lean/UniformExponent.lean) proves `0<theta<1` and the
exact rational inequality `theta<1-2/10^13`. The runtime includes scalar
preparation, schedule generation, branches, indexing, heap reads/writes and
movement. There is no opaque DFT, circuit-generator or whole-array primitive.
Uninitialized reads fail; prepared divisions require nonzero denominators;
products of two input-dependent values are rejected. Branches test natural
numbers, not arbitrary complex values.

Complex operations are exact and charged at unit cost. Polynomial integer
bounds give O(log(n+2))-bit integer and address words. They do not bound the
precision needed to represent complex scalars. This is not a bit-complexity,
floating-point error or GPU runtime guarantee. Noncomputable semantic
evaluation does not add arbitrary-function instructions or uncharged complex
constants to the finite program; rational literals belong to the fixed code.

## Same-program proof chain

| Stage | Closed link |
|---|---|
| Startup and allocation | Actual working lengths, canonical master root, chirps, normalization, protected CRT maps and shared polynomial allocation are produced from the initial state |
| Local caches | Actual balanced forests, ragged requests, depth/color/replay slots, direct leaves and coefficient banks are generated and retained |
| Recursive saving | The same fixed smaller-body program executes genuine residual children; native handlers, returns, padding and spectators have charged execution proofs |
| Synchronized clock | Physical active-event selection, matching factors, all-axis tensor action, packing, common children and inverse movement execute every clock tick with a uniform cost bound |
| Three-transform caller | The actual 20-stage program joins prepared-kernel and data transforms, retained spectrum, pointwise multiplication, third transform, CRT transfer and output writes |
| Final theorem | `UniformFinalDFTExecution.execution hn x` proves exact outputs, single root and the actual budget; `uniformDFT` derives the unconditional machine statement |

The final caller supplies every component's entry conditions through the same
physical states. Earlier component statements with supplied banks or child
actions remain useful local interfaces; they are not premises of the closed
final theorem. The [historical component receipts](uniform-closeout.md) record
those narrower verification boundaries.

## Constructive replacement and verification

The original `dft_layers` existence proof chooses a scalar outside a finite
forbidden set. The uniform program instead prints the bounded-fanout
convolution DAGs, dirty replay, deterministic layers and explicit zero-free
six-C factors. `UniformDiagonal` uses
`lambda = 1 + sum_j c_j*conj(c_j)` and proves the required nonzero values.
Computed root extraction and independent alpha/beta CRT maps fix the standard
Fourier phase and output order.

The coherent frozen-source audit passes 1,271 modules and 82,513 declaration
closures: 79,030 public/generated and 3,483 private. Only `propext`,
`Quot.sound` and `Classical.choice` occur; the exact closed-statement and frozen
hash guards pass. Six final modules pass fresh default-limit builds. Normal
verification also passes with the exact promoted sources and standard axioms.
It freshly checks Main, the exact target and full census, accepting certified
artifacts only when the compiler and complete source/dependency/artifact
lineage match. Counts of checked declarations do not substitute for the
theorem statement above.
The original 51 upstream modules and their prior receipts remain preserved.

Run `./scripts/verify-uniform.sh`; its closed-target path invokes
`scripts/verify-uniform-final.py` and writes the final algorithm receipt.
`--rebuild-all` forces fresh compilation of every project module. Earlier
component receipts remain historical snapshots; reproducing their original
results requires matching historical sources/configuration.
