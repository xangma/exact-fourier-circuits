# Constructive saving seed: implementation and audit

The explicit companion paper supplies a constructive witness for its particular
two-coordinate kernel, rather than an executable small witness for the abstract
Lean existence proof. `network.py` now generates that construction as lazy
structured instructions, computes its complete forward-call budget, and runs
small exact checks. The paper's saving instance is too wide to expand or run:
its tensor width is `2^6544863000071` coordinates.

This is a **costed lazy circuit program**, not an expanded `WordStep` list or a
Lean-verified witness. Its metadata retains `expanded=false` and
`kernel_verified=false`. These statements concern this constructed seed, not
whether the existing abstract Lean theorem compiles.

The subsequent [proof contract](proof-contract.md) records exact hypotheses and
missing Lean obligations. In particular, scalar parameters allow `h>=3`, but
the full framed stream fails at `h=3` and `h=6`: the required positive-dimensional
binary complements are alternating. The saving range `h>=22` avoids these
obstructions, as does the tested `h=4` projection. Scalar-only tests at `h=3`
do not certify its framed stream.

## Exact source and scope

Audited local sources, read directly because the parent graph status/indexing
had not established a usable generation:

- `../math/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build/sections/network.tex`
- The same paper's `sections/local.tex` and `sections/synthesis.tex`.
- `../math/lean/OAI/Computability/FourierCircuit/Words.lean`, especially
  `FiniteWinStatement`, forward-only `WordStep.call`, and chronological
  `wordMatrix`.

This is a focused exact-source audit. No repository-wide completeness claim or
graph-generation claim is made. The full Toeplitz/Fourier compiler is outside
this module: the saving seed needs only the paper's scalar network, frame
identity, and constant-size shear compiler.

## What the code implements

`NetworkParameters` computes all sizes without enumerating the enormous role
set. Triples have deterministic combinatorial ranks; neighbors are generated
as disjoint triples followed by triples sharing two elements. Side roles count
**ordered** neighboring pairs. Each stage invocation has separate auxiliaries.

The eight scalar rows are emitted as elementary shears, retaining physical
gate grouping. At stage two the code reverses the rows and their signs and
uses physical `Y` as logical source. Therefore the complete scalar network
maps `(X,Y,A,c)` to `(-Y,X,A,c)` for arbitrary auxiliary contents. Exact tests
check every entry of its matrix at `h=3`, and arbitrary rational/complex dirty
auxiliaries at `h=4`.

`Residual` implements every residual in the paper's table. It uses sparse
orthonormal binary complement bases from `gf2.py`, tensor products with the
fixed prefix and future lines, and lazy coordinate bases. It avoids a dense
million-by-million binary matrix. `iter_network_program` inserts the residual
directions before their scalar gates, then the auxiliary sink edges. A residual
vector `z` uses a forward `C_z` when its signed weight is 1 modulo 4, and an
inverse when it is 3. The inverse needs one forward call and translation by
`z`; no inverse kernel call is allowed or counted.

Directional calls need no explicit basis-change matrix: choose any supported
bit of `z`; each address with that bit zero pairs with `address XOR z`. Applying
the symmetric kernel on those ordered pairs implements `a I + b R_z` exactly.
For `f` columns, perform these pair layers independently in every column.

At the sinks, `TerminalCorrection` translates every exceptional `Y_d` array by
`u_d` in each column, then sends `new X=old Y`, `new Y=-old X`. These are
invertible monomials. The final arrays then each carry `C^(tensor mf)`, including
all dirty auxiliary roles. `SeedPlan.instructions()` additionally emits
ordinary transforms for the padding roles and the transform on the role-index
axes, so the complete structured program acts on exactly `2^b` coordinates.

The program contains macro instructions rather than an exhausted flat C-call
stream. Expanding a directional macro means the ordered-pair calls above;
expanding a pointwise shear means the three-C-call shear word on every address;
expanding the corrections/padding/role-axis macros follows their descriptions.
The global coordinate contract is `index=(role << (m*f)) | address`. Within
the address, column `c` occupies bits `c*m` through `(c+1)*m-1`; a sparse
direction support index names the corresponding least-significant address
bit. Role axis `j` occupies global bit `m*f+j`. Padding applies a forward C
pair layer on each address bit of each added role. The final role-axis stage
applies a forward C pair layer on each role bit, at every address. This agrees
with row-major tensor powers up to the explicitly specified bit convention.
The astronomical stream has not been exhausted, its full matrix has not been
constructed, and this Python program has not been connected to the precise
noncomputable coordinate enumeration of Lean's `tensorPower`.

## Pointwise cost, including shear compilation

Let `v=binom(h,3)`, `d=binom(h-3,3)+3(h-3)`, `I0=3v^2`, `m=h^3`.
One scalar invocation has:

| Rows | Nonzero shears |
|---|---:|
| 0 and 5 (`JA`) | `2vd` |
| 2 and 7 (`Vx`) | `2vd` |
| 1 and 4 (`Rc`, four inputs per target) | `8v` |
| 3 and 6 (`Gx`, three incidence entries plus center sum) | `8v` |
| Total | `4vd+16v` |

Every coefficient is `+/-1` or `+/-1/2`, so the **three**-forward-C nonzero-shear
word applies directly; the six-call device for possibly zero coefficients is
unnecessary. Consequently this concrete construction has

```
H = 3 I0 (4vd+16v) = 36 v^3 (d+4)
```

pointwise calls per address. The underlying identity is
`H' = a^-1 diag(1,i) C diag(1,i)` and
`H' diag(2,1) H' diag(-3,1) H' = [[-8,-10],[0,-6]]`.
Multiplication by `diag(-1/8,-1/6)` gives shear coefficient `5/4`;
conjugating by `diag(4t/5,1)` gives coefficient `t`. All diagonal factors are
nonzero for these rational coefficients.

For the paper's `h=100`:

```
W      = 1873807244643542670000
W_star = 2361183241434822606848 = 2^71
Delta  = 6871402692000000
S      = W_star*m-Delta = 2361183241427951204156000000
H      = 22486194194905980000000
f_min  = floor(2H/Delta)+1 = 6544863
b      = m*f_min+71 = 6544863000071
```

The separate call contributions are

```
directional = S*f * 2^(mf-1)
pointwise   = 2H  * 2^(mf-1)
role axes   = 71*W_star * 2^(mf-1)
g           = (S*f+71*W_star+2H) * 2^(mf-1)
ordinary    = b*W_star * 2^(mf-1) = b*2^(b-1)
saved       = (Delta*f-2H) * 2^(mf-1)
```

At `f_min`, the positive saving coefficient is `847159236000000`. Every
calculation uses ordinary small integers for the coefficients and retains the
exponential factor separately. `FactoredCount.to_int()` refuses counts above
a bounded bit size. There is no allocation or huge integer shift by `b`.

The choice `h=100` is the paper's fixed parameter, not the smallest parameter
for this network. The dimension margin is positive exactly when `h>=22`.
Among integer `22<=h<=100`, this same three-call construction minimizes `b` at
`h=25`: `f=380881`, `b=5951265671`. That width remains unexecutable. This bounded
comparison does not claim a globally optimal saving circuit or a useful
practical crossover.

## Verification and practical interpretation

The focused suite passes 10 tests. Its full `h=4` lazy instruction stream has
62,208 directional steps and 5,376 scalar shears, agreeing with the independent
integer formulas. Every generated residual basis at that size has the correct
dimension and is pairwise orthonormal.

`apply_network_walsh_mode` also executes the **complete framed network**, with
arbitrary complex amplitudes in every role, on four exact Walsh-character
subspaces, including a two-column mode. On such a subspace the directional
kernel is exactly multiplication by `i^[z dot frequency]`, so no `2^64` array is
needed. All outputs equal the expected multiplier
`i^(sum of frequency weights)` times the original amplitudes, including the
auxiliaries. This checks frame cancellation, inverse directions, terminal
translations and the signed bank correction together. It is not a general-array
execution or a full saving-seed verification.

The small scalar and frame examples demonstrate correctness mechanisms. Their
`Delta` is negative and they are explicitly **not saving witnesses**. CUDA can
test their manageable arithmetic or kernel blocks, but cannot materialize this
particular saving seed. No inconsistency was found in the audited network,
dimension budget, or three-call shear identity; the limitation is the size and
the gap between a structured program and a fully kernel-checked finite word.

Focused command:

```
PYTHONPATH=src python3 -m unittest discover -s tests -p test_network.py -v
```

Observed: all 10 tests passed in 6.332 seconds on the local host. Toolchain
installation, existing Lean proof compilation, deployment, and CUDA observations
are separate parent-task outcomes and are not certified by this report.
