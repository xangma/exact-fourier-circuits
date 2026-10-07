# Contract for the explicit saving construction

This contract connects the companion paper and lazy Python construction to
the exact Lean theorem. The original theorem is checked. Our explicit saving
word is not yet checked: its metadata remains `kernel_verified=false`.
The new conditional bridge states exactly what would finish that connection.

## Statements and cost models

`OAI.ExactFourier.MainStatement` in [Core.lean](../lean/OAI/Computability/FourierCircuit/Core.lean)
asserts: for every real `c>0` and natural threshold `N0>=2`, there are `n>=N0`
and a circuit computing the unnormalized matrix
`F[n][j,k] = exp(2*pi*i/n)^(j*k)` with fewer than `c*n*log_2(n)` gates.
The quantifiers allow selected arbitrarily large lengths. They do not give a
fast circuit at every length, bounded coefficients, an accuracy bound,
bit complexity, or an executable construction at practical sizes.

A scalar gate is one addition, subtraction, or multiplication by a fixed
exact complex number. Multiplications by zero and diagonal scalings are
charged. All earlier values and a supplied zero remain available; input and
output aliases, fanout and reindexing need no gates. The coefficients are
elements of mathematical `ℂ`, rather than machine floats.

`FiniteWinStatement` in [Words.lean](../lean/OAI/Computability/FourierCircuit/Words.lean)
has a different intermediate cost: there exist a matrix `A` of size `q`,
`IsUnit A` (invertibility), `not IsMonomial A`, `b>=2`, and a **finite list**
`W : List (WordStep A (q^b))` such that

```
wordMatrix W = tensorPower A b
wordCalls W < b*q^(b-1).
```

`WordStep.call` is a forward `A` call on an ordered injective tuple of
coordinates. `WordStep.monomial` is a permutation with nonzero coordinate
scalings. It costs zero **kernel calls**, but not zero scalar gates.
Words run chronologically; `wordMatrix` uses a reversed matrix product, so a
later operation left-multiplies an earlier operation. Correctness and call
saving must be proved for the same word, on exactly `q^b` coordinates.

For our kernel `C=[[(1+i)/2,(1-i)/2],[(1-i)/2,(1+i)/2]]`,
[ConstructiveBridge.lean](../lean/ConstructiveBridge.lean) proves invertibility
and nonmonomiality. Its `finiteWin_of_word` and `main_of_word` accept a literal
`W : List (WordStep C (2^b))`, its tensor identity, and strict saving.
They supply the exact finite-win and Fourier conclusions. They supply no word.

## Reusable Fourier bridge

The remaining construction work ends at `finiteWin_of_word`. These existing
upstream results already handle the rest:

| Result | Role |
|---|---|
| `Amplification.cost_word_power`, `normalized_recurrence` in [TensorCostAlgebra.lean](../lean/OAI/Computability/FourierCircuit/TensorCostAlgebra.lean) | Convert call saving into a scalar-cost recurrence, charging monomial overhead through `W.length` |
| `Amplification.tensor_amplification` in [AmplificationMaster.lean](../lean/OAI/Computability/FourierCircuit/AmplificationMaster.lean) | Obtain exponent `0<a<1` and tensor cost `O(q^k*(k+1)^a)` |
| `PositiveGeneration.positive_generation` in [ParameterAlgebra.lean](../lean/OAI/Computability/FourierCircuit/ParameterAlgebra.lean), `ParallelTensorCost.layered_cost` in [PairFamilies.lean](../lean/OAI/Computability/FourierCircuit/PairFamilies.lean) | Generate invertible local matrices using fixed forward-call patterns and bound their tensor cost |
| `NewtonFourier.dft_layers`, `FourierCRT.factorization` in [ToeplitzCross.lean](../lean/OAI/Computability/FourierCircuit/ToeplitzCross.lean) | Factor exact Fourier matrices and combine coprime sizes |
| `FourierTransfer.family_cost`, `win_to_fourier` in [Main.lean](../lean/OAI/Computability/FourierCircuit/Main.lean) | Obtain unbounded Fourier lengths with normalized scalar cost tending to zero |

The original `GraphBlocks.finite_win` proves existence by contradiction through
matrix prices. It does not identify that witness with the Python network.
Our witness can use `win_to_fourier` directly once its obligations are proved.

## Parameter and coordinate contract

Use integer `h>=22` for the saving witness, and define

```
v = binom(h,3)                         d = binom(h-3,3)+3*(h-3)
m = h^3                               I0 = 3*v^2
W = 2*v^3 + I0*(v*d+h+1)              Delta = 2*v^3-2*I0*(h+1)*h
r = ceil(log_2(W))                    W_star = 2^r
S = W_star*m-Delta                    H = 3*I0*(4*v*d+16*v)
f = floor(2*H/Delta)+1                 b = m*f+r.
```

Here `W` is the number of **roles**, not the word list. `S` counts residual
directions after padding. `H` counts the three-C compiled scalar calls per
address. The natural-number subtraction defining `S` needs the dimension
identity and nonnegativity proof; truncated subtraction cannot silently replace
the paper's integer arithmetic. Prove `Delta>0` and `f>=1` for the selected
instance. The companion paper's recursive batch restriction `f>=72` is not
needed merely to certify this finite seed.

`NetworkParameters` accepts `h>=3` to describe scalar sizes. That is not a
sufficient hypothesis for every framed construction: the all-ones triple at
`h=3`, and disjoint triples covering all six coordinates at `h=6`, have
alternating orthogonal complements with no orthonormal basis. `gf2.py` rejects
those inputs. The saving range avoids both obstructions. Our tested `h=4`
projection also needs its own pivot-existence argument, rather than the paper's
argument using a coordinate outside a support of size at most six.

Python uses `index=(role << (m*f)) | address`. Column `c` uses address bits
`c*m` through `(c+1)*m-1`; role axis `j` uses global bit `m*f+j`.
Sparse tensor factors flatten in row-major order, with the last factor
fastest. A direction pairs addresses `x` and `x XOR z`, using a chosen
supported bit to enumerate each pair once. The kernel is symmetric, but the
word's embeddings must still be ordered injections.

Lean's `tensorCoordinates` is a noncomputable `Fintype.equivFin` enumeration.
It promises neither this bit ordering nor this tensor-factor ordering.
Construct a finite coordinate equivalence and conjugate the compiled word.
`TensorAxis.source_power_reindex` supplies the existing bridge to recursive
Kronecker powers; `CircuitCost.cost_reindex` preserves scalar cost. The new
word relabeling must also preserve forward-call count.

## Dependency map and missing statements

Names below are proposed proof obligations unless an implemented declaration
is explicitly named. Each statement must be symbolic over the finite index
types; exhausting the astronomical instruction stream is unnecessary.

For `triple_incidence_identity`, let T be the three-element subsets of `Fin h`,
E the ordered pairs `(S,T)` with intersection size 0 or 2, B=`ℂ^T`,
A=`ℂ^E`, and K=`ℂ^(Fin h + {*})`.
The maps have domains `V:B->A`, `G:B->K`, `J:A->B`, `R:K->B`, with

```
(Vx)[S,T] = x[T]
(Gx)[j] = sum_{T containing j} x[T]     (Gx)[*] = sum_T x[T]
(JA)[S] = -sum_{T neighbor S} ((|S intersect T|-1)/2)*A[S,T]
(Rc)[S] = (sum_{j in S} c[j]-c[*])/2.
```

The coefficients use integer/rational arithmetic embedded in ℂ, including
the negative coefficient at intersection size 0. Prove `R*G+J*V=I_B` with
these orientations. This is distinct from binary incidence dot products.

| Obligation | Required statement and hypotheses | Current evidence |
|---|---|---|
| `triple_incidence_identity` | With `G` the triple-incidence rows plus center row, `R` carrying the `-1/2` coefficients, and `J,V` the even-intersection adjacency maps, prove the **complex** identity `R*G+J*V=I` with correct ordered-pair indexing | `ScalarNetwork.incidence_identity` and `invocation_dirty_identity` prove the actual complex maps and all-dirty invocation; `TripleCounting` proves neighbor/edge/role cardinalities by bijections |
| `triple_pivots_exist` | A triple has an unused pivot; two norm-one, mutually orthogonal neighboring triples admit the second pivot after the first transvection, for the required `h>=22` | `BinaryComplement.triple_indicator_valid_pivot` and `triple_pair_valid_pivots` prove existence; the pair result needs ambient cardinality at least 7, satisfied by the saving range |
| `transvection_frame` | Over `ZMod 2`, `T_v(x)=x+<v,x>v` preserves the dot product and is an involution when `<v,v>=0`; map coordinate pivots to prescribed norm-one orthogonal vectors using `T_first o T_second` | New [BinaryFrames.lean](../lean/BinaryFrames.lean) formalization |
| `complement_frame` | Under successful distinct-pivot hypotheses, the remaining transformed coordinate vectors form an orthonormal basis of the prescribed orthogonal complement | `BinaryComplement.oneComplementBasis` and `twoComplementBasis` package actual spanning orthonormal bases and cardinalities; individual triple and pair existence proved |
| `residual_partition` | For every row/edge and stage, prove the exact nested orthogonal sums with orthonormal residual bases, and equal source/target labels at every scalar shear. Consecutive stage boundaries agree; only central row 3 to row 4 decreases | `BinaryResiduals` proves all eleven symbolic decomposition shapes, tensor/direct-sum bases, empty factors and actual central decrease dimension; `GateFrames` instantiates actual common gate labels and geometric residual bases; `TripleInvocationFrames` proves concrete initial, consecutive and final bank spaces. Full invocation chronology and global assembly remain |
| `signed_weight` | Tensor frames preserve the product dot form, including the empty tensor; unit directions have odd weight. Prove tensor weight multiplicativity and weight additivity modulo 4 for orthogonal vectors. Increasing edges use inverse at weight 3 modulo 4; decreasing edges use inverse at weight 1 | `BinaryTensor` proves tensor dot/weight products, empty tensors, and orthogonal weight additivity modulo 4; `FrameSpectrum` proves both signed kernel phase rules |
| `signed_frame_spectrum` | For a nondegenerate binary subspace U with orthonormal basis, use forward C_z at weight 1 modulo 4 and inverse C_z at weight 3. Prove its Walsh multiplier is `i^wt(P_U(xi))`, with P_U the orthogonal projection, including basis independence and ratios for nested subspaces | `FrameSpectrum.signedWord_frame` proves whole-array identities using Walsh completeness, plus actual frame inverses and the terminal ratio; `BinaryProjection` proves basis independence and actual geometric residual ratios |
| `directional_pairs` | For `z!=0` and `f>=1`, one column's pair expansion computes `C_z=a*I+b*R_z` using `2^(mf-1)` forward calls. A Python DirectionalStep has f column layers, hence `f*2^(mf-1)` calls. Its inverse is a forward layer then translation | `DirectionalWords.compile_directional` and `compile_inverse_directional` give literal ordered-pair words with exact matrix and count; the latter uses forward calls plus translation |
| `lift_scalar_edge` | Source and target frames intertwine every scalar shear; arbitrary dirty auxiliary data is preserved | `FrameCommutation.compatible_frames_commute` proves actual linear address-frame commutation under the nonzero-entry support condition; `GateFrames` discharges the actual forward and reverse row support conditions; global assembly remains |
| `network_terminal_identity` | Stage prefixes telescope, stage two retains physical frame labels while reversing scalar rows/signs and exchanging logical banks. The exceptional triple-tensor direction has weight 27. Translate Y first, then apply `(X,Y)<-(Y,-X)` to restore all roles to the ordinary transform | `TripleNetwork` implements the actual three physical axes, reversed stage-two updates and side-pair orientation; arbitrary dirty auxiliaries are restored. `FrameSpectrum.terminal_frame_ratio` proves the whole-array line/perp terminal ratio. `TerminalWords` supplies the literal free correction and an ordinary per-role word; it consumes the still-missing full labeled-network action |
| `compile_nonzero_shear` | Each coefficient `+/-1,+/-1/2` has a typed three-forward-C word with invertible monomials, in the specified chronological order | `TypedKernelWords.shearWord_matrix`/`shearWord_calls` prove the literal three-C list. `RoleWords` proves its physical pointwise action, source/other-role restoration and multiplied count |
| `padded_seed_identity` | Add `W_star-W` ordinary roles, then all role-axis transforms, giving `C^(tensor b)` on exactly `2^b` coordinates for every input | `TensorWords` proves embedding, parallel copies, tensor-coordinate transport and an ordinary tensor word; `PaddingWords` proves literal padding, role axes and tensor fusion given a correct network word; that network input is still missing |
| `seed_word_count` | The very same finite word has `g=(S*f+r*W_star+2*H)*2^(mf-1)` calls; prove every combinatorial enumeration and injection cardinality | `TripleCounting` verifies actual finite role/edge counts; component word counts and the actual `ColumnSchedule` lift are checked. The residual sum and the assembled saving-word count remain |
| `strict_seed_saving` | With `S+Delta=W_star*m`, `Delta>0` and the floor choice of `f`, show `g<b*2^(b-1)` and `b>=2` | `SavingBudget` proves general cancellation and floor choice. `ExplicitSeedBudget` proves the closed h=100 arithmetic inequality with astronomical powers left symbolic; the formula is not yet tied to a saving word |
| `constructive_finite_win` | Feed the word, its identity and its strict call bound into `ConstructiveBridge.finiteWin_of_word` | Conditional bridge checked; explicit inputs missing |

Pivot and complement existence, signed spectral identities and literal component
compilers are now checked. The critical path is the complete gate/frame schedule,
stage coordinate identities, and action/count proofs for the assembled word. The budget
algebra and upstream Fourier transfer do not resolve any missing action identity.

## Numerical interpretation and verification boundaries

Machine precision cannot invalidate these exact-complex statements merely by
making their floating-point implementation inaccurate. The [isolated-shear experiment](isolated-shear-stability.md) exhibits complete source loss on normal finite inputs despite an exact two-coordinate matrix identity. A disagreement can
instead expose a wrong translation, wrong ordering, or an unstable concrete
implementation. We investigate those separately with exact references and
retained CUDA arrays. Bounded projections do not inherit the full seed's saving
and do not establish full-width stability.

New proof checks use pinned Lean/Mathlib and inspect axiom closures for only
`propext`, `Classical.choice`, and `Quot.sound`. The checks exclude `sorry`
and custom axioms. This contract makes no claim that all rows above are proved.
The original 51 upstream modules remain unchanged.

Source discovery used the `exact-fourier-circuits` graph at generation
`2026-10-07T11:11:44Z` and targeted traces/snippets for Python, followed by exact
source reads for Lean's flagged whole-file parser gaps. This is a focused
dependency audit, not an exhaustive graph completeness claim.
