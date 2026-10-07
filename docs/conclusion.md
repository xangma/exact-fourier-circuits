# Exact saving and finite-precision behavior

The papers supplied the missing construction: a literal finite Lean word with
both its exact tensor identity and a strict forward-C-call saving proved.
The integrated build and axiom audit passed all 1,101 registered declarations.
The 51 original modules are unchanged; the axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`.

The [finite tensor paper](../../math/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf)
provides the exact Fourier transfer, while the
[explicit construction paper](../../math/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf)
provides the incidence network, binary frames, residual accounting and padding.
Their details resolved the physical stage-two reversal, terminal correction,
actual residual total and cost of role-axis layers.

## What Lean proves

[ExplicitSeed.lean](../lean/ExplicitSeed.lean) defines the actual `h=100` word:
three chronological network stages, terminal correction, coordinate
canonicalization, padding, role-axis transforms and tensor fusion. Its
`word_matrix`, `word_calls` and `word_saves` certify the same list of operations.
The closed `witness` and `finiteWin` have no circuit-action or count premises;
`main` derives the exact Fourier theorem through the unchanged upstream bridge.
The [proof contract](proof-contract.md) maps the dependencies, and the
[verification receipt](../verification/constructive-seed.json) records source
hashes and axiom closures.

For the kernel `C=[[(1+i)/2,(1-i)/2],[(1-i)/2,(1+i)/2]]`, the witness has

```
columns = 6544863
b = 6544863000071
width = 2^b
saved forward C calls = 847159236000000 * 2^6544862999999
```

This comparison uses exact natural-number arithmetic. Machine precision does
not enter the count or matrix proof. Free invertible monomials belong to the
intermediate call model; the upstream transfer charges their scalar overhead.
The Fourier conclusion applies at selected unbounded lengths, and supplies no
floating-point error bound or practical faster FFT.

The word uses noncomputable finite coordinate and basis choices. The Python
producer follows the paper but has no formal translation proof to this Lean
word; its `kernel_verified=false` metadata therefore remains appropriate.
Even the smaller `h=25` seed has billions of address bits. Materializing either
saving seed or benchmarking its full Fourier implementation is infeasible.

## What CUDA establishes

On **len / RTX4090**, the bounded projected network was checked in 48 cases;
worst relative L2 errors were `1.59e-6` in FP32 and `2.06e-15` in FP64. Those
projections have no claimed saving and do not establish full-width stability.

A focused experiment checked all 9,360 retained isolated-shear cases against
exact references. With coefficient `t=1`, the literal three-C implementation
changes source `1` to `0` beside target `2^24` in FP32 or `2^64` in FP64.
Direct shears preserve source `1`. CPU traces identify the first rounding step
at which source-one and source-zero states become identical; later exact
cancellation cannot recover that lost information. FMA on/off gave identical
output bytes. Common normalization removed observed overflow while retaining
source loss. [Counterexamples, controls and reproduction](isolated-shear-stability.md).

These results establish componentwise failure of this arithmetic ordering on
normal finite inputs. A normwise metric can hide the entire small-source error
beside the large target. They do not invalidate the exact Lean theorem or prove
instability of every permitted saving circuit. The exact saving and the tested
implementation's numerical failure are separate, verified outcomes.
