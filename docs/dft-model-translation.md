# Translating the actual DFT program

**Status: component proofs; the complete translation remains open.** Our existing
all-length DFT theorem is checked in `UniformMachine`. This work does not yet
establish that its actual program meets OpenAI's typed-RAM contract. It uses the
unchanged `RAM` and `Goal` definitions pinned in
`lean/ModelEquivalenceUpstream/MANIFEST.json`, rather than OpenAI's independent
DFT algorithm as a replacement witness.

## How affine intermediates can be represented legally

For an input-dependent source value `a`, let `a₀` be its value in the same
execution with zero input. Represent the value by:

```
(dependence flag, (prepared offset a₀, homogeneous data a − a₀))
```

Prepared values have zero homogeneous component. Original input values have
zero offset. A typed operation can update both components together without
injecting a prepared scalar into the data channel. The flag preserves the
source restrictions on multiplication and division, including a flagged zero.

`DFTModelAdmissibilityControl.initial_execution_match` proves from instruction
semantics that changing the input preserves the exact successful instruction
count, control flow, natural registers/heaps, prepared scalar values and word
bounds. `DFTModelAdmissibilityActual.actual_zero_match` applies it to our literal
twenty-stage DFT program and establishes zero terminal output on zero input.
It does not assert that intermediate offsets are zero.

`DFTModelAffinePaired.paired_field_success` proves that one actual typed field
operation returns both components of the matching source/zero-source result,
with constant charged work. `DFTModelAffineActual.actual_zero_projected` proves
that projecting the homogeneous part of the paired terminal source values
returns the DFT. This last theorem is a semantic endpoint theorem: the complete
compiler must still construct and maintain the paired state through memory and
control flow.

This does not contradict the affine counterexample in
[the model comparison](machine-model-comparison.md). A general affine function
may have nonzero terminal offset. Dropping that offset would change its answer.

## Checked components and explicit boundaries

| Component | Established boundary |
|---|---|
| Input/zero-input control correspondence | Actual source execution, unchanged ticks and bounds; not a typed interpreter. |
| Paired field operations | Legal typed constructors, exact paired result and bounded work; no scalar-to-data injection. |
| Pointwise multiplication and kernel save | Actual source stage executions, frames and typed whole-bank operations; affine data and statically prepared kernel tapes retain their proper types. |
| Binary pair and full binary stage | Physical bank → physical bank, with actual source execution/frame agreement; packing, butterfly and restoration are charged, totaling `420PQ+44 ≤ 17(25PQ+6)`. |
| Working headers and CRT tables | Closed `n`-only producer: genuine prime selection, retained prime tape, radices, weights, and both physical permutations. Exact selected/source values, charged work and polynomial peak. |
| Root preparation | Closed `n → D` typed program, exact actual master order, validity, work at most six times source preparation and peak at most `(n+2)^12`; no prime oracle or supplied working length. |
| Scalar powers and root extraction | Closed binary powering, one recursive halving call, charged exponent division, and canonical divisor roots; no additional root provision. |
| Outer scalar preparation | Original `n`, master root and input → computed working length, chirps, padded input/kernel, normalization and five C constants. Exact individual source-layout contracts, charged work and polynomial peak. |
| Combined initial entry | `DFTModelInitialPreparation.program` packages headers, CRT permutations, C constants and outer operands from those original inputs. All repeated producer work is charged, and `DFTModelInitialPreparationBounds` proves total work `O(n)`. The recursive cache forest is not included. |
| Prepared powers | Closed producer from a length and prepared root, exact powers, work at most `200N+25` and peak at most `N+2`; not the whole cache forest. |
| Residual addresses | Raw directions → charged mask/pivot/basis, one XOR table, geometric native/spectator addresses, gather/scatter and word bounds. The recursive child-call join remains open. |
| Recursive batching | Generic batching for supplied child code, with explicit child validity/peak bounds; gathering and flattening are charged. The actual recursive body and emitters remain open. |
| Recursive scalar record | Exact paired result of the real scalar source record, including source/zero-source executions and frames, with constant-factor work and bounded peak. |
| Recursive binary loop | Actual finite loop syntax, validity and work; each physical binary stage matches actual/zero-source runs. Whole-loop tensor semantics, peak and the recursive body join remain open. |
| Recursive exchange record | Charged raw-record decoding and chronological pair loop, with exact actual/zero-source executions, flags, frames and physical output, work at most `(20R+10)` times source ticks and peak at most `B`. The record printer/dispatcher remains open. |
| Recursive Y row | Raw direction bits → one shared XOR table → one whole paired-bank movement, with actual/zero-source round executions and exact paired output. Work is at most `16(R+1)` times the source round allowance, peak at most `4B+2`; the complete record header/row loop remains open. |
| Global diagonal event | Charged lane/pool record reads → one tensor-coefficient descent → complete role-bank scaling. Actual diagonal source execution and paired scaling lemmas; the calendar/cache producer and whole clock remain open. |
| Input-independent typed billing | For every typed program, changing homogeneous input data preserves work, validity and integer peak when prepared scalars, natural words and array shapes are fixed. The DFT solver's uniform work bound needs no extra compiler premise. |
| Cost-contract adapter | Derives OpenAI's exact `DFTProgram` and `TimeBounds` from explicit `ComputationalPremises`; no instance of those premises exists yet. |

The source DFT proof and the 51 originally vendored OpenAI files are unchanged.
Local stage theorems that accept already-encoded tapes are not being counted as
proofs that the outer program constructs those tapes for free.
`DFTModelBinaryBaseline` additionally proves that the complete binary stage
returns the exact paired actual/zero-source outputs. The weaker `Represents`
relation alone preserves only values, flags and the zero data part of prepared
values. The complete compiler must maintain the stronger zero-source offset
identity through every stage and recursive call.

## Remaining proof, in dependency order

1. Finish the actual cache forest, including recursive/Newton kernel and
   schedule records. The working headers, CRT permutations and outer scalar
   preparation now have closed initial-input producers. That does not imply
   that every prepared cache used by the later clocks is constructed.
2. Compile the actual recursive saving body. Preserve chronological record
   order; batch only independent cells within a record. One recursive invocation
   must return both channels. Two recursive calls for offset and data would
   change the recurrence and can destroy the saving.
3. Compile the synchronized global clock, including matching movement,
   direction/basis tables, complete role batches and prepared diagonal factors.
   Table production and restoration of physical bank layouts must be charged;
   residual address/block word bounds must also be established.
4. Assemble the actual outer stages: preparation, kernel transform/save, input
   transform, pointwise product, inverse transform and final chirp/output.
5. Prove `DFTModelCost.ComputationalPremises` for those concrete closed `order`
   and `solve` programs. This supplies validity, polynomial word bounds, exact
   outputs, and total
   `order.work + 1 + solve.work ≤ C * sourceTicks + C * (n + 1)` for fixed `C`.
   Uniform solver billing is already a universal typed-program theorem.
   Only then apply `DFTModelCost.contract` and certify the whole translation.

Dense copying after each mutable source store is insufficient: the existing
checked implementation costs linearly in tape capacity per update. Copying the
source's virtual address slabs would be worse still. The intended construction
uses compact banks, fresh whole-layer arrays and disjoint child batches.
Likewise, scanning address bits for every element can introduce a logarithmic
factor. Residual and CRT tables need explicit amortized preparation bounds.

## Reproduction and trust boundary

With the pinned dependencies and certified project artifacts installed:

```sh
python3 scripts/verify-dft-model-components.py
```

The verifier freshly builds every `DFTModel*.lean` module in dependency order,
at ordinary limits, and checks the axiom closure of all declarations defined in
those modules, including private and generated declarations. It pins the prior
DFT and model-comparison receipts, verifies their reused source/artifact hashes,
and rechecks their hashes before and after the run. Fresh components are built
in a separate artifact directory with no fallback to old component artifacts;
their hashes are pinned before the declaration audit and rechecked afterward.
Optional split server/private and IR artifacts, including artifacts at the
actual isolated import paths, are snapshotted and checked before and after;
previously absent parts must remain absent. Reused main artifacts have the
prior certificates' hashes; optional parts retain the explicit installed-cache
trust boundary recorded in the new receipt.
The inherited DFT
cone retains its seven recorded historical limit exceptions; this is not a
claim that every inherited proof used default limits.

The resulting `verification/dft-model-components.json` deliberately records
`compiler_closed: false`. A passing component audit is not a passing compiler
certificate or an executed enormous saving instance. OpenAI's full `Main`
has separately passed the [unchanged upstream reproduction](upstream-dft-reproduction.md);
that independent result does not discharge our compiler premises.
