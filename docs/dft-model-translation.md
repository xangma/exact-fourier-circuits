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
| Fixed seed and unit records | Fixed finite typed programs construct the exact nested `scheduleRecords q` tapes and the unit record from runtime `(q, role)`. Every runtime field copy and literal lookup is charged; work depends only on the fixed payload. The enormous payload is handled symbolically. Input word bounds remain a caller obligation; this is not the global cache forest. |
| Actual recursive entry and record printers | Raw entry registers → actual stack allocation or retained child stack, geometry and physical seed/unit printing, in both real source runs. `DFTModelSavingNativeNodePair.paired` returns the genuine printed records, unit pointer metadata and unchanged complete paired input bank. The combined 20-module audit, including padding-role adapters, checked 259 declaration closures at default limits. The large body and root are joined by the closed source/billing component below. |
| Odd-axis preparation and compact banks | A closed caller from `(n, master root)` extracts all odd roots and produces Newton `H`, scale, inverse `H`, diagonal/inverse diagonal, and reciprocal-series `G` coefficients. A charged adapter constructs the exact original five-lane cache layout and proves its lane/address provenance against original retained source data. No produced root or coefficient table is supplied. The all-axis spectrum and synchronized calendar producers are now checked separately; their physical cache/global-clock assembly remains open. |
| Rectangle kernels and spectrum banks | Runtime rectangle metadata and the original master root → charged root extraction, Newton/`G` production, all six original displacement kernels, root powers and six spectra. The exact original seven-block shared bank is derived without a supplied kernel or spectrum table. Local work is quadratic in the axis width, plus charged root extraction, when the actual convolution length is at most eight times that width. The closed spectrum forest performs the actual traversal once and constructs every genuine rectangle bank, retaining its node directory. A closed all-axis caller derives the selected radices and master order, includes the final binary axis, retains the actual root rows, and charges every forest and repeated root-production call. Its work bound is the explicit sum of those axis budgets and its peak is at most `(n+2)^24`. Matching factors and clock storage remain separate obligations. |
| Balanced descriptor traversal | Closed runtime width/offset → the source algorithm's actual selected descriptors, preorder node directory and complete rectangle tape, including zero/small widths. Charged search and traversal have polynomial work and peak bounds. The kernel audit is supplemented by exact serialized-program cases at the first split threshold and recursive splits, with rejected mutants. No input tree or supplied plan is assumed. |
| Direct leaf records | Closed runtime width/offset/coefficient-base → the actual traversal plus forward and reversed-transposed direct-leaf record tapes. Zero/one widths and empty split nodes are covered, and every address and copy is charged. The records reference scalar coefficient addresses; this packet does not construct their scalar banks or matching factors. |
| Balanced cache calendar | Closed runtime width/offset/start → the native synchronized subtree duration and exact nine-field event tape. Both children start together; parent rectangles begin after the maximum child duration. Value, unconditional validity and polynomial work/peak pass the isolated default-limit audit (15 fresh modules, 423 standard-axiom declaration closures). Exact serialized-program cases include unequal child durations and rejected timing mutants. Scalar factors and storage assembly remain separate. |
| Residual addresses and paired batches | Raw directions → charged mask/pivot/basis, one XOR table, geometric native/spectator addresses, gather/scatter and word bounds. The concrete residual body invokes one complete paired child per group and transports its returned flags. Additive source wrappers preserve the scanner's actual least-pivot fact and the group loop's exact returned Scalars. The complete oriented opcode-zero record now joins actual least-pivot gathering, every direction and group, restoration and both exact returned banks. Its local source contract retains the smaller-child induction hypothesis. The closed positive-depth strong induction now supplies those actual paired children without a caller callback. |
| Recursive padding record | Actual opcode-five decoding, charged fresh unit printing, all ascending roles and all nested directions return the complete actual/zero-source banks, flags and numerical padding action. The source footprint includes the patched unit fields and four mode cells; it is proved explicitly. Actual-tick role, loop and full-record billing pay fresh unit printing with the same child cost factor. The closed positive-depth induction discharges the local record contracts’ smaller-child premise. |
| Closed recursive syntax and validity | `DFTModelSavingProgram.program` is one closed upstream program: it computes the split, prints seed/unit tapes, dispatches records chronologically, recursively batches residual groups and executes the spectator suffix. `DFTModelSavingValidity.program_valid` covers all internally executed descendants without a child-validity oracle. The self-call and fuel lemmas preserve the entire tagged tape and account for actual work. |
| Closed recursive source and billing | `DFTModelSavingNativeBilledChildInduction.execution` constructs both genuine source runs at every positive depth and discharges the local smaller-child premises. `DFTModelSavingNativeRoot.execution` joins actual root allocation, printing, the whole schedule, suffix and charged halt for every exponent. It returns the exact complete paired tape, numerical physical transform and memory frames, with typed work at most one fixed `K` times those same actual source ticks. Matched initialized entry states, startup constants and ordinary source word/space conditions remain caller obligations. The recursive packet passed 39 fresh default builds and a 548-declaration standard-axiom audit; its root extension separately passed four fresh builds and 52 declaration closures. These overlapping packet counts are not an aggregate certificate. `DFTModelSavingNativeRootCompare` relates this bound to any supplied terminated source run by exact tick determinism. The closed polynomial peak theorem is described below. |
| Stream shape and flags | The actual dispatcher and stream preserve the node parameters and complete bank length for arbitrary records and child handlers. Boolean dependency flags are preserved under Boolean output of actual children. These invariants allow arbitrary flag patterns; numerical matrix equality is never used to assert canonical tags. |
| Recursive scalar and marker records | Runtime scalar headers are decoded before one whole-bank shear. Both real source runs, frames, cursors, exact paired output, constant-factor primitive work and bounded peak are checked. Additional full-saving-loop adapters include header dispatch and return, preserve parent metadata, and identify the exact whole paired bank for scalar records and both identity markers. The chronological source fold is joined into the closed positive-depth source and work induction. |
| Recursive binary base and spectator suffix | Complete tensor-base and suffix programs match genuine actual/zero-source binary runs, including flags, offsets, frames, constants, cursors, validity, work and peak. The actual saving-program small entry, allocation and terminal branch are joined to the exact closed compiler output. The suffix constructs its startup stride by charged doublings. Zero base length and empty suffix are formal endpoints; the large positive-depth saving-body source and work induction are now joined. |
| Recursive exchange record | Charged raw-record decoding and chronological pair loop, with exact actual/zero-source executions, flags, frames and physical output. A full saving-loop adapter now includes header dispatch and return, exact paired dispatch output and retained parent metadata; work is at most `(20W+81)` times full source ticks and peak at most `B`. The chronological whole-body fold is joined into the closed positive-depth source and work induction. |
| Recursive Y record | Raw record headers and inline directions feed the chronological row loop and both actual197 executions. A full saving-loop adapter joins header dispatch, restoration and return, with exact paired dispatch output, frames, cursors, constants and parent metadata. Work is at most `(32(W+1)+49)` times full source runtime, peak at most `4B+2`. The chronological whole-body fold is joined into the closed positive-depth source and work induction. |
| Global diagonal event | Charged lane/pool record reads → one tensor-coefficient descent → complete role-bank scaling. `DFTModelGlobalClockPairedEvent.actual_execution` constructs both actual131 source witnesses and proves exact paired outputs of one typed run, with work at most 200 times source ticks and peak at most `B`. Matched entry states, raw factor pools and paired original data remain entry conditions; global cache provenance and the whole clock remain open. |
| Input-independent typed billing | For every typed program, changing homogeneous input data preserves work, validity and integer peak when prepared scalars, natural words and array shapes are fixed. The DFT solver's uniform work bound needs no extra compiler premise. |
| Recursive local billing | Charged dispatcher, residual, padding and leaf bounds count each child work term once. Billed residual wrappers retain actual child durations and bound typed work against those same source ticks, with one fixed factor. Padding billing and the closed positive-depth source/work induction are checked. The same fixed factor is retained across every recursive depth; root packaging has passed its isolated audit. A source runtime upper bound alone cannot supply this comparison. |
| Closed recursive peak | `DFTModelSavingPeakClosed.polynomial_peak` bounds the actual closed saving AST by `C*(2^k+1)^2` for one fixed `C`, arbitrary prepared complex parameter and full-width Boolean-tagged bank. Seed printing, suffix, threshold and recursion-fuel charges are included. The internal induction bounds fuel explicitly; the exported program theorem supplies its actual fuel internally and requires no child, action, cache or peak callback. This is the typed RAM's integer/tape peak, not a measured GPU memory claim. |
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

1. Finish the actual cache forest and clock storage. The working headers, CRT
   permutations, outer scalars, seed/unit records and odd-axis Newton/`G` banks
   now have closed producers. The exact odd compact lanes also have a charged
   adapter. Closed rectangle kernels and shared spectrum banks are checked.
   The balanced descriptor traversal and full rectangle spectrum forest are
   checked, including a closed all-axis spectrum caller. Direct-leaf record
   production is checked; scalar coefficient banks, matching factors and complete
   storage chronology must still be joined. The exact synchronized calendar
   producer has passed its fresh isolated audit and serialized-program timing controls.
2. Integrate the checked recursive saving body with the global clock. Preserve chronological record
   order; batch only independent cells within a record. One recursive invocation
   must return both channels. Two recursive calls for offset and data would
   change the recurrence and can destroy the saving. The closed syntax and
   validity are checked. Full residual and padding records now retain real
   returned dependency flags and the native scanner's actual least-pivot choice.
   The closed positive-depth source and cost inductions discharge their
   smaller-child hypotheses, preserving actual child durations and returned
   flags. The root entry/halting join and closed polynomial peak bound are checked.
   The combined verifier below rebuilds these components together. `DFTModelSavingNativeRootCompare` relates
   billing to any supplied terminated execution by deterministic equality of
   its actual instruction count. Numerical
   matrix identities alone do not establish the flag identities, and an upper
   runtime budget alone does not establish a bound against `sourceTicks`.
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
