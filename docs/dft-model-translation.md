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
| Direct leaf records and coefficients | Closed width/offset/coefficient-base producers construct the actual forward and reversed-transposed records. Charged inverse-`H` production at the root and inverse root supplies their exact coefficient pairs, including native compact-lane address provenance. The forest caller follows actual node order and retains empty split nodes. A separate forward chronology producer adds genuine timestamps and shear/scale kinds. Transposed records are a prepared orientation, not an additional global event family. Matching selection and physical storage assembly remain open. |
| Balanced cache calendar | Closed runtime width/offset/start → the native synchronized subtree duration and exact nine-field event tape. Both children start together; parent rectangles begin after the maximum child duration. Value, unconditional validity and polynomial work/peak pass the isolated default-limit audit (15 fresh modules, 423 standard-axiom declaration closures). Exact serialized-program cases include unequal child durations and rejected timing mutants. Scalar factors and storage assembly remain separate. |
| Rectangle replay chronology | Actual seven-field rectangle row and start → charged exponent/height calculation, all six native replay phases, exact ordered slot tape, timestamps, shear kind and duration. No supplied exponent, plan, duration or schedule is assumed. Endpoint selection and scalar banks remain separate. |
| Matching factors | Runtime radix, actual pairs-first full permutation, coefficient pairs and produced `I`/`aInv` → the native lane-major `9r` factor bank, including singleton factors, source scatter and inverse negation. Forward/inverse/broadcast source selections are checked. `DFTModelCacheMatchingProduced.program` joins the proper seven-block paired spectra/decoder, native matching permutation, canonical C constants and factor writer, invoking each once with exact additional work `73`. It takes the same raw selected rows and canonical master root throughout; endpoint matching/range, coefficient labels and rectangle/address geometry remain explicit premises. |
| Raw topology and DAG depths | Raw rectangle extents `(a,e)` generate their own exponent, finite registers, actual native allocation budget and fixed fuel, execute the original CrossTopology271 instruction list and read back all five topology fields. The charged depth recurrence then computes the exact original typed depths, bounded by `8K+6`. Allocation uses the actual native `B+1`; coarse polynomial envelopes are proof bounds. Topology work is at most `10^24*(a+e+1)^8` and peak at most `10^14*(a+e+1)^4`; depth work is charged separately. No initialized state, topology, depth bank or fuel is supplied. |
| Stable depth buckets | Charged level/gate scans reproduce the native stable order and offset directory. Ties retain gate chronology; level zero is retained and labels above the gate count are omitted. `DFTModelCacheBucketRaw.program` starts from raw `(a,e)`, calls topology, depth and stable bucketing once each, and retains the genuine `(K,count,flat5)` output. Its exact-output theorem requires no supplied topology, depth, order or source witness. It exports the genuine topology execution witness and equality to native canonical bucket values; the separate physical Bucket24 execution adapter retains its entry conditions. The complete raw producer has work at most `10^25*(a+e+1)^8` and peak at most `10^15*(a+e+1)^4`; the dense bucket printer's gate-count bound is quartic. |
| Height rows and native coloring | `DFTModelCacheHeightRaw.program` generates topology/depth/buckets internally and selects the exact physical Row3 occurrences at a requested height, retaining duplicates and coefficient addresses. Its work is at most the raw-bucket budget plus `1200*(2G+1)^2+25`, independent of physical bases and requested height; peak retains ordinary address bounds. Its source adapter matches the actual per-height132 program under ordinary source-bank, header and address conditions. A separate closed `DFTModelCacheColor.program` initializes finite storage, runs the original native51 greedy program with computed fuel, and reads its exact colors. Degree six implies eleven proper matching layers; exhausted palettes retain sentinel11 outside that condition. Coloring work is locally cubic and peak quadratic in endpoint bound plus row count. Charged endpoint rebasing, stable color selection, the full186 traversal and physical cache assembly remain separate joins. |
| Conjugate spectra and physical coefficients | A closed producer runs the original seven-block spectrum algorithm at the canonical root and its charged inverse, then zips the two actual banks. Work is exactly twice the original spectrum work plus `133N+20`. Signed physical-address decoding computes six replay constants, preserves row order and negates both pair components for negative addresses. Native inverse routing, including width-one aliases, is proved on the forward-leaf coefficient domain. Raw selected physical rows remain an input; a prepared conjugate bank or coefficient-pair table is not supplied. |
| Integer metadata compiler | `DFTModelCacheNatControl` and `DFTModelCacheNatDispatch` compile a fixed finite instruction list with charged PC selection, fuel and dense finite updates. Genuine bounded native executions imply validity, exact represented Nat state and work/peak bounds under explicit finite-address safety. Generic invalid paths use scalar inverse-of-zero guards; successful metadata paths avoid them. This is preparation machinery, not a constant-cost mutable heap for the main input bank. |
| Concrete matching-table client | `DFTModelCacheMatchingNat.execution` starts from radix and selected raw endpoint rows, charges initialization, computes fuel, executes the actual native Matching55 program and reads back pairs followed by ascending unused indices. It proves work at most `3000000*(r+1)^2` and peak at most `4000*(r+1)`, including radix zero. Endpoint provenance, matching and range are explicit obligations; no initialized state, permutation, fuel or safety trajectory is supplied. The third row word is ignored and charged zero projection replaces it. |
| Mixed-program Nat projection | `DFTModelCacheNatProjection.bounded_source` preserves exact ticks and Nat state of genuine successful mixed runs without length instructions. Scalar instructions become charged PC advances; original scalar/output/root fields are retained. Its typed adapter has explicit initialization, finite-address safety and charged fuel obligations. It does not compile the scalar effects or instantiate the full rectangle printer. |
| Cache asymptotics | All-axis spectrum and calendar budgets and actual work are `o(n)`. The sum of existing initial-preparation, all-axis and calendar budgets is `O(n)`. The actual raw topology/depth/bucket work also sums to `o(n)` for explicitly polynomially many clients whose extents fit the genuine selected radices. Client counts and extents remain premises; no composed whole-cache bound is claimed. |
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
| Sector gather, scatter and closed child | Genuine native sector gather/reverse-scatter preserve complete paired Scalars and tags. Scatter retains a compact patch with the original bank; its reader has constant charged work. `DFTModelSectorTranspose.saving` gathers the whole child bank and enters the actual closed saving program once, retaining context, with exact billing, unconditional validity and polynomial peak. Generating the runtime sector directory, joining the actual native child entry, and materializing the final whole bank remain open. |
| Sector direct map | A closed producer takes runtime volume and an ordered, fitted sector directory, constructs all sparse markers, packed chunks, lookup tables and binary carries internally, then emits the direct map. Under the explicit directory geometry and count bound, actual work is at most `2000*(V+1)` and peak at most `6*(V+1)`. A reader uses at most100 work to select the correct role-major compact child cell or retained spectator cell. The native adapter identifies genuine BatchCell readback; that readback is not a charged directory producer. Runtime directory generation, child patches and one final whole-bank materialization remain separate. |
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

1. Join the actual cache factory and physical storage. Compose generated height
   rows with rebased coloring, stable matching selection and borrowed cells from original runtime
   inputs. Existing producers now supply raw topology and depths, stable
   buckets, roots,
   spectra, direct-leaf coefficients/chronology, rectangle replay slots,
   paired spectra, signed coefficient decoding, matching permutations and
   factors. Their combined ABI, stored-source
   provenance and total preparation budget still need one coherent program.
   Concrete mixed-printer metadata clients must discharge static length/operand
   restrictions, charged finite initialization, safety and justified fuel.
2. Generate the runtime sector directory for the checked direct-map producer and join the checked sector call to
   its actual native child entry. Keep one paired recursive call and preserve
   its returned flags. Use constant-work patch lookup and one final whole-bank
   materialization. The closed recursive source/billing and polynomial peak
   theorems supply the child; a supplied execution budget alone does not prove
   billing against its actual `sourceTicks`.
3. Assemble the complete synchronized global clock, including matching
   movement, direction/basis tables, role batches and diagonal factors.
   Prove charged layout restoration, source correspondence, work and storage
   for the same concrete execution.
4. Assemble the actual outer stages: preparation, kernel transform/save, input
   transform, pointwise product, inverse transform and final chirp/output.
5. Prove `DFTModelCost.ComputationalPremises` for those concrete closed `order`
   and `solve` programs. This supplies validity, polynomial word bounds, exact
   outputs, and total
   `order.work + 1 + solve.work ≤ C * sourceTicks + C * (n + 1)` for fixed `C`.
   Uniform solver billing is already a universal typed-program theorem.
   Only then apply `DFTModelCost.contract` and certify the whole translation.

Dense copying after each main-bank store costs linearly in tape capacity and
does not preserve the runtime saving. Polynomial copying is acceptable inside
the small preparation clients only with their explicit aggregate asymptotic
bound. The global construction uses compact patches, a direct sector map and
disjoint child batches. Copying virtual address slabs, searching all patches
per read, or scanning address bits per element can introduce unwanted factors;
table generation and final materialization must be charged.

Calendar event tags describe whole-leaf/whole-rectangle macros. They cannot be
copied into the native shear/scale/recursive event-kind field. Rectangle inverse
replay also negates coefficients; conjugation is a separate scalar operation.

## Reproduction and trust boundary

With the pinned dependencies and certified project artifacts installed:

```sh
python3 scripts/verify-dft-model-components.py --jobs 4
```

The verifier freshly builds every `DFTModel*.lean` module in dependency order,
running only dependency-ready modules concurrently (`--jobs` defaults to one),
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
`python3 scripts/test-dft-model-builds.py` checks dependency ordering, worker
limits, failures and repeated stop requests against actual child processes.
The inherited DFT
cone retains its seven recorded historical limit exceptions; this is not a
claim that every inherited proof used default limits.

The resulting `verification/dft-model-components.json` deliberately records
`compiler_closed: false`. A passing component audit is not a passing compiler
certificate or an executed enormous saving instance. OpenAI's full `Main`
has separately passed the [unchanged upstream reproduction](upstream-dft-reproduction.md);
that independent result does not discharge our compiler premises.
