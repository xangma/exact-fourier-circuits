# Fourier circuit investigation plan

We are investigating the result described in `math/lean/docs/130.md`: why its
exact circuit saving is valid, how an explicit saving circuit realizes it,
and whether that construction remains accurate in floating-point arithmetic.
The deliverables are a checked constructive argument and a reproducible
numerical assessment, with their remaining limitations stated explicitly.

Lean's theorem concerns exact mathematical operations and a particular cost
model. CUDA tests concrete finite-precision implementations. Our specialized
kernel is `C = [[(1+i)/2,(1-i)/2],[(1-i)/2,(1+i)/2]]`; its tensor-power saving
seed is one part of the broader Fourier argument. We must connect those parts
explicitly before claiming an executable faster DFT.

1. **Establish the baseline — completed.**
   The original theorem checks with pinned Lean/Mathlib and 51 unchanged
   upstream modules. The exact Python engine, lazy construction, and bounded
   projections are implemented. All 73 Python tests and eleven new Lean
   projection/network identities pass. Forty-eight CUDA cases on len compared
   compiled three-C shears with direct shears, in FP32/FP64 with FMA on/off.
   Worst relative errors were `1.59e-6` and `2.06e-15`; compiled shears produced
   roughly 2.3 times the stress-input error. Raw outputs were independently
   checked. See the [experiment report](docs/projected-stability.md).

2. **Write the precise proof contract — completed.**
   Identify the exact theorem statements, circuit semantics, allowed free
   operations, charged calls, tensor coordinate convention, and parameter
   assumptions. Map the paper's explicit construction and Python objects to
   those definitions. Include the tensor-power-to-Fourier bridge and distinguish
   what is already proved from what the implementation still assumes.
   **Deliverable:** a dependency map and an explicit list of missing lemmas.
   **Completion:** every claimed output identity and saving count has a named
   statement and specified hypotheses.
   See [proof contract](docs/proof-contract.md). Its dependency map records the
   scalar/call-cost distinction, coordinate transport, admissible parameter
   range and missing action/count proofs. The checked conditional q=2 bridge
   can reuse the upstream Fourier transfer once a concrete word is supplied.

3. **Prove the specific binary frame construction — in progress.**
   Formalize the incidence/complement identities, residual subspaces, signed
   weights, and orthonormal bases over GF(2). Instantiate the existing general
   dirty-auxiliary and frame-telescoping proofs with this construction. Prove
   the terminal correction and arbitrary auxiliary-data behavior.
   **Deliverable:** Lean modules proving the actual network's exact action.
   **Completion:** the proofs cover the required parameter family, rather than
   only sampled inputs or generic algebra with an unproved frame hypothesis.
   Checked components now include triple-incidence cancellation, successful
   triple/pair pivots and actual complement bases, tensor weights, signed Walsh
   operators and terminal correction, all eleven symbolic residual table shapes,
   and the three-axis scalar network with the actual stage-two reversal.
   Actual per-invocation frame labels, concrete consecutive-stage coordinate
   identities, column lifts and a literal free terminal correction now compile.
   Whole-network chronology and residual totals still require assembly; generic table hypotheses alone do not finish this step.

4. **Connect the construction to a saving word and its cost — in progress.**
   Translate directional layers, compiled shears, padding, permutations and
   scalings into Lean's chronological word model. Prove the coordinate
   identification, output tensor identity, and forward-call count. Derive the
   strict saving inequality for an explicit valid parameter choice. Keep the
   construction symbolic: even the current smaller saving choice has billions
   of address bits and cannot be materialized.
   **Deliverable:** a kernel-checked constructive finite-win statement matching
   the Python budget. **Completion:** correct action and strict saving are
   proved together, without `sorry`, custom axioms, or native decision shortcuts.
   Literal three-C shears, directional layers, signed frame words, pointwise
   role lifts and the ordinary tensor compiler now have exact action/count
   proofs. Actual neighbor, edge and physical role cardinalities are checked.
   The h=100 arithmetic saving is proved symbolically, but its connection to
   the complete saving word remains open.

5. **Investigate numerical stability alongside the proof work.**
   First isolate the three-C shear: measure target error and failure to restore
   its source on cancellation-sensitive and wide-range inputs. Use exact or
   higher-precision references and compare arithmetic orderings and equivalent
   scaling choices. Then vary projection maps, address width and construction
   height where resource sizing permits; otherwise test bounded stage blocks.
   Track stage errors, small-output accuracy, intermediate growth, norm drift
   and nonfinite events. Set the accuracy criterion before judging a variant.
   **Deliverable:** retained counterexamples or an error-growth characterization,
   with controls that identify the responsible operations. **Completion:** we
   can explain the observed scaling with precision and construction size;
   passing small projections alone does not establish full-width stability.

6. **Assess what the result means for an actual Fourier implementation.**
   Once the exact bridge and numerical behavior are understood, identify any
   feasible DFT instance and compare its accuracy, memory and runtime with an
   ordinary FFT under equivalent conditions. If the saving construction remains
   infeasible, document its symbolic saving and numerical limits instead.
   **Deliverable:** a supported conclusion about exact validity, stability and
   practical usefulness, each backed by its own evidence.

The immediate next action is to finish the full frame schedule, stage boundary
transport and residual dimension total, then assemble and count the same literal
saving word. Numerical work can proceed independently once its test contract is
fixed. The isolated-shear experiment is now complete: all 9,360 raw CUDA cases were
independently verified. Normal finite inputs expose complete source loss in
the compiled shear, reproduced by chronological CPU rounding traces; scaling
controls do not repair it. See [numerical report](docs/isolated-shear-stability.md).
This establishes a concrete implementation limit; a full-width stability
characterization remains out of reach for the enormous saving seed.

Every experiment will have explicit memory/work limits, a deadline, input and
source hashes, retained logs and a stop command. Remote jobs will preserve
existing services. Each milestone will report implementation, exact checks,
Lean verification and observed CUDA results separately. A failed check will
trigger reproduction and competing-hypothesis tests before another patch.
