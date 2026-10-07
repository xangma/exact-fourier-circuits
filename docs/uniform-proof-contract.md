# Contract for the all-length uniform algorithm

The target is the main theorem of [An explicit power saving for the exact
discrete Fourier transform](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf):
one deterministic algorithm computes the standard, unnormalized DFT at every
positive length, in `O(n*(log n)^theta*(log log n)^(4-theta))` time. Preparation,
schedule generation and memory/index work are charged; the supplied specified
root has order less than `1024*n^3`, and integer words have `O(log(n+2))` bits.

The closed subsequential `ExplicitSeed.main` remains the previous result.
It does not prove this target. No all-length algorithm theorem is proved yet.

## Operational statement

[UniformMachine.lean](../lean/UniformMachine.lean) defines a finite instruction
alphabet and `UniformDFTStatement theta`. A single program is quantified before
the input length. It explicitly loads inputs, writes/reads heaps, prepares
scalars, obtains one root, and emits outputs. Uninitialized heap reads fail.
The instruction count includes preparation and traversal; there is no opaque
DFT, circuit-generator or whole-array primitive. Only natural-number branches
are available. Prepared divisions require nonzero denominators, and products
of two input-dependent values are rejected. Polynomial bounds on all
intermediate integer values and addresses enforce the logarithmic-word model.
The root order is fixed for the length before quantifying the input vector.

The interpreter uses mathematical complex values to specify exact operations.
Its noncomputable semantic evaluation does not supply an arbitrary function
instruction or a complex constant to the finite program. Partial division's
nonzero precondition is a semantic validity condition, not a complex test
instruction. Rational literals belong to the fixed program.

## Dependencies and status

| Obligation | Evidence and remaining link |
|---|---|
| Exact exponent | `UniformExponent` proves the paper's actual lambda/theta constants, `0<theta<1`, and `theta<1-2*10^-13`. Its recurrence estimates retain explicit recurrence premises |
| Complete recursive batches | `UniformBatching` proves actual quotient reduction, full batches, width partition, recursion depth and master-root bounds. `UniformNetworkCost` defines a computable count majorant and proves its recurrence and critical bound without abstract recurrence premises. An operational network must still realize the reserved charges |
| Computable working lengths | `UniformWorkingLength` selects initial odd primes and minimal binary fill, proves `2n<=L<4n`, quadratic prime bounds, coprimality and logarithmic integer-value bounds. `UniformWorkingPreparation` implements trial division, candidate scanning and binary doubling, proves the returned fields and a sublinear counted preparation cost. Its fixed RAM lowering remains |
| Canonical root extraction | `UniformRoots` proves specified roots extract to the specified smaller roots, preserving the DFT phase. `UniformPowerMachine` supplies an actual fixed twelve-instruction repeated-squaring program, bounded execution, logarithmic cost and canonical root extraction. Initial root loading and integration into the full program remain |
| Zero-free shear compiler | `UniformLocalShear` proves one six-C pattern for every coefficient, including zero. `UniformScalarPreparation` develops shared coefficient/conjugate arithmetic DAGs. `UniformDiagonal` replaces the forbidden-set scalar choice with an explicit nonzero shift. `UniformNewton` prints a computable shared `8n+3`-register DAG, certifies every division and proves its prepared Newton/Toeplitz factorization. Actual local Fourier schedules remain |
| Linear traversal and packing | `UniformTraversal` develops actual accumulator traversal, exact node/leaf counts and packing arithmetic. `UniformTraversalMachine` executes the four packing updates in nine charged instructions with bounded intermediates. The sector permutation, full DFS stack, table preparation and data movement must still be linked to the algorithm |
| Computed CRT | `UniformCRT` implements inverse digits, idempotents, address tables and the encoding/decoding bijection, proves the specified-root tensor phase and local output permutations. `UniformSelectedCRT` applies this to the actual selected factors. Charged preparation and RAM array traversal remain |
| Chirp reduction | `UniformChirp` proves the exact DFT chirp identity and successive-ratio table formulas. `UniformCyclic` proves cyclic convolution, signed support without aliasing, the positive-exponent adapter and the exact three-transform reduction. Its charged RAM implementation remains |
| Final asymptotics | `UniformAsymptotics` proves both actual axis Theta estimates, the working-cost expression's paper bound and its little-o decimal improvement. `UniformNetworkCost` also bounds the defined aggregate count, including counted working-length preparation and fixed polynomial reserves. The actual algorithm must still be proved to realize those reserves |
| Bounded-length fallback | `UniformDirectMachine` provides one literal finite program computing every positive-length standard DFT with one root and exactly `7*n^2+9*n+7` instructions. `UniformDirectBounds` proves actual bounded execution with integer/address bound `n+21`, hence `(n+2)^5`. Integration into the fast algorithm remains |
| Single program | The operational target is defined. Its local compiler, batching, CRT, padding and output procedures must be assembled and proved in that model |

## Reuse boundary

The existing local `dft_layers` result is an algebraic existence theorem. Its
dependency `RectStableAlgebra.SumLayered.diagonal` chooses a scalar outside a
finite forbidden set (`Infinite.exists_notMem_finset`), so it cannot serve as
the requested uniform local compiler. The paper supplies the constructive
replacement: printed bounded-fanout convolution DAGs, dirty replay, integer
workspace search, deterministic layering and zero-free six-C shears.
`UniformDiagonal` now proves the explicit replacement
`lambda = 1 + sum_j c_j*conj(c_j)`, with `lambda != 0` and
`c_j-lambda != 0` for every coefficient. This does not replace the existing
layer proof or supply an executable local compiler by itself.

Likewise, the original amplification theorem's existential exponent cannot
replace the exact `S/W_*` batching recurrence or prove data-movement costs.
CRT factorization identities can be reused after linking them to computed
idempotents and index tables. Standard root extraction is needed: an arbitrary
primitive root can permute the standard DFT outputs.

New components require successful Lean builds, complete registered axiom
checks and source hashes. The 51 vendored files remain unchanged. Definitions,
generic estimates and proved component identities will be reported separately
from a closed proof of `UniformDFTStatement`; no count of checked declarations
will be used as a substitute for that final proof.

Run `scripts/verify-uniform.sh` for the separate component registry. It verifies
the pins, hashes the complete local import closure before building, rejects
source changes during verification and checks every registered axiom closure.
The retained receipt explicitly states that the full uniform algorithm is
unproved. The previous closed seed theorem is rechecked as a baseline.
