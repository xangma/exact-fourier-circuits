# Machine-model comparison

The unchanged models are **not equivalent under their declared DFT data
interface**. This is a Lean theorem, not an inference from their different syntax.
The proof compares our `UniformMachine` with the exact, unmodified upstream
`RAM` and `Goal` definitions at OpenAI revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## The formal counterexample

Every upstream typed program preserves zero data. Natural words and prepared
scalars, including the supplied root, are unrestricted. Non-scalar input data
are zero, and all non-scalar output data must remain zero. The proof covers every
`Atom` and `Code` constructor, including arrays, loops, internal handlers and
bounded recursion, in both product modes. It does not assume validity. Reading
outside an output tape also returns the prescribed zero default.

Our machine permits adding a prepared constant to input data. The literal
seven-instruction program in
[ModelEquivalenceCounterexample.lean](../lean/ModelEquivalenceCounterexample.lean)
computes `z + 1` at length one. Its checked execution starts from `initial`,
halts after seven charged instructions, satisfies word bound `6` at every
state, and requests exactly the canonical root of order one. At zero input,
its output is one.

[ModelEquivalence.lean](../lean/ModelEquivalence.lean) combines these facts:

- `upstream_zero_output`: every upstream transform program returns zero data on
  zero input, for every length and every supplied prepared scalar.
- `no_affine_program`: no upstream transform program with the declared input
  interface computes this affine function.
- `models_not_equivalent`: the actual bounded, single-root execution is paired
  with the impossibility result.
- `no_interface_preserving_compiler`: no compiler for all our programs can
  preserve even this restricted family of successful executions using that same
  input/output convention.

Thus our entire language is **affine-capable**. Its dependence flag prevents
data-data multiplication; it does not enforce homogeneous linearity. Historical
comments saying that data computations “remain linear” must be understood with
this qualification. Neither the machine definition nor its existing proof
receipt was edited to conceal the difference.

## What this does and does not establish

The negative theorem fixes the natural data interface: the length, one prepared
root, the original input tape, and direct output values. It does **not** rule out
an encoding that supplies an additional constant-one data channel, a suitable
extension of the upstream language, or a compiler for a homogeneous fragment of
ours. Such a translation would need its own construction and cost proof.

This counterexample does not invalidate either DFT theorem. The DFT is
homogeneous linear and sends zero to zero. Our proved algorithm is constrained
by its exact DFT correctness theorem despite the broader language allowing
affine programs. Equivalence of the two complete languages is a stronger claim
than either algorithm needs. A cost-preserving translation of the actual DFT
algorithms or an appropriate common fragment remains unproved.

The follow-on [actual DFT translation](dft-model-translation.md) uses separate
prepared-offset and homogeneous-data channels, with a matching zero-input
execution. Its component proofs do not yet close the whole-program bridge.

## Positive primitive translations

The investigation also checks concrete translations rather than assuming a
compiler:

| Source and target | Checked result |
|---|---|
| Our partial natural operations → upstream `Code` | `ModelEquivalenceNat.natCode_reflects` preserves results and represents failure by `Bill.valid`. Division and modulo by zero are guarded explicitly. Accepted work is at most 3; all paths at most 9. |
| Upstream total natural operations → our instructions | `ModelEquivalenceScalarLowering.nat_compile_correct` handles all six operations, including zero denominators and comparison, in at most 5 instructions including halt. |
| Upstream scalar primitives → our instructions | `ModelEquivalenceScalarLowering.Primitive.compile_correct` proves typed value agreement, actual bounded execution, storage/register frames and at most 3 instructions including halt. |

These are primitive fragments, not a full array/control-flow compiler. Terminal
halt macros have not been composed into arbitrary translated programs.

There is a separate memory-cost obstacle. The actual typed `Code` update in
`ModelEquivalenceInterpreter` reproduces `Tape.set` by constructing a fresh
tape. Its in-range work is exactly `35 * length + 2`; our mutable store takes
one instruction. `update_no_uniform_constant` rules out constant overhead for
**this implementation**. It is not a lower bound against every possible memory
representation. The finite Nat-cell encoding likewise assumes an encoded
initial heap; it does not claim to construct a complete interpreter.

## Reproduce and trust boundary

With the project's pinned Lean/Mathlib dependencies installed:

```sh
python3 scripts/verify-model-comparison.py
```

The driver freshly compiles the 12 relevant project modules at default limits,
checks the exact negative theorem type, and audits all declarations by their
defining module, including private and generated declarations. It verifies the
51 original vendored source hashes and the separately pinned upstream definition
copies. Cached external artifacts are checked against the existing certified
final-DFT receipt; Lean and Mathlib are not rebuilt from first principles.

The new [receipt](../verification/model-comparison.json) certifies this bounded
comparison. It does not rebuild OpenAI's full `FourierTransform.Main`, provide a
whole-language compiler, or replace the separate final-DFT verification receipt.
No astronomical saving instance is evaluated.
