import ModelEquivalenceZeroPreservation
import ModelEquivalenceCounterexample
import ModelEquivalenceNat
import ModelEquivalenceScalarLowering
import ModelEquivalenceInterpreter
import OAI.Computability.FourierTransform.Goal

set_option autoImplicit false

/-! The unchanged models are not equivalent under their declared data interface.
Upstream typed data stay zero on zero input, even with arbitrary prepared scalars.
Our machine accepts addition of a prepared constant to data. The counterexample
below terminates, uses one canonical root, and has constant work and word bounds.
This does not refute equivalence of a smaller homogeneous DFT fragment, nor does
it refute either DFT correctness theorem. Primitive simulations are imported as
separate, strictly weaker positive results. -/
namespace ExactFourierCircuits.ModelEquivalence
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section

def dftInput (n : ℕ) (rho : ℂ) (x : Fin n → ℂ) : dftInKind.T :=
  (n, rho, (⟨n, x⟩ : Tape ℂ))

/-- Any upstream transform program returns zero at every data position on zero
input. This includes out-of-range reads, whose prescribed default is zero. -/
theorem upstream_zero_output (q : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (i : ℕ) :
    (run q (dftInput n rho (fun _ => 0))).val.look i 0 = 0 := by
  have input_zero : ModelEquivalenceZeroPreservation.ZeroData dftInKind (dftInput n rho (fun _ => 0)) :=
    ⟨True.intro, True.intro, fun _ => rfl⟩
  have output_zero := ModelEquivalenceZeroPreservation.prog_zero q _ input_zero
  exact ModelEquivalenceZeroPreservation.tape_look (fun z : ℂ => z = 0) _ i 0 output_zero rfl

/-- Natural data-interface agreement at length one. No compiler, cost bound,
validity or output-size premise is assumed, making the obstruction stronger. -/
def MatchesAffine (q : Prog false dftInKind dftOutKind) : Prop :=
  ∀ z : ℂ, (run q (dftInput 1 (root 1) (ModelEquivalenceCounterexample.input z))).val.look 0 0 = z + 1

theorem no_affine_program : ¬∃ q : Prog false dftInKind dftOutKind, MatchesAffine q := by
  rintro ⟨q, hq⟩
  have hz := upstream_zero_output q 1 (root 1) 0
  have ho := hq 0
  change (run q (dftInput 1 (root 1) (fun _ => 0))).val.look 0 0 = 0 + 1 at ho
  rw [hz, zero_add] at ho
  exact zero_ne_one ho

/-- A concrete terminating single-root machine program has no upstream program
with the same input/output observations. Thus unrestricted model equivalence
already fails before asking for preservation of operation counts or storage. -/
theorem models_not_equivalent :
    (∀ z : ℂ, ∃ s : UniformMachine.State,
      UniformMachine.BoundedExecution ModelEquivalenceCounterexample.program 1 (ModelEquivalenceCounterexample.input z) 6
        UniformMachine.initial 7 s ∧
      s.outputs 0 = some (z + 1) ∧ s.rootOrders = [1]) ∧
    ¬∃ q : Prog false dftInKind dftOutKind, MatchesAffine q := by
  refine ⟨?_, no_affine_program⟩
  intro z
  exact ⟨ModelEquivalenceCounterexample.result z, ModelEquivalenceCounterexample.execution z 6 (by omega), ModelEquivalenceCounterexample.output_value z, ModelEquivalenceCounterexample.root_orders z⟩

/-- Even this small subset of successful executions would have to be preserved
by a compiler using the same data interface and the same single supplied root. -/
def PreservesAtOne (p : UniformMachine.Program)
    (q : Prog false dftInKind dftOutKind) : Prop :=
  ∀ (z : ℂ) (ticks : ℕ) (s : UniformMachine.State),
    UniformMachine.BoundedExecution p 1 (ModelEquivalenceCounterexample.input z) 6
      UniformMachine.initial ticks s →
    s.rootOrders = [1] →
    s.outputs 0 = some ((run q (dftInput 1 (root 1)
      (ModelEquivalenceCounterexample.input z))).val.look 0 0)

theorem no_interface_preserving_compiler :
    ¬∃ compile : UniformMachine.Program → Prog false dftInKind dftOutKind,
      ∀ p, PreservesAtOne p (compile p) := by
  rintro ⟨compile, correct⟩
  apply no_affine_program
  refine ⟨compile ModelEquivalenceCounterexample.program, ?_⟩
  intro z
  have agreement := correct ModelEquivalenceCounterexample.program z 7
    (ModelEquivalenceCounterexample.result z)
    (ModelEquivalenceCounterexample.execution z 6 (by omega))
    (ModelEquivalenceCounterexample.root_orders z)
  rw [ModelEquivalenceCounterexample.output_value] at agreement
  exact (Option.some.inj agreement).symm

end
end ExactFourierCircuits.ModelEquivalence
