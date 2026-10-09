import UniformMachine

set_option autoImplicit false

namespace ExactFourierCircuits.ModelEquivalenceCounterexample
open UniformMachine OAI.ExactFourier
noncomputable section

/-- A terminating affine map with one explicit root request. -/
def program : Program :=
  [.natLiteral 1 1, .root 2 1, .input 0 0, .scalarLiteral 1 1,
   .fieldBinary .add 0 0 1, .output 0 0, .halt]

def input (z : ℂ) : Fin 1 → ℂ := fun _ => z

def afterNat : State := writeNat initial 1 1
def afterRoot : State :=
  { writeScalar afterNat 2 ⟨zeta 1, false⟩ with rootOrders := [1] }
def afterInput (z : ℂ) : State := writeScalar afterRoot 0 ⟨z, true⟩
def afterLiteral (z : ℂ) : State := writeScalar (afterInput z) 1 ⟨1, false⟩
def afterAdd (z : ℂ) : State := writeScalar (afterLiteral z) 0 ⟨z + 1, true⟩
def result (z : ℂ) : State :=
  { next (afterAdd z) with
    outputs := Function.update (afterAdd z).outputs 0 (some (z + 1)) }

theorem program_length : program.length = 7 := rfl

theorem bounds (z : ℂ) (B : ℕ) (hB : 6 ≤ B) :
    WordBound B afterNat ∧ WordBound B afterRoot ∧
    WordBound B (afterInput z) ∧ WordBound B (afterLiteral z) ∧
    WordBound B (afterAdd z) ∧ WordBound B (result z) := by
  have hr : ∀ r : ℕ, (if r = 1 then 1 else 0) ≤ B := by
    intro r
    split_ifs <;> omega
  simp [WordBound, afterNat, afterRoot, afterInput, afterLiteral, afterAdd,
    result, initial, writeNat, writeScalar, next, Function.update_apply, hr]
  omega

/-- Every instruction, including the halt and the sole root request, is charged. -/
theorem execution (z : ℂ) (B : ℕ) (hB : 6 ≤ B) :
    BoundedExecution program 1 (input z) B initial 7 (result z) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bounds z B hB
  apply BoundedExecution.next (initial_wordBound B)
    (u := afterNat) (t := 6)
  · rfl
  apply BoundedExecution.next b1 (u := afterRoot) (t := 5)
  · simp [step, program, afterNat, afterRoot, writeNat, writeScalar, next, initial]
  apply BoundedExecution.next b2 (u := afterInput z) (t := 4)
  · simp [step, program, afterNat, afterRoot, afterInput, input,
      writeNat, writeScalar, next, initial]
  apply BoundedExecution.next b3 (u := afterLiteral z) (t := 3)
  · simp [step, program, afterNat, afterRoot, afterInput, afterLiteral,
      writeNat, writeScalar, next, initial]
  apply BoundedExecution.next b4 (u := afterAdd z) (t := 2)
  · simp [step, program, afterNat, afterRoot, afterInput, afterLiteral, afterAdd,
      evalField, writeNat, writeScalar, next, initial]
  apply BoundedExecution.next b5 (u := result z) (t := 1)
  · simp [step, program, afterNat, afterRoot, afterInput, afterLiteral, afterAdd,
      result, writeNat, writeScalar, next, initial]
  apply BoundedExecution.halt b6
  rfl

theorem output_value (z : ℂ) : (result z).outputs 0 = some (z + 1) := by
  simp [result]

theorem all_outputs (z : ℂ) (j : Fin 1) :
    (result z).outputs j.val = some (z + 1) := by
  have hj : j.val = 0 := by omega
  simpa [hj] using output_value z

theorem root_orders (z : ℂ) : (result z).rootOrders = [1] := rfl

theorem data_tag (z : ℂ) : (result z).scalarReg 0 = ⟨z + 1, true⟩ := by
  simp [result, afterAdd, writeScalar, next]

theorem final_pc (z : ℂ) : (result z).pc = 6 := rfl

theorem zero_input_output : (result 0).outputs 0 = some 1 := by
  simpa using output_value 0

theorem affine_execution (z : ℂ) (B : ℕ) (hB : 6 ≤ B) :
    ∃ s : State, BoundedExecution program 1 (input z) B initial 7 s ∧
      (∀ j : Fin 1, s.outputs j.val = some (z + 1)) ∧
      s.rootOrders = [1] ∧ s.scalarReg 0 = ⟨z + 1, true⟩ ∧ s.pc = 6 :=
  ⟨result z, execution z B hB, all_outputs z, root_orders z, data_tag z, final_pc z⟩

end
end ExactFourierCircuits.ModelEquivalenceCounterexample
