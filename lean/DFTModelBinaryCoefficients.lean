import DFTModelBinaryPair

set_option autoImplicit false

/-! Prepared C coefficients use only `cone`, prepared field arithmetic, and
the checked inverse of two. The existing master-root extraction of `i` remains
a separate phase; this program introduces no extra root request. -/
namespace ExactFourierCircuits.DFTModelBinaryCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier
noncomputable section

def two : Prog false sc sc :=
  .comp (.fork (.atom .cone) (.atom .cone)) (.atom (.add .scalar))
def half : Prog false sc sc := .comp two (.atom .inv)
def numerator (negative : Bool) : Prog false sc sc :=
  .comp (.fork (.atom .cone) (.atom .id))
    (if negative then .atom (.sub .scalar) else .atom (.add .scalar))
def coefficient (negative : Bool) : Prog false sc sc :=
  .comp (.fork half (numerator negative)) (.atom (.scale .scalar))
def program : Prog false sc DFTModelBinaryPair.Coefficients :=
  .fork (coefficient false) (coefficient true)

theorem coefficient_run (negative : Bool) (z : ℂ) :
    run (coefficient negative) z =
      ⟨if negative then (1-z)/2 else (1+z)/2,15,0,True⟩ := by
  cases negative <;>
    simp [coefficient,numerator,half,two,run,Code.run,Atom.run,Bill.pass,
      Bill.pay,Bill.one,div_eq_mul_inv,mul_comm]
  all_goals left; norm_num

theorem program_run (z : ℂ) :
    run program z = ⟨((1+z)/2,(1-z)/2),31,0,True⟩ := by
  change ((run (coefficient false) z).pass (fun y =>
    (run (coefficient true) z).pass (fun x => Bill.one (y,x)))) = _
  rw [coefficient_run,coefficient_run]
  simp [Bill.pass,Bill.one]

theorem program_C : run program Complex.I = ⟨(a,b),31,0,True⟩ := by
  rw [program_run]
  rfl

/-- Charged upstream coefficient construction agrees with the actual seven
source instructions, starting from a prepared `i`. -/
theorem actual_execution {n B : ℕ} (x : Fin n → ℂ) (s : State)
    (pc : s.pc=0) (imaginary : s.scalarReg 0=UniformPairMachine.prepared Complex.I)
    (code : 7≤B) (wb : WordBound B s) :
    ∃ t, BoundedExecution UniformPairMachine.coefficientProgram n x B s 7 t ∧
      t.scalarReg 0=UniformPairMachine.prepared (run program Complex.I).val.1 ∧
      t.scalarReg 1=UniformPairMachine.prepared (run program Complex.I).val.2 ∧
      t.natReg=s.natReg ∧ t.natHeap=s.natHeap ∧ t.scalarHeap=s.scalarHeap ∧
      t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
      (run program Complex.I).valid ∧ (run program Complex.I).work ≤ 5*7 ∧
      (run program Complex.I).peak ≤ B := by
  have execution := UniformPairMachine.coefficient_execution n x B s pc imaginary code wb
  have values := UniformPairMachine.coefficient_values s
  have frame := UniformPairMachine.coefficient_frame s
  refine ⟨UniformPairMachine.coefficientState s,execution,?_,?_,frame.1,frame.2.1,
    frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2,?_,?_,?_⟩
  · simpa only [program_C] using values.1
  · simpa only [program_C] using values.2
  · rw [program_C]
    trivial
  · rw [program_C]
    change 31 ≤ 5*7
    omega
  · rw [program_C]
    exact Nat.zero_le B

end
end ExactFourierCircuits.DFTModelBinaryCoefficients
