import UniformGlobalCalendarPhases
import UniformFixedNetworkScheduleMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarPhaseDirectory
open UniformMachine UniformGlobalMatchingScaleMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def kind : Phase → ℕ
 | .diagonal _ => 0
 | .kernel => 1
def lane : Phase → ℕ
 | .diagonal j => j.val
 | .kernel => 0
def words : List ℕ := phases.flatMap (fun p => [kind p,lane p])
lemma words_length : words.length=56 := rfl
lemma words_values : ∀ v ∈ words, v≤8 := by decide
lemma words_kind (i : Fin 28) : words[2*i.val]'(by rw [words_length];have:=i.isLt;omega)=
 kind (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩) := by fin_cases i <;> rfl
lemma words_lane (i : Fin 28) : words[2*i.val+1]'(by rw [words_length];have:=i.isLt;omega)=
 lane (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩) := by fin_cases i <;> rfl

/-- Real172-instruction literal printer constructs the phase decoder's two-word
kind/lane bank; no preinitialized directory is assumed. -/
theorem execution (T B n : ℕ) (x : Fin n → ℂ) (s : State)
 (base : s.natReg 2600=T) (pc : s.pc=0) (wb : WordBound B s)
 (extent : T+56≤B) (code : 172≤B) :
 ∃ u, BoundedExecution (UniformFixedNetworkScheduleMachine.program words) n x B s 172 u ∧
 UniformFixedNetworkScheduleMachine.Printed T words u ∧
 (∀ z, z<T ∨ T+56≤z → u.natHeap z=s.natHeap z) ∧
 UniformFixedNetworkScheduleMachine.Frame s u ∧ u.natReg 2601=T+56 := by
 have produced := UniformFixedNetworkScheduleMachine.printer_execution words T B n x s base pc wb
  (by intro v hv;have:=words_values v hv;omega) (by rwa [words_length])
  (by rwa [words_length])
 simpa only [words_length] using produced

/-- Actual seven-op dynamic phase reader. -/
def readOps : List Op := [.literal 6762 2,.mul 6763 6761 6762,.add 6763 6760 6763,
 .getNat 6764 6763,.literal 6762 1,.add 6763 6763 6762,.getNat 6765 6763]
def program : Program := readOps.map Op.code++[.halt]
lemma program_length : program.length=8 := rfl
lemma readOps_code : BlockAt readOps program 0 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma halt_code : program[7]?=some .halt := rfl

lemma printed_cells (T : ℕ) (s : State) (printed : UniformFixedNetworkScheduleMachine.Printed T words s)
 (i : Fin 28) :
 s.natHeap (T+2*i.val)=some (kind (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩)) ∧
 s.natHeap (T+2*i.val+1)=some (lane (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩)) := by
 constructor
 · have h:=printed (2*i.val) (by rw [words_length];have:=i.isLt;omega)
   rwa [words_kind] at h
 · have h:=printed (2*i.val+1) (by rw [words_length];have:=i.isLt;omega)
   rw [words_lane] at h
   simpa only [Nat.add_assoc] using h

/-- Charged decoder reads precisely the real compiler's phase kind and lane. -/
theorem read_execution (T B n : ℕ) (x : Fin n → ℂ) (s : State) (i : Fin 28)
 (base : s.natReg 6760=T) (index : s.natReg 6761=i.val) (pc : s.pc=0) (wb : WordBound B s)
 (printed : UniformFixedNetworkScheduleMachine.Printed T words s) (extent : T+56≤B) (code : 8≤B) :
 BoundedExecution program n x B s 8 (applyBlock readOps s) ∧
 (applyBlock readOps s).natReg 6764=kind (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩) ∧
 (applyBlock readOps s).natReg 6765=lane (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩) := by
 obtain ⟨k,l⟩:=printed_cells T s printed i
 have kr : kind (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩)≤1 := by
  generalize phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩ = p
  cases p <;> simp [kind]
 have lr : lane (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩)≤8 := by
  generalize phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩ = p
  cases p with
  | diagonal j => have:=j.isLt;simp [lane];omega
  | kernel => simp [lane]
 simp only [List.get_eq_getElem] at kr lr
 simp only [Nat.mul_comm,Nat.add_assoc] at k l
 have run:=block_runs readOps program 0 n B x s readOps_code pc wb (by change 7≤B;omega)
  (by simp [readOps,readable,Op.readable,Op.apply,writeNat,next,base,index,k,l,Nat.add_assoc])
  (by simp [readOps,peak,Op.peak,Op.apply,writeNat,next,base,index,k,l,Nat.add_assoc];have:=i.isLt;omega)
 have endPC : (applyBlock readOps s).pc=7 := by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have haltEq : step program n x (applyBlock readOps s)=.halted (applyBlock readOps s) := by simp [step,endPC,halt_code]
 refine ⟨run.executes (.halt run.final_bound haltEq),?_,?_⟩
 all_goals simp [readOps,applyBlock,Op.apply,writeNat,next,base,index,k,l,Nat.add_assoc]

end
end ExactFourierCircuits.UniformGlobalCalendarPhaseDirectory
