import DFTModelCacheDAGDepthValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDAGDepth
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] step program ModelEquivalenceInterpreter.update

def workBudget (N G : ℕ) : ℕ := 5*(N+1+G)+19+G*(35*(N+1+G)+91)

theorem rowValue_le (q : Row3.T) (d : Tape ℕ) (j : ℕ)
    (h : ∀ a,d.look a 0 ≤ j) : rowValue q d ≤ j+1 := by
  unfold rowValue
  split
  · exact Nat.add_le_add_right (max_le (h _) (h _)) 1
  · exact Nat.add_le_add_right (h _) 1

theorem iterations_labels_le (N : ℕ) (qs : Tape Row3.T) (j a : ℕ) :
    (iterations N qs j).val.look a 0 ≤ j := by
  induction j generalizing a with
  | zero=>
    simp only [iterations,Bill.steps,Bill.one,Tape.look,Tape.tab]
    by_cases h : a<N+1+qs.len <;> simp [h]
  | succ j ih=>
    change (run step ((N,qs),(j,(iterations N qs j).val))).val.look a 0 ≤ j+1
    rw [step_run,ModelEquivalenceInterpreter.tape_set_look]
    split
    · exact rowValue_le _ _ j ih
    · exact (ih a).trans (by omega)

theorem iterations_valid (N : ℕ) (qs : Tape Row3.T) (j : ℕ) :
    (iterations N qs j).valid := by
  induction j with
  | zero=>trivial
  | succ j ih=>
    change (iterations N qs j).valid ∧ (run step ((N,qs),(j,_))).valid
    rw [step_run]
    exact ⟨ih,trivial⟩

theorem iterations_work (N : ℕ) (qs : Tape Row3.T) (j : ℕ) :
    (iterations N qs j).work ≤ 1+j*(35*(N+1+qs.len)+91) := by
  induction j with
  | zero=>simp [iterations,Bill.steps,Bill.one]
  | succ j ih=>
    have hu:=(ModelEquivalenceInterpreter.update_work_bounds w (iterations N qs j).val
      (N+1+j) (rowValue (qs.look j (0,(0,0))) (iterations N qs j).val)).2
    rw [iterations_length] at hu
    change (iterations N qs j).work+
      (run step ((N,qs),(j,(iterations N qs j).val))).work+1 ≤ _
    rw [step_run]
    dsimp only [Bill.work]
    have hm:(j+1)*(35*(N+1+qs.len)+91)=j*(35*(N+1+qs.len)+91)+(35*(N+1+qs.len)+91):=by ring
    rw [hm]
    split_ifs <;>omega

theorem iterations_peak (N : ℕ) (qs : Tape Row3.T) (j : ℕ) (hj:j ≤ qs.len) :
    (iterations N qs j).peak ≤ max (N+1+qs.len) 2 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have old:=ih (by omega)
    have hv:=rowValue_le (qs.look j (0,(0,0))) (iterations N qs j).val j
      (iterations_labels_le N qs j)
    have hu:=ModelEquivalenceInterpreter.update_peak w (iterations N qs j).val
      (N+1+j) (rowValue (qs.look j (0,(0,0))) (iterations N qs j).val)
    rw [iterations_length] at hu
    have hz:N+1+qs.len≠0:=by omega
    simp only [hz,ite_false] at hu
    change max (max (iterations N qs j).peak
      (run step ((N,qs),(j,(iterations N qs j).val))).peak) (j+1) ≤ _
    rw [step_run,hu]
    dsimp only [Bill.peak]
    omega

theorem program_valid (N : ℕ) (qs : Tape Row3.T) : (run program (N,qs)).valid := by
  rw [program_run]
  exact iterations_valid N qs qs.len

theorem program_work (N : ℕ) (qs : Tape Row3.T) :
    (run program (N,qs)).work ≤ workBudget N qs.len := by
  have h:=iterations_work N qs qs.len
  rw [program_run]
  unfold workBudget
  dsimp only [Bill.work]
  omega

theorem program_peak (N : ℕ) (qs : Tape Row3.T) :
    (run program (N,qs)).peak ≤ N+qs.len+2 := by
  have h:=iterations_peak N qs qs.len (le_refl _)
  rw [program_run]
  dsimp only [Bill.peak]
  omega

theorem specification (N : ℕ) (qs : List UniformDAGDepthMachine.Row)
    (ht : UniformDAGDepthMachine.Topological N qs) :
    (run program (N,rowsTape qs)).val=
      Tape.tab (N+1+qs.length) (UniformDAGDepthMachine.evaluate (N+1) qs (fun _=>0)) ∧
    (run program (N,rowsTape qs)).valid ∧
    (run program (N,rowsTape qs)).work ≤ workBudget N qs.length ∧
    (run program (N,rowsTape qs)).peak ≤ N+qs.length+2 :=
  ⟨program_value N qs ht,program_valid N (rowsTape qs),program_work N (rowsTape qs),
    program_peak N (rowsTape qs)⟩

end
end ExactFourierCircuits.DFTModelCacheDAGDepth
