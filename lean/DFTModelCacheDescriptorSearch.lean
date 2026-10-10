import DFTModelCacheDescriptorFits

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev SearchStepInput := p w (p w w)
def searchIndex : Prog false SearchStepInput w := .comp (.atom .snd) (.atom .fst)
def searchOld : Prog false SearchStepInput w := .comp (.atom .snd) (.atom .snd)
def searchPair : Prog false SearchStepInput Pair := .fork (.atom .fst) searchIndex
def searchStep : Prog false SearchStepInput w :=
  .ifz searchIndex searchOld
    (.ifz (.comp searchPair allBad) searchIndex searchOld)
/-- Exhaustively test every positive b≤v and retain the last fitting b. -/
def selected : Prog false w w :=
  .loop (nat .add (.atom .id) (.atom (.lit 1))) (.atom (.lit 0)) searchStep

def selectSteps (v j : ℕ) : Bill ℕ :=
  Bill.steps 0 (fun b old=>run searchStep (v,(b,old))) j

theorem selectSteps_succ (v j : ℕ) :
    selectSteps v (j+1)=((selectSteps v j).pass
      (fun old=>run searchStep (v,(j,old)))).pay 1 (j+1) := rfl

theorem selected_value_steps (v : ℕ) : (run selected v).val=(selectSteps v (v+1)).val := rfl
theorem selectSteps_zero (v : ℕ) : selectSteps v 0=Bill.one 0 := rfl

theorem selected_valid_steps (v : ℕ) : (run selected v).valid ↔ (selectSteps v (v+1)).valid := by
  simp only [selected,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  change (((True ∧ True ∧ True) ∧ True) ∧ True ∧ (selectSteps v (v+1)).valid) ↔ _
  simp

theorem selected_work_steps (v : ℕ) : (run selected v).work=(selectSteps v (v+1)).work+7 := by
  simp only [selected,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  change 5+(1+(selectSteps v (v+1)).work)+1=_
  omega

attribute [local irreducible] allBad selected searchStep selectSteps

theorem searchStep_value (v b old : ℕ) :
    (run searchStep (v,(b,old))).val=if b=0 then old else
      if UniformWorkspacePlanner.allFits v b then b else old := by
  rw [searchStep]
  dsimp only [searchIndex,searchOld,searchPair,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  have hz := allBad_zero v b
  dsimp only [run] at hz
  split_ifs <;> simp_all


theorem selectSteps_one (v : ℕ) : (selectSteps v 1).val=0 := by
  rw [selectSteps_succ,selectSteps_zero]
  change (run searchStep (v,(0,0))).val=0
  rw [searchStep_value]
  rfl

theorem selectSteps_seen (v j : ℕ) (hj : 0<j) :
    UniformWorkspaceSearchMachine.Seen v j (selectSteps v j).val := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hz : j=0
    · subst j
      rw [selectSteps_one]
      exact UniformWorkspaceSearchMachine.seen_zero v
    · have old:=ih (by omega)
      have hnext:=UniformWorkspaceSearchMachine.seen_next old (by omega : 0<j)
      rw [selectSteps_succ]
      change UniformWorkspaceSearchMachine.Seen v (j+1)
        (run searchStep (v,(j,(selectSteps v j).val))).val
      rw [searchStep_value,ite_eq_right hz]
      exact hnext

theorem selected_value (v : ℕ) : (run selected v).val=UniformWorkspacePlanner.selected v := by
  rw [selected_value_steps]
  change (selectSteps v (v+1)).val=_
  exact UniformWorkspaceSearchMachine.selected_of_seen (selectSteps_seen v (v+1) (by omega))

end
end ExactFourierCircuits.DFTModelCacheDescriptor
