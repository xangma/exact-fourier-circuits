import DFTModelCacheDescriptorSearch
import DFTModelCacheDescriptorFitsBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] allBad searchStep selectSteps selected

theorem searchStep_valid (v b old : ℕ) : (run searchStep (v,(b,old))).valid := by
  have ha:=allBad_valid v b
  dsimp only [run] at ha
  rw [searchStep]
  dsimp only [searchIndex,searchOld,searchPair,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  split_ifs <;> simp_all

theorem searchStep_work (v b old : ℕ) (hb : b≤v) :
    (run searchStep (v,(b,old))).work≤1000*(v+1)^3+25 := by
  by_cases hz : b=0
  · subst b
    rw [searchStep]
    simp [searchIndex,searchOld,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  · have ha:=allBad_work v b (by omega)
    dsimp only [run] at ha
    rw [searchStep]
    dsimp only [searchIndex,searchOld,searchPair,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    split_ifs <;> simp_all only <;> omega

theorem selectSteps_valid (v j : ℕ) : (selectSteps v j).valid := by
  induction j with
  | zero => rw [selectSteps_zero];trivial
  | succ j ih =>
    rw [selectSteps_succ]
    exact ⟨ih,searchStep_valid v j _⟩

theorem selectSteps_work (v j : ℕ) (hj : j≤v+1) :
    (selectSteps v j).work≤j*(1000*(v+1)^3+26)+1 := by
  induction j with
  | zero => rw [selectSteps_zero];simp only [Bill.one,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ j ih =>
    have old : (selectSteps v j).work≤j*(1000*(v+1)^3+26)+1 := ih (by omega)
    have step:=searchStep_work v j (selectSteps v j).val (by omega)
    rw [selectSteps_succ]
    change (selectSteps v j).work+(run searchStep (v,(j,(selectSteps v j).val))).work+1≤_
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem selected_valid (v : ℕ) : (run selected v).valid := by
  exact (selected_valid_steps v).mpr (selectSteps_valid _ _)

theorem selected_work (v : ℕ) : (run selected v).work≤2000*(v+1)^4 := by
  have old:=selectSteps_work v (v+1) (le_refl _)
  rw [selected_work_steps]
  have h1:=Nat.le_self_pow (by decide : (4:ℕ)≠0) (v+1)
  have h2:=Nat.one_le_pow 4 (v+1) (by omega)
  have eq : (v+1)*(1000*(v+1)^3+26)=1000*(v+1)^4+26*(v+1) := by ring
  rw [eq] at old
  omega

end
end ExactFourierCircuits.DFTModelCacheDescriptor
