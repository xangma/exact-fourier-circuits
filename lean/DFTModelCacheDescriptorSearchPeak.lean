import DFTModelCacheDescriptorSearchBounds
import DFTModelCacheDescriptorFitsPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] allBad searchStep selected selectSteps

theorem searchStep_peak (v b old : ℕ) (hb : b≤v) :
    (run searchStep (v,(b,old))).peak≤4000*(v+1)^2 := by
  by_cases hz : b=0
  · subst b
    rw [searchStep]
    simp [searchIndex,searchOld,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  · have ha:=allBad_peak v b (by omega) hb
    dsimp only [run] at ha
    rw [searchStep]
    dsimp only [searchIndex,searchOld,searchPair,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    split_ifs <;> simp_all only [max_zero,zero_max]
    all_goals omega

theorem selectSteps_peak (v j : ℕ) (hj : j≤v+1) :
    (selectSteps v j).peak≤4000*(v+1)^2 := by
  induction j with
  | zero => rw [selectSteps_zero];exact Nat.zero_le _
  | succ j ih =>
    have old:=ih (by omega)
    have step:=searchStep_peak v j (selectSteps v j).val (by omega)
    rw [selectSteps_succ]
    change max (max (selectSteps v j).peak (run searchStep (v,(j,(selectSteps v j).val))).peak) (j+1)≤_
    refine max_le (max_le old step) ?_
    have h : v+1≤4000*(v+1)^2 := by nlinarith
    omega

theorem selected_peak (v : ℕ) : (run selected v).peak≤4000*(v+1)^2 := by
  have old:=selectSteps_peak v (v+1) (le_refl _)
  rw [selected]
  dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero]
  rw [selectSteps] at old
  dsimp only [run] at old
  simp only [max_le_iff]
  have h : v+1≤4000*(v+1)^2 := by nlinarith
  exact ⟨⟨by nlinarith,h⟩,old⟩

end
end ExactFourierCircuits.DFTModelCacheDescriptor
