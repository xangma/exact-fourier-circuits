import DFTModelGlobalSectorPreparationAxis

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] blockCell digitCell

theorem blockProgram_run (x : Axis.T) :
 run blockProgram x=(Bill.tab x.2.1.len Block.blank (fun j=>run blockCell (x,j))).pay 6 x.2.1.len := by
 simp only [blockProgram,blockCount,widths,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 simp only [max_zero,zero_max,true_and]
 norm_num
 constructor <;> ac_rfl

theorem blockProgram_valid (x : Axis.T) : (run blockProgram x).valid := by
 rw [blockProgram_run]
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro j _
 rw [blockCell_run]
 trivial

theorem blockProgram_work (x : Axis.T) :
 (run blockProgram x).work≤20*x.2.1.len*x.2.1.len+45*x.2.1.len+8 := by
 rw [blockProgram_run]
 change (Bill.tab x.2.1.len Block.blank (fun j=>run blockCell (x,j))).work+6≤_
 rw [ModelEquivalenceInterpreter.tab_work]
 have h:(∑j∈Finset.range x.2.1.len,(run blockCell (x,j)).work)≤
     x.2.1.len*(20*x.2.1.len+41) := by
  calc
   _≤∑_j∈Finset.range x.2.1.len,(20*x.2.1.len+41) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [blockCell_run]
    have hj:=Finset.mem_range.mp hj
    dsimp only [Bill.work]
    omega
   _=_ := by simp [Nat.mul_comm]
 nlinarith

theorem digitProgram_run (x : Axis.T) :
 run digitProgram x=(Bill.tab x.1 Digit.blank (fun j=>run digitCell (x,j))).pay 2 0 := by
 simp [digitProgram,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 omega

theorem digitProgram_valid (x : Axis.T) : (run digitProgram x).valid := by
 rw [digitProgram_run]
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 exact fun j _=>digitCell_valid x j

theorem digitProgram_work (x : Axis.T) :
 (run digitProgram x).work≤42*x.1*x.2.1.len+60*x.1+4 := by
 rw [digitProgram_run]
 change (Bill.tab x.1 Digit.blank (fun j=>run digitCell (x,j))).work+2≤_
 rw [ModelEquivalenceInterpreter.tab_work]
 have h:(∑j∈Finset.range x.1,(run digitCell (x,j)).work)≤x.1*(42*x.2.1.len+56) := by
  calc
   _≤∑_j∈Finset.range x.1,(42*x.2.1.len+56) :=
    Finset.sum_le_sum (fun j _=>digitCell_work x j)
   _=_ := by simp [Nat.mul_comm]
 nlinarith

attribute [local irreducible] blockProgram digitProgram

theorem prepareAxis_work (x : Axis.T) (shape:x.2.1.len≤x.1) :
 (run prepareAxis x).work≤200*(x.1+1)^2 := by
 have hb:=blockProgram_work x
 have hd:=digitProgram_work x
 have hs:=Nat.mul_le_mul shape shape
 have hp:=Nat.mul_le_mul_left x.1 shape
 change 1+((run blockProgram x).work+(run digitProgram x).work+1)+1≤_
 nlinarith

theorem prepareAxis_valid (x : Axis.T) : (run prepareAxis x).valid := by
 change True ∧ ((run blockProgram x).valid ∧ (run digitProgram x).valid ∧ True) ∧ True
 exact ⟨trivial,⟨blockProgram_valid x,digitProgram_valid x,trivial⟩,trivial⟩

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
