import DFTModelSavingResidualNativeGroupSlice
import DFTModelSavingResidualSourcePeak
import DFTModelSavingResidualBoolean

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine
noncomputable section

def bits111 : Tape ℕ := Tape.tab 3 (fun _=>1)
def bits001 : Tape ℕ := Tape.tab 3 (fun j=>if j=2 then 1 else 0)
def bank : Tape Tagged.T := Tape.tab 8 (fun j=>tagged (j%2=1) j (j+10))
def flipped : Tape Tagged.T := (run (DFTModelSavingResidualFlip.program Tagged) (2,(1,bank))).val

theorem weight_three_forward :
  (run DFTModelSavingResidualOrientation.program ((3,bits111),0)).val=1 := by rfl
theorem weight_three_inverse :
  (run DFTModelSavingResidualOrientation.program ((3,bits111),1)).val=0 := by rfl
theorem weight_one_forward :
  (run DFTModelSavingResidualOrientation.program ((3,bits001),0)).val=0 := by rfl
theorem weight_one_inverse :
  (run DFTModelSavingResidualOrientation.program ((3,bits001),1)).val=1 := by rfl
theorem weight_three_charged :
  (run DFTModelSavingResidualOrientation.program ((3,bits111),0)).work=84 := by rfl
theorem missing_bits_stay_missing :
  (run DFTModelSavingResidualOrientation.program ((3,Tape.empty ℕ),0)).val=0 := by rfl

theorem flip_length : flipped.len=8 := by rfl
theorem flip_first : flipped.look 0 Tagged.blank=bank.look 1 Tagged.blank := by rfl
theorem flip_next_pair : flipped.look 2 Tagged.blank=bank.look 3 Tagged.blank := by rfl
theorem flip_last : flipped.look 7 Tagged.blank=bank.look 6 Tagged.blank := by rfl
theorem flip_true_flag : (flipped.look 0 Tagged.blank).1=1 := by rfl
theorem flip_false_flag : (flipped.look 1 Tagged.blank).1=0 := by rfl
theorem flip_baseline : (flipped.look 0 Tagged.blank).2.1=1 := by
  rw [flip_first]
  change ((1 : ℕ) : ℂ)=1
  norm_num
theorem flip_homogeneous : (flipped.look 0 Tagged.blank).2.2=11 := by
  rw [flip_first]
  change ((1 : ℕ) : ℂ)+10=11
  norm_num
theorem flip_disabled :
  (run (DFTModelSavingResidualFlip.program Tagged) (2,(0,bank))).val.look 3 Tagged.blank=
    bank.look 3 Tagged.blank := by rfl
theorem flip_three_bits :
  (run (DFTModelSavingResidualFlip.program Tagged) (8,(1,bank))).val.look 0 Tagged.blank=
    bank.look 7 Tagged.blank := by rfl

end
end ExactFourierCircuits.DFTModelSavingResidualFixtures
