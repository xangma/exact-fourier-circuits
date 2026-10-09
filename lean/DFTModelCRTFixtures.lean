import DFTModelCRTSelected

set_option autoImplicit false

/-! Small exact kernel reductions of the actual typed program, covering MSB
ordering, modular reduction, scatter inversion and malformed auxiliary metadata. -/
namespace ExactFourierCircuits.DFTModelCRTFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCRT
noncomputable section

def rows23 : Tape (ℕ × (ℕ × ℕ)) :=
  Tape.tab 2 (fun i => if i=0 then (2,(3,3)) else (3,(4,2)))
def input23 : (p w Args).T := (2,(0,(6,rows23)))

theorem physical_alpha_23 :
    (List.range 6).map (fun j => (run program input23).val.1.look j 0) =
      [0,4,2,3,1,5] := by rfl

theorem inverse_beta_23 :
    (List.range 6).map (fun j => (run program input23).val.2.look j 0) =
      [0,5,1,3,2,4] := by rfl

theorem work_23 : (run program input23).work=1255 := by rfl
theorem peak_23 : (run program input23).peak≤49 := by
  apply program_peak_le 2 _ 6 (by decide) rfl (by decide)
  · intro i hi
    interval_cases i <;> decide
  · intro i hi
    interval_cases i <;> decide
  · decide
theorem valid_23 : (run program input23).valid := program_valid _ _

theorem empty_axes_alpha :
    (run program (0,(0,(1,Tape.empty _)))).val.1.look 0 9=0 := by rfl
theorem empty_axes_inverse :
    (run program (0,(0,(1,Tape.empty _)))).val.2.look 0 9=0 := by rfl
theorem empty_axes_work : (run program (0,(0,(1,Tape.empty _)))).work=39 := by rfl
theorem empty_axes_peak : (run program (0,(0,(1,Tape.empty _)))).peak=1 := by rfl

def rows2 : Tape (ℕ × (ℕ × ℕ)) := Tape.tab 1 (fun _ => (2,(1,1)))
theorem one_axis_alpha :
    (run program (1,(0,(2,rows2)))).val.1.look 1 0=1 := by rfl
theorem one_axis_inverse :
    (run program (1,(0,(2,rows2)))).val.2.look 1 0=1 := by rfl
theorem one_axis_work : (run program (1,(0,(2,rows2)))).work=327 := by rfl

/-- Missing radix metadata is not silently replaced by a supplied permutation. -/
theorem missing_metadata_empty :
    (run program (1,(0,(2,Tape.empty _)))).val.1.len=0 := by rfl

def badBeta : Tape (ℕ × (ℕ × ℕ)) := Tape.tab 1 (fun _ => (2,(1,0)))
/-- Permutation validity is essential: duplicate scatter keys use the real last write. -/
theorem duplicate_beta_last_write :
    (run program (1,(0,(2,badBeta)))).val.2.look 0 0=1 := by rfl
theorem duplicate_beta_unwritten_blank :
    (run program (1,(0,(2,badBeta)))).val.2.look 1 9=0 := by rfl

end
end ExactFourierCircuits.DFTModelCRTFixtures
