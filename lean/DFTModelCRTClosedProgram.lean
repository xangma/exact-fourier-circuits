import DFTModelCRTMetadataCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTClosed
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformCRTTraversalCycle UniformSelectedPhysicalCRT
noncomputable section

attribute [local irreducible] DFTModelCRT.program DFTModelCRTMetadata.metadata

/-- Fixed charged packaging: compute all metadata, then call the held CRT producer. -/
def pack : Prog false DFTModelCRTMetadata.Input (p w DFTModelCRT.Args) :=
  .fork DFTModelCRTMetadata.axisCount
    (.fork (.atom (.lit 0))
      (.fork DFTModelCRTMetadata.workingLength DFTModelCRTMetadata.metadata))

def program : Prog false DFTModelCRTMetadata.Input (p (Ty.a w) (Ty.a w)) :=
  .comp pack DFTModelCRT.program

theorem pack_run (x : DFTModelCRTMetadata.Input.T) :
    Code.run pack () x=⟨(x.1+1,(0,(x.2.1,(Code.run DFTModelCRTMetadata.metadata () x).val))),
      (Code.run DFTModelCRTMetadata.metadata () x).work+12,
      max (x.1+1) (Code.run DFTModelCRTMetadata.metadata () x).peak,
      (Code.run DFTModelCRTMetadata.metadata () x).valid⟩ := by
  simp only [pack,Code.run,Atom.run,Bill.pass,Bill.one,Bill.word]
  rw [DFTModelCRTMetadata.axisCount_run,DFTModelCRTMetadata.workingLength_run]
  simp only [max_zero,zero_max,true_and,and_true]
  congr 1
  omega

theorem pack_selected {n : ℕ} (hn : 0<n) :
    (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).val=DFTModelCRT.selectedInput n := by
  rw [pack_run,DFTModelCRTMetadata.selected_metadata hn]
  rfl

theorem selected_value {n : ℕ} (hn : 0<n) :
    (Code.run program () (DFTModelCRTMetadata.selectedInput n)).val=
      (run DFTModelCRT.program (DFTModelCRT.selectedInput n)).val := by
  change (Code.run DFTModelCRT.program ()
    (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).val).val=_
  rw [pack_selected hn]

theorem selected_values {n : ℕ} (hn : 0<n) (j : Fin (len n)) :
    (run program (DFTModelCRTMetadata.selectedInput n)).val.1.look j.val 0=(physicalAlpha n j).val ∧
    (run program (DFTModelCRTMetadata.selectedInput n)).val.2.look j.val 0=((physicalBeta n).symm j).val := by
  rw [selected_value hn]
  exact DFTModelCRT.selected_values n j

theorem selected_output_lengths {n : ℕ} (hn : 0<n) :
    (run program (DFTModelCRTMetadata.selectedInput n)).val.1.len=len n ∧
    (run program (DFTModelCRTMetadata.selectedInput n)).val.2.len=len n := by
  rw [selected_value hn]
  exact DFTModelCRT.selected_output_lengths n

theorem selected_work {n : ℕ} (hn : 0<n) :
    (run program (DFTModelCRTMetadata.selectedInput n)).work≤520*(len n+1) := by
  have metadata := DFTModelCRTMetadata.selected_work hn
  have crt := DFTModelCRT.selected_work hn
  dsimp only [run] at metadata crt
  change (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).work+
    (Code.run DFTModelCRT.program ()
      (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).val).work+1≤_
  rw [pack_selected hn,pack_run]
  dsimp only [Bill.work]
  omega

theorem selected_peak {n : ℕ} (hn : 0<n) :
    (run program (DFTModelCRTMetadata.selectedInput n)).peak≤(len n+1)^2 := by
  have metadata := DFTModelCRTMetadata.selected_peak hn
  have crt := DFTModelCRT.selected_peak hn
  dsimp only [run] at metadata crt
  have count := DFTModelCRTMetadata.selected_count_le hn
  have vv : len n≤(len n+1)^2 := by nlinarith
  change max (max (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).peak
    (Code.run DFTModelCRT.program ()
      (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).val).peak) 0≤_
  rw [pack_selected hn,pack_run]
  exact max_le (max_le (max_le (count.trans vv) metadata) crt) (by omega)

theorem selected_valid {n : ℕ} (hn : 0<n) :
    (run program (DFTModelCRTMetadata.selectedInput n)).valid := by
  change (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).valid ∧
    (Code.run DFTModelCRT.program ()
      (Code.run pack () (DFTModelCRTMetadata.selectedInput n)).val).valid
  rw [pack_selected hn,pack_run]
  exact ⟨DFTModelCRTMetadata.metadata_valid _,DFTModelCRT.selected_valid n⟩

end
end ExactFourierCircuits.DFTModelCRTClosed
