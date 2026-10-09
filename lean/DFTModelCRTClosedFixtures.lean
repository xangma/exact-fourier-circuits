import DFTModelCRTClosedProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTClosedFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def input32 : DFTModelCRTMetadata.Input.T := (1,(6,(2,Tape.tab 1 (fun _ => 3))))

theorem inverse_2_mod_3 : (run DFTModelCRTMetadata.inverse (2,3)).val=2 := by rfl
theorem inverse_3_mod_2 : (run DFTModelCRTMetadata.inverse (3,2)).val=1 := by rfl
theorem inverse_2_mod_5 : (run DFTModelCRTMetadata.inverse (2,5)).val=3 := by rfl

theorem rows32 : (List.range 2).map (fun i =>
    (run DFTModelCRTMetadata.metadata input32).val.look i (0,(0,0))) =
      [(3,(4,2)),(2,(3,3))] := by rfl

theorem alpha32 : (List.range 6).map (fun i =>
    (run DFTModelCRTClosed.program input32).val.1.look i 0)=[0,3,4,1,2,5] := by rfl

theorem inverse_beta32 : (List.range 6).map (fun i =>
    (run DFTModelCRTClosed.program input32).val.2.look i 0)=[0,5,2,1,4,3] := by rfl

theorem metadata_work32 : (run DFTModelCRTMetadata.metadata input32).work=386 := by rfl

theorem closed_work32 : (run DFTModelCRTClosed.program input32).work=1535 := by rfl

theorem malformed_missing_prime_radix_zero :
    (run DFTModelCRTMetadata.metadata (1,(6,(2,Tape.empty _)))).val.look 0 (9,(9,9))=(0,(0,0)) := by rfl

end
end ExactFourierCircuits.DFTModelCRTClosedFixtures
