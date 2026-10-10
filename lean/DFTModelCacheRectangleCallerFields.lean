import DFTModelCacheRectangleCallerProgram
import DFTModelCacheRectanglePreparationGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def preparedConfig (q:UniformLocalRectangleDescriptors.Row) : DFTModelCacheTopology.Config.T :=
 DFTModelCacheTopology.config (DFTModelCacheTopology.exponent q.a q.e) q.a q.e

/-- All seven words are from the same original descriptor; physical offset is
retained even though local geometry and Newton indices do not add it. -/
theorem input_rows (seedRadix D C T P:ℕ) (z:ℂ) (d c:ℕ) (enabled:Bool)
 (q:UniformLocalRectangleDescriptors.Row) :
 let x:=input seedRadix D C T P z d c enabled q
 rowValue x 0=q.width ∧ rowValue x 1=q.offset ∧ rowValue x 2=q.a ∧
 rowValue x 3=q.e ∧ rowValue x 4=q.split ∧ rowValue x 5=q.i0 ∧ rowValue x 6=q.j0 := by
 simp [rowValue,input,Tape.look,Tape.tab,UniformLocalRectangleDescriptors.Row.words]

theorem metadata_input (seedRadix D C T P:ℕ) (z:ℂ) (d c:ℕ) (enabled:Bool)
 (q:UniformLocalRectangleDescriptors.Row) :
 metadataValue (input seedRadix D C T P z d c enabled q) (preparedConfig q)=
 DFTModelCacheDisplacement.metadata seedRadix
  (DFTModelCacheRectanglePreparation.parameters seedRadix q) := by
 simp [metadataValue,rowValue,input,Tape.look,Tape.tab,UniformLocalRectangleDescriptors.Row.words,
  preparedConfig,DFTModelCacheTopology.config,DFTModelCacheDisplacement.metadata,
  DFTModelCacheRectanglePreparation.parameters,DFTModelCacheRectanglePreparation.width,
  DFTModelCacheRectanglePreparation.height,DFTModelCacheTopology.exponent,
  UniformWorkspacePlanner.exponent]

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller
