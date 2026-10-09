import UniformBorrowedCoordinateExecutionBridge
import UniformChunkMatchingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBorrowedCoordinateBridge
open UniformChunkPortMachine UniformToeplitzChunkWord

/-- The actual matching producer's coordinate function agrees, occurrence by
occurrence, with the exact placement of the mathematical chunk word. -/
theorem coordinate_natPorts {B:ℕ}(p:UniformChunkMatchingPreparation.Parameters)
 (l:UniformChunkMatchingPreparation.Layout p B)
 (i:Fin (p.height.e+UniformCrossHeightPreparationMachine.gates p.height+p.height.a)):
 UniformChunkMatchingPreparation.coordinate p l.capacity
  (natPorts p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a i)=
 ((placementOfFit (g:=UniformCrossHeightPreparationMachine.gates p.height)
  (intervalEmbedding p.radix p.source p.height.e l.sourceRange)
  (intervalEmbedding p.radix p.target p.height.a l.targetRange)
  (interval_separated l.sourceRange l.targetRange l.separated)
  (by have h:=l.capacity;omega)).embedding i).val:=
 mapped_natPorts_eq l.sourceRange l.targetRange l.separated l.capacity i
end ExactFourierCircuits.UniformBorrowedCoordinateBridge
