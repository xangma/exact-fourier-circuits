import UniformSixCPhaseContext
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCReplayDescriptor
open UniformReplayPrint UniformSixCPhaseContext
noncomputable section
def enabledParameters (p:UniformChunkMatchingPreparation.Parameters) (enabled:Bool) :=
 {p with height:={p.height with enabled:=enabled}}
lemma enabledMatching {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (enabled:Bool) :
 UniformChunkMatchingPreparation.Layout (enabledParameters p enabled) B:=by
 constructor
 all_goals first
 | exact l.code | exact l.radixPositive | exact l.sourceRange | exact l.targetRange
 | exact l.separated | exact l.capacity | exact l.oldRows | exact l.oldColors | exact l.oldDirectory
 | exact l.borrowFresh | exact l.selectedFresh | exact l.ordinalFresh | exact l.mappedFresh
 | exact l.permutationFresh | exact l.widthsFresh | exact l.markersFresh | exact l.finalBound
 | exact l.depthBound | exact l.colorBound

def enabledPacking {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (enabled:Bool) :
 UniformMatchingPackingPreparation.Layout (enabledParameters p enabled) B:=
 ⟨enabledMatching l.matching enabled,l.packing,l.bound,l.oneAxis,l.axisRow,l.volume,l.code⟩
def geometry {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) : UniformSixCBroadcast.Geometry:=
 ⟨p.radix,p.source,p.height.e,p.target,p.height.a,UniformCrossHeightPreparationMachine.gates p.height,p.borrowed,
  l.capacity,by unfold UniformCrossHeightPreparationMachine.gates;nlinarith,l.targetRange,l.sourceRange⟩
def halfWord {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (positive:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) : List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) :=
 phaseWord l false ha he ++ reverseCode (UniformSixCBroadcast.word positive (geometry l.matching)
  (UniformToeplitzCrossDAG.bankSize p.height.K)) ++ phaseWord l true ha he

def fullWord {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) : List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) :=
 (show List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) from halfWord (p:=enabledParameters p true) (enabledPacking l true) true ha he) ++
 (show List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) from halfWord (p:=enabledParameters p false) (enabledPacking l false) false ha he)
end
end ExactFourierCircuits.UniformSixCReplayDescriptor
