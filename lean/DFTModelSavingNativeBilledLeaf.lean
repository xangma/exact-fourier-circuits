import DFTModelSavingNativeLeafExactTime
import DFTModelSavingNativeBilledSequence
import DFTModelSavingCostBilledLeafActual

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeBilledLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch

/-- All concrete nonrecursive opcodes, with their actual measured source
execution and the stream's per-record work charged to those same ticks. -/
theorem execution (n B T tapeEnd A F q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (leaf : DFTModelSavingNativeLeafTyped.Leaf i)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q i).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (recordEnd : T+(Instruction.record q i).data.length≤F-6)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 g g0,DFTModelSavingNativeBilledSequence.StepResult n B T A F q rest stack depth stackTop K
      cost x I h i s s0 f f0 u u0 (ticks q rest cost i) g g0 := by
  obtain ⟨u,u0,g,g0,source⟩:=DFTModelSavingNativeLeafExactTime.execution
    n B T tapeEnd A F q rest stack depth stackTop reserve cost x I h i leaf s s0 f f0 same pc parent
    metadata live printed data data0 geometry recordEnd constants bound
  refine ⟨u,u0,g,g0,source,?_⟩
  exact (DFTModelSavingCost.leaf_actual_billed q rest cost i leaf I h f f0 geometry.positive).trans
    (Nat.mul_le_mul_right _ cap)

end
end ExactFourierCircuits.DFTModelSavingNativeBilledLeaf
