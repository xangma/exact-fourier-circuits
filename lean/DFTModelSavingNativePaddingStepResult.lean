import DFTModelSavingNativePaddingExecution
import DFTModelSavingNativePaddingStepValue
import UniformRecursivePaddingRecord

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingStep
open UniformMachine DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl UniformFixedNetwork UniformNativeScheduleSemantics
open UniformFixedNetworkScheduleMachine (Printed actualRoles)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
noncomputable section

/-- Padding's real footprint includes its patched unit record and four mode
cells. The core record frame intentionally does not cover this final record. -/
structure Frame (U A F q rest stack depth stackTop : ℕ) (s u : State) : Prop where
  endPointer : u.natHeap (F-1)=s.natHeap (F-1)
  unitPointer : u.natHeap (F-2)=s.natHeap (F-2)
  natHeap : ∀z,z<F→(z<stack+34*depth∨stackTop ≤ z)→z≠U+1→z≠U+3→
    z≠F-6→z≠F-5→z≠F-4→z≠F-3→u.natHeap z=s.natHeap z
  scalarHeap : ∀z,z<F→(z<A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z
  roots : u.rootOrders=s.rootOrders
  outputs : u.outputs=s.outputs

structure Result (n B T U A F q rest stack depth stackTop : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler DFTModelSavingRecords.Port)
    (s s0 u u0 : State) (time : ℕ)
    (f f0 g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop where
  actual : BoundedRuns UniformRecursiveSavingProgram.program n x B s time u
  baseline : BoundedRuns UniformRecursiveSavingProgram.program n (fun _=>0) B s0 time u0
  matched : StateMatch u u0
  pc : u.pc=UniformRecursiveSavingProgram.address .loop
  pc0 : u0.pc=UniformRecursiveSavingProgram.address .loop
  parent : Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u
  parent0 : Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u0
  data : Present A W (2^(q*m+rest)) g u
  data0 : Present A W (2^(q*m+rest)) g0 u0
  values : arrayValues q rest g=(semantic q rest .padding).mulVec (arrayValues q rest f)
  values0 : arrayValues q rest g0=(semantic q rest .padding).mulVec (arrayValues q rest f0)
  frame : Frame U A F q rest stack depth stackTop s u
  frame0 : Frame U A F q rest stack depth stackTop s0 u0
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  time_bound : time ≤ 73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost)
  code : DFTModelSavingChronology.recordStep W rest h (Instruction.record q .padding)
    ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)=
      ((q*m+rest,I),DFTModelRecursiveScalarSource.paired g g0)

end
end ExactFourierCircuits.DFTModelSavingNativePaddingStep
