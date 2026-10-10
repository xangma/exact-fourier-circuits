import DFTModelSavingNativePaddingLoop
import UniformRecursivePaddingExecution

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingExecution
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
noncomputable section

structure Result (n B U R A F q w r stack depth stackTop saved start : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (handler : Handler DFTModelSavingRecords.Port)
    (s s0 u u0 : State) (ticks prior : ℕ)
    (f f0 g g0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) : Prop where
  run : BoundedRuns P.program n x B s ticks u
  zeroRun : BoundedRuns P.program n (fun _=>0) B s0 ticks u0
  matched : StateMatch u u0
  pc : u.pc=P.address .loop
  cursor : u.natReg 2850=saved
  parent : Parent (q*(w+1)+r) q A F r stack depth u
  zeroParent : Parent (q*(w+1)+r) q A F r stack depth u0
  printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data u
  present : Present A R (2^(q*(w+1)+r)) g u
  zeroPresent : Present A R (2^(q*(w+1)+r)) g0 u0
  endPointer : u.natHeap (F-1)=s.natHeap (F-1)
  zeroEndPointer : u0.natHeap (F-1)=s0.natHeap (F-1)
  unitPointer : u.natHeap (F-2)=s.natHeap (F-2)
  zeroUnitPointer : u0.natHeap (F-2)=s0.natHeap (F-2)
  nat : ∀z,z<F→(z<stack+34*depth∨stackTop ≤ z)→z≠U+1→z≠U+3→
    z≠F-6→z≠F-5→z≠F-4→z≠F-3→u.natHeap z=s.natHeap z
  zeroNat : ∀z,z<F→(z<stack+34*depth∨stackTop ≤ z)→z≠U+1→z≠U+3→
    z≠F-6→z≠F-5→z≠F-4→z≠F-3→u0.natHeap z=s0.natHeap z
  scalar : ∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r) ≤ z)→u.scalarHeap z=s.scalarHeap z
  zeroScalar : ∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r) ≤ z)→u0.scalarHeap z=s0.scalarHeap z
  constants : UniformBinaryCStageMachine.Constants u
  zeroConstants : UniformBinaryCStageMachine.Constants u0
  roots : u.rootOrders=s.rootOrders
  zeroRoots : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  zeroOutputs : u0.outputs=s0.outputs
  time : ticks ≤ (R-start)*(roleCost q w r cost+6)+21
  value : (DFTModelSavingNativePaddingFold.steps handler q r start (R-start)
    ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired f f0)).val=
      ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired g g0)
  values : ∀i,UniformRecursivePaddingArrays.values g i=
    if start  ≤  i.val then (UniformRecursivePaddingArrays.lowMatrix q w r).mulVec
      (UniformRecursivePaddingArrays.values f i) else UniformRecursivePaddingArrays.values f i
  zeroValues : ∀i,UniformRecursivePaddingArrays.values g0 i=
    if start  ≤  i.val then (UniformRecursivePaddingArrays.lowMatrix q w r).mulVec
      (UniformRecursivePaddingArrays.values f0 i) else UniformRecursivePaddingArrays.values f0 i

end
end ExactFourierCircuits.DFTModelSavingNativePaddingExecution
