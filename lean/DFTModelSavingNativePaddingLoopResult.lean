import DFTModelSavingNativePaddingRoleData
import UniformRecursivePaddingArrays

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingLoop
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
open UniformRecursivePaddingArrays (values action)
noncomputable section

structure Result (n B U R A F q w r stack depth stackTop saved : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (L : List (Fin R)) (I : ℂ)
    (handler : Handler DFTModelSavingRecords.Port) (index prior : ℕ)
    (s s0 u u0 : State) (ticks outPrior : ℕ)
    (f f0 g g0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) : Prop where
  run : BoundedRuns P.program n x B s ticks u
  zeroRun : BoundedRuns P.program n (fun _=>0) B s0 ticks u0
  matched : StateMatch u u0
  pc : u.pc=P.address .loop
  cursor : u.natReg 2850=saved
  parent : Parent (q*(w+1)+r) q A F r stack depth u
  zeroParent : Parent (q*(w+1)+r) q A F r stack depth u0
  printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q outPrior).data u
  present : Present A R (2^(q*(w+1)+r)) g u
  zeroPresent : Present A R (2^(q*(w+1)+r)) g0 u0
  nat : ∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠U+1→z≠U+3→z≠F-4→
    u.natHeap z=s.natHeap z
  zeroNat : ∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠U+1→z≠U+3→z≠F-4→
    u0.natHeap z=s0.natHeap z
  scalar : ∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r)≤z)→u.scalarHeap z=s.scalarHeap z
  zeroScalar : ∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r)≤z)→u0.scalarHeap z=s0.scalarHeap z
  constants : UniformBinaryCStageMachine.Constants u
  zeroConstants : UniformBinaryCStageMachine.Constants u0
  roots : u.rootOrders=s.rootOrders
  zeroRoots : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  zeroOutputs : u0.outputs=s0.outputs
  time : ticks≤L.length*(roleCost q w r cost+6)+10
  value : (DFTModelSavingNativePaddingFold.steps handler q r index L.length
    ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired f f0)).val=
      ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired g g0)
  values : UniformRecursivePaddingArrays.values g=action q w r R L
    (UniformRecursivePaddingArrays.values f)
  zeroValues : UniformRecursivePaddingArrays.values g0=action q w r R L
    (UniformRecursivePaddingArrays.values f0)

end
end ExactFourierCircuits.DFTModelSavingNativePaddingLoop
