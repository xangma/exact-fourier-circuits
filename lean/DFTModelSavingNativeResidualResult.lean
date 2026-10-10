import DFTModelSavingNativeResidualFinish

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeResidual
open UniformMachine BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformFixedNetworkScheduleMachine (macroRecord)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program

structure Result (n B T nRoles R A F q w r stack depth stackTop:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)
 (handler:Handler DFTModelSavingResidual.Port)(rawTape:Tape ℕ)
 (s s0 u u0:State)(ticks:ℕ)(Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar):Prop where
 run:BoundedRuns P.program n x B s ticks u
 zeroRun:BoundedRuns P.program n (fun _=>0) B s0 ticks u0
 matched:StateMatch u u0
 pc:u.pc=P.address .loop
 parent:UniformRecursiveResidualEdge.Parent (q*(w+1)+r) q A F
  (T+(macroRecord q emb (.edge old new role edge)).data.length) r stack depth u
 zeroParent:UniformRecursiveResidualEdge.Parent (q*(w+1)+r) q A F
  (T+(macroRecord q emb (.edge old new role edge)).data.length) r stack depth u0
 present:∀i z,u.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y i z)
 zeroPresent:∀i z,u0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y0 i z)
 nat:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠F-6→u.natHeap z=s.natHeap z
 zeroNat:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠F-6→u0.natHeap z=s0.natHeap z
 scalar:∀z,z<F→(z<A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤z)→u.scalarHeap z=s.scalarHeap z
 zeroScalar:∀z,z<F→(z<A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤z)→u0.scalarHeap z=s0.scalarHeap z
 constants:UniformBinaryCStageMachine.Constants u
 zeroConstants:UniformBinaryCStageMachine.Constants u0
 roots:u.rootOrders=s.rootOrders
 zeroRoots:u0.rootOrders=s0.rootOrders
 outputs:u.outputs=s.outputs
 zeroOutputs:u0.outputs=s0.outputs
 time:ticks≤edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+53
 value:(Code.run DFTModelSavingRecords.residual handler
  (r,(rawTape,((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)))).val=
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired Y Y0)
 values:∀z,(Y (emb role) z).value=(UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformNativeResidualSemantics.nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))).mulVec
  (fun y=>(X (emb role) y).value) z
 zeroValues:∀z,(Y0 (emb role) z).value=(UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformNativeResidualSemantics.nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))).mulVec
  (fun y=>(X0 (emb role) y).value) z
 other:∀i,i≠emb role→∀z,Y i z=X i z
 zeroOther:∀i,i≠emb role→∀z,Y0 i z=X0 i z

end
end ExactFourierCircuits.DFTModelSavingNativeResidual
