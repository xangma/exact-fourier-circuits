import DFTModelSavingNativeDirectionAlignment
import DFTModelSavingDirectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width DFTModelSavingResidual.program

structure PairDirectionResult (n B T nRoles R A F q w r stack depth stackTop:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (rawTape:Tape ℕ)(s s0 u u0:State)(ticks:ℕ)(Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar) : Prop where
 run:BoundedRuns P.program n x B s ticks u
 zeroRun:BoundedRuns P.program n (fun _=>0) B s0 ticks u0
 matched:StateMatch u u0
 pc:u.pc=P.address .directionNext
 control:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse u
 zeroControl:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse u0
 present:∀i z,u.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y i z)
 zeroPresent:∀i z,u0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y0 i z)
 nat:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z
 zeroNat:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u0.natHeap z=s0.natHeap z
 scalar:∀z,z<F→(z<A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤z)→u.scalarHeap z=s.scalarHeap z
 zeroScalar:∀z,z<F→(z<A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤z)→u0.scalarHeap z=s0.scalarHeap z
 constants:UniformBinaryCStageMachine.Constants u
 zeroConstants:UniformBinaryCStageMachine.Constants u0
 roots:u.rootOrders=s.rootOrders
 zeroRoots:u0.rootOrders=s0.rootOrders
 outputs:u.outputs=s.outputs
 zeroOutputs:u0.outputs=s0.outputs
 time:ticks+3≤UniformRecursiveResidualDirectionLoop.directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost
 value:(DFTModelSavingDirection.rowBill handler r j.val rawTape
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)).val=
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired Y Y0)
 values:∀z,(Y (emb role) z).value=(UniformRecursiveResidualDirectionLoop.directionMatrix q w r edge j).mulVec
  (fun y=>(X (emb role) y).value) z
 zeroValues:∀z,(Y0 (emb role) z).value=(UniformRecursiveResidualDirectionLoop.directionMatrix q w r edge j).mulVec
  (fun y=>(X0 (emb role) y).value) z
 other:∀i,i≠emb role→∀z,Y i z=X i z
 zeroOther:∀i,i≠emb role→∀z,Y0 i z=X0 i z

theorem of_tails (n B T nRoles R A F q w r stack depth stackTop:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (rawTape:Tape ℕ)(copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) rawTape)
 (s s0 a a0 u u0:State)(ticks:ℕ)(Y Y0:Fin (2^(q*(w+1)+r))→Scalar)
 (p:Fin (w+1))(hp:edgeVectors edge j p=1)(first:∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0)
 (fits:ExplicitSeedBudget.roleBits≤q*w+r)(qp:1≤q)(arrayEnd:A+R*2^(q*(w+1)+r)≤F)
 (same:StateMatch s s0)
 (data:∀a z,s.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X a z))
 (data0:∀a z,s0.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X0 a z))
 (actual:DirectionResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j (X (emb role)) p hp s a u ticks Y)
 (zero:DirectionResult n B T nRoles R A F q w r stack depth stackTop cost (fun _=>0) emb role edge j (X0 (emb role)) p hp s0 a0 u0 ticks Y0)
 (pairBank:DFTModelSavingResidualNativeGroup.PairBank q (BG.groupCount q w r) (F+4*2^(q*(w+1)+r)) (BG.groupCount q w r)
  I handler (FV.input q w r fits (edgeVectors edge j) p hp (X (emb role)))
   (FV.input q w r fits (edgeVectors edge j) p hp (X0 (emb role))) a a0) :
 ∃Z Z0:Fin R→Fin (2^(q*(w+1)+r))→Scalar,
 PairDirectionResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j X X0 I handler rawTape s s0 u u0 ticks Z Z0 := by
 obtain ⟨u0',run0',matched⟩:=DFTModelSavingResidualNativeGroup.boundedRuns_match (y:=fun _=>0) actual.run same
 have last:u0'=u0:=DFTModelSavingResidualNativeGroup.boundedRuns_unique run0' zero.run
 subst u0'
 let Z:Fin R→Fin (2^(q*(w+1)+r))→Scalar:=Function.update X (emb role) Y
 let Z0:Fin R→Fin (2^(q*(w+1)+r))→Scalar:=Function.update X0 (emb role) Y0
 have updated:∀z,Z (emb role) z=Y z:=by intro z;simp only [Z,Function.update_self]
 have updated0:∀z,Z0 (emb role) z=Y0 z:=by intro z;simp only [Z0,Function.update_self]
 have kept:∀a,a≠emb role→∀z,Z a z=X a z:=by
  intro a ne z;simp only [Z,Function.update_of_ne ne]
 have kept0:∀a,a≠emb role→∀z,Z0 a z=X0 a z:=by
  intro a ne z;simp only [Z0,Function.update_of_ne ne]
 have present:∀i z,u.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Z i z):=by
  intro i z
  by_cases eq:i=emb role
  · subst i;rw [updated];exact actual.present z
  · rw [actual.scalar _ (by
      have h:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*(w+1)+r)) i
      have small:=z.isLt
      unfold UniformFixedNetworkShearChildMachine.roleBase at h
      omega) (by
      have h:=UniformFixedNetworkShearChildMachine.role_outside A (emb role) i eq z
      simpa only [UniformFixedNetworkShearChildMachine.roleBase,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h),kept i eq]
    exact data i z
 have present0:∀i z,u0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Z0 i z):=by
  intro i z
  by_cases eq:i=emb role
  · subst i;rw [updated0];exact zero.present z
  · rw [zero.scalar _ (by
      have h:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*(w+1)+r)) i
      have small:=z.isLt
      unfold UniformFixedNetworkShearChildMachine.roleBase at h
      omega) (by
      have h:=UniformFixedNetworkShearChildMachine.role_outside A (emb role) i eq z
      simpa only [UniformFixedNetworkShearChildMachine.roleBase,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h),kept0 i eq]
    exact data0 i z
 have scatter:∀z,Z (emb role) (DFTModelResidualBasisGeometry.permutation q w r (edgeVectors edge j) p hp z)=
  UniformRecursiveResidualOutput.selected (q*(w+1)+r) q (by nlinarith)
   (UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge))
   (UniformRecursiveGroupBank.array (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) a) z:=by
  intro z
  rw [updated]
  exact Option.some.inj ((actual.present _).symm.trans (actual.scatter z))
 have scatter0:∀z,Z0 (emb role) (DFTModelResidualBasisGeometry.permutation q w r (edgeVectors edge j) p hp z)=
  UniformRecursiveResidualOutput.selected (q*(w+1)+r) q (by nlinarith)
   (UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge))
   (UniformRecursiveGroupBank.array (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) a0) z:=by
  intro z
  rw [updated0]
  exact Option.some.inj ((zero.present _).symm.trans (zero.scatter z))
 have value: (DFTModelSavingDirection.rowBill handler r j.val rawTape
   ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)
   ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)).val=
   ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired Z Z0):=by
  obtain ⟨hq,hm,ha,hflag,_⟩:=DFTModelSavingDirection.macro_headers q emb role edge rawTape copied
  change (Code.run DFTModelSavingResidual.program handler
   (DFTModelSavingDirection.decoded r j.val rawTape ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0))).val=_
  unfold DFTModelSavingDirection.decoded
  rw [hq,hm,ha,hflag]
  exact node_value handler q w r (F+4*2^(q*(w+1)+r)) (q*(w+1)+r)
   (edgeVectors edge j) (DFTModelSavingDirection.row (w+1) j.val rawTape) (emb role) I (edgeInverse edge)
   X X0 Z Z0 qp (DFTModelSavingDirection.row_source q emb role edge rawTape copied j)
   (UniformResidualFibers.edgeVector_norm edge j) p hp first fits a a0 pairBank scatter scatter0 kept kept0
 have charge: ticks+3≤UniformRecursiveResidualDirectionLoop.directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost:=by
  have boundTime:=actual.time
  have scan:=UniformResidualOrientationMachine.ticks_bound (edgeVectors edge j)
  have tailBound:(if UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge)
   then (17*((w+1)+r)+35)*2^(q*(w+1)+r)+39 else 10*2^(q*(w+1)+r)+12)≤
   max ((17*((w+1)+r)+35)*2^(q*(w+1)+r)+39) (10*2^(q*(w+1)+r)+12):=by
   split
   · exact Nat.le_max_left _ _
   · exact Nat.le_max_right _ _
  unfold UniformRecursiveResidualDirectionLoop.directionCost
  omega
 refine ⟨Z,Z0,actual.run,zero.run,matched,actual.pc,actual.control,zero.control,present,present0,
  actual.nat,zero.nat,actual.scalar,zero.scalar,actual.constants,zero.constants,actual.roots,zero.roots,
  actual.outputs,zero.outputs,charge,value,?_,?_,kept,kept0⟩
 · intro z;rw [updated];exact actual.values z
 · intro z;rw [updated0];exact zero.values z


end
end ExactFourierCircuits.DFTModelSavingNativeDirection
