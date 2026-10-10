import DFTModelSavingNativeDirectionLoopValue

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly UniformTensorMonomialMachine BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
open UniformRecursiveResidualDirectionLoop (Visit action directionCost next_execution control_pc setPC_frame setPC_pc)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width DFTModelSavingResidual.program

theorem matched_runs {p:Program}{n B ticks:ℕ}{x:Fin n→ℂ}{s s0 u u0:State}
 (a:BoundedRuns p n x B s ticks u)(z:BoundedRuns p n (fun _=>0) B s0 ticks u0)(same:StateMatch s s0):StateMatch u u0:=by
 obtain ⟨v,run,last⟩:=DFTModelSavingResidualNativeGroup.boundedRuns_match (y:=fun _=>0) a same
 have eq:=DFTModelSavingResidualNativeGroup.boundedRuns_unique run z
 subst v
 exact last

structure PairLoopResult (n B T nRoles R A F q w r stack depth stackTop:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(L:List (Fin edge.dimension))
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (rawTape:Tape ℕ)(s s0 u u0:State)(ticks:ℕ)(Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar) : Prop where
 run:BoundedRuns P.program n x B s ticks u
 zeroRun:BoundedRuns P.program n (fun _=>0) B s0 ticks u0
 matched:StateMatch u u0
 pc:u.pc=P.address .edgeDone
 control:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth edge.dimension edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse u
 zeroControl:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth edge.dimension edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse u0
 present:∀i z,u.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y i z)
 zeroPresent:∀i z,u0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y0 i z)
 nat:∀z,z< F→(z< stack+34*depth∨stackTop≤ z)→u.natHeap z=s.natHeap z
 zeroNat:∀z,z< F→(z< stack+34*depth∨stackTop≤ z)→u0.natHeap z=s0.natHeap z
 scalar:∀z,z< F→(z< A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤ z)→u.scalarHeap z=s.scalarHeap z
 zeroScalar:∀z,z< F→(z< A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)≤ z)→u0.scalarHeap z=s0.scalarHeap z
 constants:UniformBinaryCStageMachine.Constants u
 zeroConstants:UniformBinaryCStageMachine.Constants u0
 roots:u.rootOrders=s.rootOrders
 zeroRoots:u0.rootOrders=s0.rootOrders
 outputs:u.outputs=s.outputs
 zeroOutputs:u0.outputs=s0.outputs
 time:ticks≤ L.length*directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+1
 value:rows handler r rawTape L ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)=
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired Y Y0)
 values:∀z,(Y (emb role) z).value=action q w r edge L (fun y=>(X (emb role) y).value) z
 zeroValues:∀z,(Y0 (emb role) z).value=action q w r edge L (fun y=>(X0 (emb role) y).value) z
 other:∀i,i≠emb role→∀z,Y i z=X i z
 zeroOther:∀i,i≠emb role→∀z,Y0 i z=X0 i z

theorem paired_loop (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(index:ℕ)(L:List (Fin edge.dimension))
 (vis:Visit edge.dimension index L)(s s0:State)(X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (childIH:DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
 (same:StateMatch s s0)(smaller:q< q*(w+1)+r)(pc:s.pc=P.address .directionTest)
 (h:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth index edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse s)
 (h0:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth index edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse s0)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (data:∀a z,s.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X a z))
 (data0:∀a z,s0.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X0 a z))
 (qp:1≤ q)(m2:2≤ w+1)(rp:r< w+1)(fits:ExplicitSeedBudget.roleBits≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length≤ F)
 (widthBound:(w+1)+1≤ B)(arrayEnd:A+R*2^(q*(w+1)+r)≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r)≤ B)(square:(2^(q*(w+1)+r))^2≤ B)
 (low:3≤ F)(dataBase:3≤ A)(stackRoom:stack+34*(depth+q+2)≤ stackTop)(stackEnd:stackTop≤ F)
 (recordAbove:stackTop≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length≤ B)
 (rawTape:Tape ℕ)(copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) rawTape) :
 ∃u u0 ticks,∃Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar,
 PairLoopResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge L X X0 I handler rawTape s s0 u u0 ticks Y Y0 := by
 induction vis generalizing s s0 X X0 with
 | done=>
  let u:=setPC s (P.address .edgeDone)
  let u0:=setPC s0 (P.address .edgeDone)
  have run:BoundedRuns P.program n x B s 1 u:=by
   simpa only [Nat.lt_irrefl,ite_false] using UniformRecursiveResidualControl.direction_test n B edge.dimension edge.dimension x s pc h.index h.dimension bound code
  have run0:BoundedRuns P.program n (fun _=>0) B s0 1 u0:=by
   simpa only [Nat.lt_irrefl,ite_false] using UniformRecursiveResidualControl.direction_test n B edge.dimension edge.dimension (fun _=>0) s0
    (same.pc.trans pc) h0.index h0.dimension (same.wordBound bound) code
  have fr:=setPC_frame s (P.address .edgeDone)
  have fr0:=setPC_frame s0 (P.address .edgeDone)
  have cu:UniformBinaryCStageMachine.Constants u:=by
   unfold UniformBinaryCStageMachine.Constants at constants ⊢
   exact ⟨(congrFun fr.2.1 1).trans constants.1,(congrFun fr.2.1 2).trans constants.2⟩
  have cu0:UniformBinaryCStageMachine.Constants u0:=by
   have c0:=DFTModelSavingResidualNativeGroup.constants_match same constants
   unfold UniformBinaryCStageMachine.Constants at c0 ⊢
   exact ⟨(congrFun fr0.2.1 1).trans c0.1,(congrFun fr0.2.1 2).trans c0.2⟩
  refine ⟨u,u0,1,X,X0,run,run0,same.withPC _,setPC_pc s _,control_pc h _,control_pc h0 _,data,data0,
   (fun _ _ _=> rfl),(fun _ _ _=> rfl),(fun _ _ _=> rfl),(fun _ _ _=> rfl),cu,cu0,fr.2.2.1,fr0.2.2.1,fr.2.2.2,fr0.2.2.2,?_,rfl,(fun _=> rfl),(fun _=> rfl),
   (fun _ _ _=> rfl),(fun _ _ _=> rfl)⟩
  simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
 | step j tail visit ih=>
  let ready:=setPC s (P.address .gather)
  let ready0:=setPC s0 (P.address .gather)
  have test:BoundedRuns P.program n x B s 1 ready:=by
   simpa only [j.isLt,ite_true] using UniformRecursiveResidualControl.direction_test n B j.val edge.dimension x s pc h.index h.dimension bound code
  have test0:BoundedRuns P.program n (fun _=>0) B s0 1 ready0:=by
   simpa only [j.isLt,ite_true] using UniformRecursiveResidualControl.direction_test n B j.val edge.dimension (fun _=>0) s0
    (same.pc.trans pc) h0.index h0.dimension (same.wordBound bound) code
  have rc:=control_pc h (P.address .gather)
  have rf:=setPC_frame s (P.address .gather)
  have rf0:=setPC_frame s0 (P.address .gather)
  have readyPrinted:Printed T (macroRecord q emb (.edge old new role edge)).data ready:=by
   intro z hz;rw [rf.1];exact printed z hz
  have readyData:∀a z,ready.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X a z):=by
   intro a z;rw [rf.2.1];exact data a z
  have readyData0:∀a z,ready0.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X0 a z):=by
   intro a z;rw [rf0.2.1];exact data0 a z
  have readyConstants:UniformBinaryCStageMachine.Constants ready:=by
   unfold UniformBinaryCStageMachine.Constants at constants ⊢
   exact ⟨(congrFun rf.2.1 1).trans constants.1,(congrFun rf.2.1 2).trans constants.2⟩
  obtain ⟨a,a0,dt,Y,Y0,one⟩:=paired_execution n B T nRoles R A F q w r stack depth stackTop reserve cost x ready emb role edge j X
   I handler childIH smaller (setPC_pc s _) rc.cursor readyPrinted rc.index rc.nativeBase rc.original rc.bits rc.volume rc.frontier rc.rest rc.stack rc.depth rc.one
   readyData qp m2 rp fits recordEnd widthBound arrayEnd poolEnd square low stackRoom stackEnd recordAbove room readyConstants test.final_bound code
   X0 ready0 (same.withPC _) readyData0 rawTape copied rc.table dataBase
  have dimB:edge.dimension≤ B:=by have z:=one.run.final_bound.2.1 4132;rwa [one.control.dimension] at z
  obtain ⟨b,nrun,bp,bc,bnh,bsh,bsr,br,bo⟩:=next_execution n B (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
   (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse x a
   one.control one.pc one.run.final_bound (by omega) code
  obtain ⟨b0,nrun0,bp0,bc0,bnh0,bsh0,bsr0,br0,bo0⟩:=next_execution n B (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
   (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse (fun _=>0) a0
   one.zeroControl (one.matched.pc.trans one.pc) one.zeroRun.final_bound (by omega) code
  have matched:=matched_runs nrun nrun0 one.matched
  have printedB:Printed T (macroRecord q emb (.edge old new role edge)).data b:=by
   intro z hz;rw [bnh,one.nat _ (by omega) (Or.inr (by omega))];exact printed z hz
  have dataB:∀i z,b.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y i z):=by
   intro i z;rw [bsh];exact one.present i z
  have dataB0:∀i z,b0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (Y0 i z):=by
   intro i z;rw [bsh0];exact one.zeroPresent i z
  have cb:UniformBinaryCStageMachine.Constants b:=by
   have ca:=one.constants
   unfold UniformBinaryCStageMachine.Constants at ca ⊢
   exact ⟨(congrFun bsh 1).trans ca.1,(congrFun bsh 2).trans ca.2⟩
  obtain ⟨u,u0,ut,Z,Z0,remaining⟩:=ih b b0 Y Y0 matched bp bc bc0 printedB dataB dataB0 cb nrun.final_bound
  refine ⟨u,u0,1+dt+2+ut,Z,Z0,((test.trans one.run).trans nrun).trans remaining.run,
   ((test0.trans one.zeroRun).trans nrun0).trans remaining.zeroRun,remaining.matched,remaining.pc,
   remaining.control,remaining.zeroControl,remaining.present,remaining.zeroPresent,?_,?_,?_,?_,
   remaining.constants,remaining.zeroConstants,remaining.roots.trans (br.trans (one.roots.trans rf.2.2.1)),
   remaining.zeroRoots.trans (br0.trans (one.zeroRoots.trans rf0.2.2.1)),remaining.outputs.trans (bo.trans (one.outputs.trans rf.2.2.2)),
   remaining.zeroOutputs.trans (bo0.trans (one.zeroOutputs.trans rf0.2.2.2)),?_,?_,?_,?_,?_,?_⟩
  · intro z hz away;exact (remaining.nat z hz away).trans ((congrFun bnh z).trans ((one.nat z hz away).trans (congrFun rf.1 z)))
  · intro z hz away;exact (remaining.zeroNat z hz away).trans ((congrFun bnh0 z).trans ((one.zeroNat z hz away).trans (congrFun rf0.1 z)))
  · intro z hz away;exact (remaining.scalar z hz away).trans ((congrFun bsh z).trans ((one.scalar z hz away).trans (congrFun rf.2.1 z)))
  · intro z hz away;exact (remaining.zeroScalar z hz away).trans ((congrFun bsh0 z).trans ((one.zeroScalar z hz away).trans (congrFun rf0.2.1 z)))
  · have atime:=one.time;have btime:=remaining.time
    simp only [List.length_cons,Nat.succ_mul];omega
  · change rows handler r rawTape tail (DFTModelSavingDirection.rowBill handler r j.val rawTape
     ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)
     ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)).val=_
    rw [one.value];exact remaining.value
  · intro z
    change (Z (emb role) z).value=action q w r edge tail
     ((UniformRecursiveResidualDirectionLoop.directionMatrix q w r edge j).mulVec (fun y=>(X (emb role) y).value)) z
    rw [←funext one.values];exact remaining.values z
  · intro z
    change (Z0 (emb role) z).value=action q w r edge tail
     ((UniformRecursiveResidualDirectionLoop.directionMatrix q w r edge j).mulVec (fun y=>(X0 (emb role) y).value)) z
    rw [←funext one.zeroValues];exact remaining.zeroValues z
  · intro i ne z;exact (remaining.other i ne z).trans (one.other i ne z)
  · intro i ne z;exact (remaining.zeroOther i ne z).trans (one.zeroOther i ne z)

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
