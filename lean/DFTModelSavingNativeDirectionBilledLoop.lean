import DFTModelSavingNativeDirectionBilledFold

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

theorem billed_loop (n B T nRoles R A F q w r stack depth stackTop reserve K:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(index:ℕ)(L:List (Fin edge.dimension))
 (vis:Visit edge.dimension index L)(s s0:State)(X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (childIH:DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies (q*(w+1)+r) n B reserve stack stackTop K K cost x I handler)
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
 (rawTape:Tape ℕ)(wide:2≤ w)(roles:R=UniformBatching.width)
 (coefficient:363*(w+1)+240*r+1347+104*UniformBatching.width≤ K)
 (initial:DFTModelClockControl.Node.T)
 (atIndex:((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)=
  (DFTModelSavingDirection.steps handler r rawTape initial index).val)
 (copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) rawTape) :
 ∃u u0 ticks,∃Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar,
 PairLoopResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge L X X0 I handler rawTape s s0 u u0 ticks Y Y0 ∧ prefixWork handler r rawTape initial L≤ K*ticks := by
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
  refine ⟨u,u0,1,X,X0,⟨run,run0,same.withPC _,setPC_pc s _,control_pc h _,control_pc h0 _,data,data0,
   (fun _ _ _=> rfl),(fun _ _ _=> rfl),(fun _ _ _=> rfl),(fun _ _ _=> rfl),cu,cu0,fr.2.2.1,fr0.2.2.1,fr.2.2.2,fr0.2.2.2,?_,rfl,(fun _=> rfl),(fun _=> rfl),
   (fun _ _ _=> rfl),(fun _ _ _=> rfl)⟩,by rw [prefixWork_nil];omega⟩
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
  obtain ⟨a,a0,dt,Y,Y0,one,p,hp,first,localTicks,childTicks,exactTicks,localBound,children⟩:=billed_execution n B T nRoles R A F q w r stack depth stackTop reserve K K cost x ready emb role edge j X
   I handler childIH smaller (setPC_pc s _) rc.cursor readyPrinted rc.index rc.nativeBase rc.original rc.bits rc.volume rc.frontier rc.rest rc.stack rc.depth rc.one
   readyData qp m2 rp fits recordEnd widthBound arrayEnd poolEnd square low stackRoom stackEnd recordAbove room readyConstants test.final_bound code
   X0 ready0 (same.withPC _) readyData0 rawTape copied rc.table dataBase
  have rowBound: (DFTModelSavingDirection.rowBill handler r j.val rawTape initial
   ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)).work+1≤ K*dt:=by
   rw [exactTicks]
   exact row_work q r emb role edge j X X0 I handler rawTape copied p hp first fits qp wide roles
    K localTicks childTicks coefficient localBound children initial
  have nextPrefix:((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired Y Y0)=
   (DFTModelSavingDirection.steps handler r rawTape initial (j.val+1)).val:=by
   rw [steps_succ_value,←atIndex,row_initial handler r j.val rawTape initial
    ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)]
   exact one.value.symm
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
  obtain ⟨u,u0,ut,Z,Z0,remaining,tailWork⟩:=ih b b0 Y Y0 matched bp bc bc0 printedB dataB dataB0 cb nrun.final_bound nextPrefix
  refine ⟨u,u0,1+dt+2+ut,Z,Z0,⟨((test.trans one.run).trans nrun).trans remaining.run,
   ((test0.trans one.zeroRun).trans nrun0).trans remaining.zeroRun,remaining.matched,remaining.pc,
   remaining.control,remaining.zeroControl,remaining.present,remaining.zeroPresent,?_,?_,?_,?_,
   remaining.constants,remaining.zeroConstants,remaining.roots.trans (br.trans (one.roots.trans rf.2.2.1)),
   remaining.zeroRoots.trans (br0.trans (one.zeroRoots.trans rf0.2.2.1)),remaining.outputs.trans (bo.trans (one.outputs.trans rf.2.2.2)),
   remaining.zeroOutputs.trans (bo0.trans (one.zeroOutputs.trans rf0.2.2.2)),?_,?_,?_,?_,?_,?_⟩,?_⟩
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
  · rw [prefixWork_cons,←atIndex]
    have sum:=Nat.add_le_add rowBound tailWork
    rw [←Nat.mul_add] at sum
    exact sum.trans (Nat.mul_le_mul_left K (by omega))

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
