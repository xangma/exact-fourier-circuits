import UniformRecursivePreparedResidualDirection
import UniformRecursiveResidualDirectionLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
open UniformMachine BinaryFrames UniformBinaryTensorCoordinates
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
open UniformTensorMonomialMachine (setPC)
noncomputable section
theorem loop_prepared (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(index:ℕ)(L:List (Fin edge.dimension))
 (vis:Visit edge.dimension index L)(s:State)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q < q*(w+1)+r)(pc:s.pc=P.address .directionTest)
 (h:D.Control (q*(w+1)+r) q A F T r stack depth index edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length)
  (macroRecord q emb (.edge old new role edge)).inverse s)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B)
 (low:3 ≤ F)(dataBase:3 ≤ A)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (recordAbove:stackTop ≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u ticks,∃Y:Fin (2^(q*(w+1)+r))→Scalar,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .edgeDone ∧
 (∀z,u.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (Y z)) ∧
 (∀z,(Y z).value=action q w r edge L (fun y=>(X y).value) z) ∧
 D.Control (q*(w+1)+r) q A F T r stack depth edge.dimension edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length)
  (macroRecord q emb (.edge old new role edge)).inverse u ∧
 (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A+(emb role).val*2^(q*(w+1)+r)∨
  A+((emb role).val+1)*2^(q*(w+1)+r) ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 ticks ≤ L.length*directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+1 ∧ (UniformRecursivePreparedValues.Prepared X→UniformRecursivePreparedValues.Prepared Y):=by
 induction vis generalizing s X with
 | done=>
  let u:=setPC s (P.address .edgeDone)
  have run:BoundedRuns P.program n x B s 1 u:=by
   simpa only [Nat.lt_irrefl,ite_false] using UniformRecursiveResidualControl.direction_test n B edge.dimension edge.dimension x s pc h.index h.dimension bound code
  have fr:=setPC_frame s (P.address .edgeDone)
  refine ⟨u,1,X,run,setPC_pc s _,?_,fun _=>rfl,control_pc h _,?_,?_,?_,fr.2.2.1,fr.2.2.2,?_,fun h=>h⟩
  · intro z;rw [fr.2.1];exact data z
  · intro z _ _;exact congrFun fr.1 z
  · intro z _ _;exact congrFun fr.2.1 z
  · unfold UniformBinaryCStageMachine.Constants at constants ⊢
    exact ⟨(congrFun fr.2.1 1).trans constants.1,(congrFun fr.2.1 2).trans constants.2⟩
  · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
 | step j tail visit ih=>
  let ready:=setPC s (P.address .gather)
  have test:BoundedRuns P.program n x B s 1 ready:=by
   simpa only [j.isLt,ite_true] using UniformRecursiveResidualControl.direction_test n B j.val edge.dimension x s pc h.index h.dimension bound code
  have readyControl:=control_pc h (P.address .gather)
  have readyFrame:=setPC_frame s (P.address .gather)
  have readyPrinted:Printed T (macroRecord q emb (.edge old new role edge)).data ready:=by
   intro z hz;rw [readyFrame.1];exact printed z hz
  have readyData:∀z,ready.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z):=by
   intro z;rw [readyFrame.2.1];exact data z
  have readyConstants:UniformBinaryCStageMachine.Constants ready:=by
   unfold UniformBinaryCStageMachine.Constants at constants ⊢
   exact ⟨(congrFun readyFrame.2.1 1).trans constants.1,(congrFun readyFrame.2.1 2).trans constants.2⟩
  obtain ⟨a,dt,Y,run,ap,yp,yv,ac,an,ash,ca,ar,ao,atime,preparedY⟩:=UniformRecursiveResidualDirection.execution_prepared
   n B T nRoles R A F q w r stack depth stackTop reserve cost x ready emb role edge j X
   childIH smaller (setPC_pc s _) readyControl.cursor readyPrinted readyControl.index readyControl.nativeBase readyControl.original readyControl.bits readyControl.volume readyControl.frontier readyControl.rest readyControl.stack readyControl.depth readyControl.one readyControl.table
   readyData qp m2 rp fits recordEnd widthBound arrayEnd poolEnd square low dataBase stackRoom stackEnd recordAbove room readyConstants test.final_bound code
  have dimB:edge.dimension ≤ B:=by have z:=run.final_bound.2.1 4132;rwa [ac.dimension] at z
  obtain ⟨b,nrun,bp,bc,bnh,bsh,bsr,br,bo⟩:=next_execution n B (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
   (T+(macroRecord q emb (.edge old new role edge)).data.length)
   (macroRecord q emb (.edge old new role edge)).inverse x a ac ap run.final_bound (by omega) code
  have printedB:Printed T (macroRecord q emb (.edge old new role edge)).data b:=by
   intro z hz
   rw [bnh,an _ (by omega) (Or.inr (by omega))]
   exact readyPrinted z hz
  have dataB:∀z,b.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (Y z):=by
   intro z;rw [bsh];exact yp z
  have cb:UniformBinaryCStageMachine.Constants b:=by
   unfold UniformBinaryCStageMachine.Constants at ca ⊢
   exact ⟨(congrFun bsh 1).trans ca.1,(congrFun bsh 2).trans ca.2⟩
  obtain ⟨u,ut,Z,ur,up,zp,zv,uc,un,ush,cu,uro,uo,utime,preparedZ⟩:=ih b Y bp bc printedB dataB cb nrun.final_bound
  have scanner:=UniformResidualOrientationMachine.ticks_bound (edgeVectors edge j)
  have tailBound:(if UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge)
   then (17*((w+1)+r)+35)*2^(q*(w+1)+r)+39 else 10*2^(q*(w+1)+r)+12) ≤
   max ((17*((w+1)+r)+35)*2^(q*(w+1)+r)+39) (10*2^(q*(w+1)+r)+12):=by
   split
   · exact Nat.le_max_left _ _
   · exact Nat.le_max_right _ _
  have localBound:1+dt+2 ≤ directionCost q w r
   (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost:=by
   unfold directionCost
   omega
  refine ⟨u,1+dt+2+ut,Z,((test.trans run).trans nrun).trans ur,up,zp,?_,uc,?_,?_,cu,
   uro.trans (br.trans (ar.trans readyFrame.2.2.1)),uo.trans (bo.trans (ao.trans readyFrame.2.2.2)),?_,fun prep=>preparedZ (preparedY prep)⟩
  · intro z
    change (Z z).value=action q w r edge tail ((directionMatrix q w r edge j).mulVec (fun y=>(X y).value)) z
    have valuesEq : (fun y => (Y y).value) =
      (directionMatrix q w r edge j).mulVec (fun y => (X y).value) := funext yv
    rw [←valuesEq]
    exact zv z
  · intro z hz away
    exact (un z hz away).trans ((congrFun bnh z).trans ((an z hz away).trans (congrFun readyFrame.1 z)))
  · intro z hz away
    exact (ush z hz away).trans ((congrFun bsh z).trans ((ash z hz away).trans (congrFun readyFrame.2.1 z)))
  · simp only [List.length_cons,Nat.succ_mul]
    omega
end
end ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
