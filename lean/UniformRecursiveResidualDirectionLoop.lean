import UniformRecursiveResidualDirection
import UniformRecursiveResidualControl
import UniformNativeResidualBasis
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
namespace D
export UniformRecursiveResidualDirection (Control)
end D
namespace C
export UniformRecursiveResidualControl (nextOps block_jump next_code next_jump)
end C
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
noncomputable section

/-- The actual chronological basis order, constructed by a bounded counter. -/
inductive Visit (dimension:ℕ):ℕ→List (Fin dimension)→Prop where
 | done:Visit dimension dimension []
 | step (j:Fin dimension)(tail:List (Fin dimension)):
   Visit dimension (j.val+1) tail→Visit dimension j.val (j::tail)

def indices (dimension index:ℕ):∀fuel:ℕ,index+fuel=dimension→List (Fin dimension)
 | 0,_=>[]
 | fuel+1,h=>⟨index,by omega⟩::indices dimension (index+1) fuel (by omega)
lemma indices_visit (dimension index fuel:ℕ)(h:index+fuel=dimension):
 Visit dimension index (indices dimension index fuel h):=by
 induction fuel generalizing index with
 | zero=>
  have eq:index=dimension:=by omega
  subst index
  exact .done
 | succ fuel ih=>exact .step ⟨index,by omega⟩ _ (ih (index+1) (by omega))
lemma indices_values (dimension index fuel:ℕ)(h:index+fuel=dimension):
 (indices dimension index fuel h).map Fin.val=List.range' index fuel:=by
 induction fuel generalizing index with
 | zero=>rfl
 | succ fuel ih=>simp only [indices,List.map_cons,List.range'_succ,ih,Nat.add_one]
lemma indices_all (dimension:ℕ):indices dimension 0 dimension (by omega)=List.finRange dimension:=by
 apply (List.map_inj_right Fin.val_injective).mp
 rw [indices_values,List.map_coe_finRange_eq_range]
 exact (List.range_eq_range').symm

lemma next_generic (main:Program)(start ret n B k q A F T r stack depth index dimension finish flag:ℕ)
 (x:Fin n→ℂ)(s:State)(h:D.Control k q A F T r stack depth index dimension finish flag s)
 (pc:s.pc=start)(atCode:BlockAt C.nextOps main start)(jump:main[start+1]?=some (.jump ret))
 (bound:WordBound B s)(indexBound:index+1 ≤ B)(extent:start+2 ≤ B)(returnBound:ret ≤ B):
 ∃u,BoundedRuns main n x B s 2 u ∧ u.pc=ret ∧
 D.Control k q A F T r stack depth (index+1) dimension finish flag u ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs:=by
 have safe:readable C.nextOps s∧peak C.nextOps s ≤ B:=by
  simp [C.nextOps,readable,peak,Op.readable,Op.peak,evalNat,h.index,h.one,indexBound]
 have run:=C.block_jump main C.nextOps start ret n B x s atCode jump pc bound extent returnBound safe.1 safe.2
 let u:=setPC (applyBlock C.nextOps s) ret
 have keep(j:ℕ)(hj:j≠4134):u.natReg j=s.natReg j:=by
  simp [u,setPC,C.nextOps,applyBlock,Op.apply,evalNat,writeNat,next,hj]
 have ind:u.natReg 4134=index+1:=by
  simp [u,setPC,C.nextOps,applyBlock,Op.apply,evalNat,writeNat,next,h.index,h.one]
 exact ⟨u,run,rfl,⟨(keep _ (by decide)).trans h.cursor,(keep _ (by decide)).trans h.nativeBase,
  (keep _ (by decide)).trans h.original,(keep _ (by decide)).trans h.bits,
  (keep _ (by decide)).trans h.volume,(keep _ (by decide)).trans h.frontier,
  (keep _ (by decide)).trans h.rest,(keep _ (by decide)).trans h.stack,
  (keep _ (by decide)).trans h.depth,(keep _ (by decide)).trans h.one,
  ind,(keep _ (by decide)).trans h.dimension,(keep _ (by decide)).trans h.finish,
  (keep _ (by decide)).trans h.flag,(keep _ (by decide)).trans h.nativeBits,
  (keep _ (by decide)).trans h.nativeRest,(keep _ (by decide)).trans h.table,(keep _ (by decide)).trans h.columns,(keep _ (by decide)).trans h.width⟩,rfl,rfl,rfl,rfl,rfl⟩

theorem next_execution (n B k q A F T r stack depth index dimension finish flag:ℕ)
 (x:Fin n→ℂ)(s:State)(h:D.Control k q A F T r stack depth index dimension finish flag s)
 (pc:s.pc=P.address .directionNext)(bound:WordBound B s)(indexBound:index+1 ≤ B)(code:P.program.length ≤ B):
 ∃u,BoundedRuns P.program n x B s 2 u ∧ u.pc=P.address .directionTest ∧
 D.Control k q A F T r stack depth (index+1) dimension finish flag u ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs:=
 next_generic P.program (P.address .directionNext) (P.address .directionTest)
  n B k q A F T r stack depth index dimension finish flag x s h pc C.next_code C.next_jump bound indexBound
  (R.code_bound .directionNext 2 B rfl code) (R.start_bound .directionTest B code)

end
end ExactFourierCircuits.UniformRecursiveResidualDirectionLoop

namespace ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
open UniformMachine UniformTensorMonomialMachine BinaryFrames UniformBinaryTensorCoordinates
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
noncomputable section

lemma setPC_pc (s:State)(p:ℕ):(setPC s p).pc=p:=rfl
lemma setPC_frame (s:State)(p:ℕ):
 (setPC s p).natHeap=s.natHeap ∧ (setPC s p).scalarHeap=s.scalarHeap ∧
 (setPC s p).rootOrders=s.rootOrders ∧ (setPC s p).outputs=s.outputs:=⟨rfl,rfl,rfl,rfl⟩

lemma control_pc {k q A F T r stack depth index dimension finish flag:ℕ}{s:State}
 (h:D.Control k q A F T r stack depth index dimension finish flag s)(pc:ℕ):
 D.Control k q A F T r stack depth index dimension finish flag (setPC s pc):=
 ⟨h.cursor,h.nativeBase,h.original,h.bits,h.volume,h.frontier,h.rest,h.stack,h.depth,h.one,
  h.index,h.dimension,h.finish,h.flag,h.nativeBits,h.nativeRest,h.table,h.columns,h.width⟩

def directionMatrix (q w r:ℕ){old new:Label (w+1)}(edge:NestedEdge old new)(j:Fin edge.dimension):
 Matrix (Fin (2^(q*(w+1)+r))) (Fin (2^(q*(w+1)+r))) ℂ:=
 UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformNativeResidualSemantics.nativeWordMatrix (UniformResidualFibers.signedColumnWord q
   (edgeVectors edge j) (UniformResidualFibers.edgeVector_norm edge j) (edgeInverse edge)))
def action (q w r:ℕ){old new:Label (w+1)}(edge:NestedEdge old new)(L:List (Fin edge.dimension))
 (f:Fin (2^(q*(w+1)+r))→ℂ):Fin (2^(q*(w+1)+r))→ℂ:=
 L.foldl (fun y j=>(directionMatrix q w r edge j).mulVec y) f

def directionCost (q w r header:ℕ)(cost:ℕ→ℕ):ℕ:=
 header+18+UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16+
 UniformRecursiveBatchGroupMachine.groupCount q w r*(cost q+169)+1+1+13+7*(w+1)+
 max ((17*((w+1)+r)+35)*2^(q*(w+1)+r)+39) (10*2^(q*(w+1)+r)+12)+3

/-- The actual ascending basis loop uses only smaller executions of this same
Program as its recursive induction hypothesis. All current descriptor and
output banks are generated by the real instructions along the path. -/
theorem loop (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(index:ℕ)(L:List (Fin edge.dimension))
 (vis:Visit edge.dimension index L)(s:State)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
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
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+1:=by
 induction vis generalizing s X with
 | done=>
  let u:=setPC s (P.address .edgeDone)
  have run:BoundedRuns P.program n x B s 1 u:=by
   simpa only [Nat.lt_irrefl,ite_false] using UniformRecursiveResidualControl.direction_test n B edge.dimension edge.dimension x s pc h.index h.dimension bound code
  have fr:=setPC_frame s (P.address .edgeDone)
  refine ⟨u,1,X,run,setPC_pc s _,?_,fun _=>rfl,control_pc h _,?_,?_,?_,fr.2.2.1,fr.2.2.2,?_⟩
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
  obtain ⟨a,dt,Y,run,ap,yp,yv,ac,an,ash,ca,ar,ao,atime⟩:=UniformRecursiveResidualDirection.execution
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
  obtain ⟨u,ut,Z,ur,up,zp,zv,uc,un,ush,cu,uro,uo,utime⟩:=ih b Y bp bc printedB dataB cb nrun.final_bound
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
   uro.trans (br.trans (ar.trans readyFrame.2.2.1)),uo.trans (bo.trans (ao.trans readyFrame.2.2.2)),?_⟩
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

namespace ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
open OAI.ExactFourier BinaryFrames FramedScheduleWords UniformFixedNetwork
open UniformNativeResidualSemantics UniformNativeCopiedInverse
open scoped Kronecker
noncomputable section
lemma nativeWordMatrix_nil (k:ℕ):nativeWordMatrix (k:=k) []=1:=by
 unfold nativeWordMatrix
 simp only [wordMatrix,List.reverse_nil,List.map_nil,List.prod_nil]
 exact (Matrix.reindexAlgEquiv ℂ ℂ (originalToNative k)).map_one
lemma nativeWordMatrix_append {k:ℕ}(A B:List (WordStep C (2^k))):
 nativeWordMatrix (A++B)=nativeWordMatrix B*nativeWordMatrix A:=by
 unfold nativeWordMatrix
 rw [TypedKernelWords.wordMatrix_append]
 exact (Matrix.reindexAlgEquiv ℂ ℂ (originalToNative k)).map_mul _ _
lemma spectatorMatrix_one (k r:ℕ):spectatorMatrix k r (1:Matrix (Fin (2^k)) (Fin (2^k)) ℂ)=1:=by
 unfold spectatorMatrix
 rw [Matrix.one_kronecker_one]
 exact (Matrix.reindexAlgEquiv ℂ ℂ (spectatorSplit k r).symm).map_one
lemma spectatorMatrix_mul (k r:ℕ)(A B:Matrix (Fin (2^k)) (Fin (2^k)) ℂ):
 spectatorMatrix k r (A*B)=spectatorMatrix k r A*spectatorMatrix k r B:=by
 unfold spectatorMatrix
 rw [←PaddingWords.reindex_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul]

def signedWords (q:ℕ){n:ℕ}{old new:Label n}(edge:NestedEdge old new)(L:List (Fin edge.dimension)):=
 (L.map (fun j=>UniformResidualFibers.signedColumnWord q (edgeVectors edge j)
  (UniformResidualFibers.edgeVector_norm edge j) (edgeInverse edge))).flatten
lemma action_matrix (q w r:ℕ){old new:Label (w+1)}(edge:NestedEdge old new)
 (L:List (Fin edge.dimension))(f:Fin (2^(q*(w+1)+r))→ℂ):
 action q w r edge L f=
 (spectatorMatrix (q*(w+1)) r (nativeWordMatrix (signedWords q edge L))).mulVec f:=by
 induction L generalizing f with
 | nil=>simp [action,signedWords,nativeWordMatrix_nil,spectatorMatrix_one]
 | cons j L ih=>
  change action q w r edge L ((directionMatrix q w r edge j).mulVec f)=_
  rw [ih]
  simp only [signedWords,List.map_cons,List.flatten_cons,nativeWordMatrix_append,spectatorMatrix_mul]
  rw [←Matrix.mulVec_mulVec]
  rfl
lemma action_basis (q w r:ℕ){old new:Label (w+1)}(edge:NestedEdge old new)
 (f:Fin (2^(q*(w+1)+r))→ℂ):
 action q w r edge (List.finRange edge.dimension) f=
 (spectatorMatrix (q*(w+1)) r (nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))).mulVec f:=
 action_matrix q w r edge (List.finRange edge.dimension) f
end
end ExactFourierCircuits.UniformRecursiveResidualDirectionLoop
