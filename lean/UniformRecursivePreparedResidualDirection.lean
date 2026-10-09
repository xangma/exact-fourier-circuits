import UniformRecursivePreparedResidualChildren
import UniformRecursiveResidualDirection
import UniformRecursiveResidualSignedValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualDirection
open UniformMachine BinaryFrames UniformBinaryTensorCoordinates
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
namespace P
export UniformRecursiveSavingProgram (Part program address)
end P
namespace BG
export UniformRecursiveBatchGroupMachine (groupCount W partition)
end BG
namespace O
export UniformRecursiveResidualOutput (execution Frame)
end O
noncomputable section
theorem execution_prepared (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (ih:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q < q*(w+1)+r)(pc:s.pc=P.address .gather)(cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val)(base:s.natReg 3300=A)(original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r)(volume:s.natReg 4122=2^(q*(w+1)+r))
 (frontier:s.natReg 4123=F)(rest:s.natReg 4127=r)(st:s.natReg 4150=stack)
 (dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (table:s.natReg 3389=F+3*2^(q*(w+1)+r))
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B)
 (low:3 ≤ F)(dataBase:3 ≤ A)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (recordAbove:stackTop ≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B) :
 ∃u ticks,∃Y:Fin (2^(q*(w+1)+r))→Scalar,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .directionNext ∧
 (∀z,u.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (Y z)) ∧
 (∀z,(Y z).value=
  (UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
   (UniformNativeResidualSemantics.nativeWordMatrix
    (UniformResidualFibers.signedColumnWord q (edgeVectors edge j)
     (UniformResidualFibers.edgeVector_norm edge j) (edgeInverse edge)))).mulVec
   (fun y=>(X y).value) z) ∧
 Control (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length)
  (macroRecord q emb (.edge old new role edge)).inverse u ∧
 (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A+(emb role).val*2^(q*(w+1)+r)∨
  A+((emb role).val+1)*2^(q*(w+1)+r) ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16+
  BG.groupCount q w r*(cost q+169)+1+1+
  UniformResidualOrientationMachine.ticks (edgeVectors edge j)+
  (if UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge)
   then (17*((w+1)+r)+35)*2^(q*(w+1)+r)+39 else 10*2^(q*(w+1)+r)+12) ∧
 (UniformRecursivePreparedValues.Prepared X→UniformRecursivePreparedValues.Prepared Y):=by
 obtain ⟨p,hp,a,ct,cr,ap,ac,bank,physical,entries,nh,sh,dest,permptr,xorptr,dirptr,direction,
  cur,work,idx,finish,raw,dim,ca,roots,outputs,cbound,nativeBits,nativeRest,tableKeep,prepared⟩:=UniformRecursiveResidualChildren.execution_prepared
  n B T nRoles R A F q w r stack depth stackTop reserve cost x s emb role edge j X
  ih smaller pc cursor printed index base original bits volume frontier rest st dp one data qp m2 rp fits
  recordEnd widthBound arrayEnd poolEnd square low stackRoom stackEnd recordAbove room constants bound code
 have dEnd:=UniformRecursiveResidualGatherRecordMachine.direction_end T edge.dimension (w+1) j.val F j.isLt
  (by simpa only [UniformFixedNetworkScheduleMachine.Record.data_length,macroRecord,
   UniformFixedNetworkScheduleMachine.edgeBits_length,Nat.add_assoc] using recordEnd)
 have dstEnd:=UniformRecursiveResidualGatherRecordMachine.data_end A R (2^(q*(w+1)+r))
  (emb role).val F (emb role).isLt arrayEnd
 have rawFlag:a.natReg 4131=(if edgeInverse edge then 1 else 0):=raw
 have tableFit:=UniformRecursiveResidualGatherRecordMachine.table_fits q (w+1) r m2
 have present:=UniformRecursiveGroupBank.complete_array (BG.partition q w r fits) bank
 obtain ⟨u,run,up,scatter,fr⟩:=O.execution n B (q*(w+1)+r) q (w+1) r
  (F+4*2^(q*(w+1)+r)) (A+(emb role).val*2^(q*(w+1)+r))
  (F+2*2^(q*(w+1)+r)) (F+3*2^(q*(w+1)+r)) (T+8+j.val*(w+1))
  (edgeInverse edge) (edgeVectors edge j) (UniformResidualFibers.edgeVector_norm edge j) x a
  ap ac.one rawFlag dirptr direction (by omega) ac.bits ac.volume ac.savedSize ac.dataBase dest ac.width ac.rest permptr xorptr
  rfl qp rp (Nat.le_of_lt smaller)
  (UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp))
  physical (UniformRecursiveGroupBank.array (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) a) present entries
  (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) square cr.final_bound code
 have sv:=UniformRecursiveResidualSignedValues.scatter_signed q w r (F+4*2^(q*(w+1)+r))
  (A+(emb role).val*2^(q*(w+1)+r)) fits (Nat.le_of_lt smaller) (edgeVectors edge j)
  (UniformResidualFibers.edgeVector_norm edge j) p hp (edgeInverse edge) X a u bank scatter
 let Y:=UniformRecursiveGroupBank.array (A+(emb role).val*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) u
 have yp:∀z,u.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (Y z):=
  UniformRecursiveGroupBank.array_present (fun z=>(sv z).1)
 have keep(i:ℕ)(hi:¬UniformRecursiveResidualInverse.InverseChanged i)
  (hs:¬UniformRecursiveResidualFinish.ScatterChanged i)(hc:¬UniformResidualOrientationMachine.Changed i):u.natReg i=a.natReg i:=fr.natReg i hi hs hc
 have keepParent(i:ℕ)(hi:i=2850∨i=3300∨i=4120∨i=4121∨i=4122∨i=4123∨i=4127∨i=4130∨i=4131∨i=4132∨i=4134∨i=4150∨i=4151∨i=4153∨i=3389∨i=4060∨i=4061):u.natReg i=a.natReg i:=by
  apply keep
  all_goals simp only [UniformRecursiveResidualInverse.InverseChanged,UniformRecursiveResidualInverse.SetupChanged,
    UniformResidualNativeTranslationMachine.Changed,UniformRecursiveResidualFinish.ScatterChanged,
    UniformRecursiveResidualFinish.SetupChanged,UniformResidualOrientationMachine.Changed];omega
 have originalWidth:(q*(w+1)+r-r)/q=w+1:=by
  rw [Nat.add_sub_cancel_right]
  exact Nat.mul_div_right (w+1) (by omega)
 have control:Control (q*(w+1)+r) q A F T r stack depth j.val edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length)
  (macroRecord q emb (.edge old new role edge)).inverse u:=
  ⟨(keepParent _ (by omega)).trans cur,(keepParent _ (by omega)).trans ac.nativeBase,
   (keepParent _ (by omega)).trans ac.original,(keepParent _ (by omega)).trans ac.bits,
   (keepParent _ (by omega)).trans ac.volume,(keepParent _ (by omega)).trans work,
   (keepParent _ (by omega)).trans ac.rest,(keepParent _ (by omega)).trans ac.stack,
   (keepParent _ (by omega)).trans ac.depth,(keepParent _ (by omega)).trans ac.one,
   (keepParent _ (by omega)).trans idx,(keepParent _ (by omega)).trans dim,
   (keepParent _ (by omega)).trans finish,(keepParent _ (by omega)).trans raw,
   (fr.nativeBits (nativeBits.trans ac.bits.symm)).trans ac.bits,
   (fr.nativeRest (nativeRest.trans ac.rest.symm)).trans ac.rest,
   (keepParent _ (by omega)).trans (tableKeep.trans table),
   (keepParent _ (by omega)).trans ac.columns,
   ((keepParent _ (by omega)).trans ac.width).trans originalWidth.symm⟩
 have uc:UniformBinaryCStageMachine.Constants u:=by
  unfold UniformBinaryCStageMachine.Constants at ca ⊢
  exact ⟨(fr.scalarHeap 1 (Or.inl (by omega)) (Or.inl (by omega))).trans ca.1,
   (fr.scalarHeap 2 (Or.inl (by omega)) (Or.inl (by omega))).trans ca.2⟩
 refine ⟨u,ct+(1+UniformResidualOrientationMachine.ticks (edgeVectors edge j)+
  if UniformResidualFibers.inverseOrientation (edgeVectors edge j) (edgeInverse edge)
  then (17*((w+1)+r)+35)*2^(q*(w+1)+r)+39 else 10*2^(q*(w+1)+r)+12),Y,
  cr.trans run,up,yp,?_,control,?_,?_,uc,fr.roots.trans roots,fr.outputs.trans outputs,?_,?_⟩
 · intro z
   have h:=(sv z).2
   rw [yp z,Option.map_some] at h
   exact Option.some.inj h
 · intro z hz away;rw [fr.natHeap];exact nh z hz away
 · intro z hz away
   exact (fr.scalarHeap z (Or.inl (by omega)) (by have h:=away;rw [Nat.add_mul] at h;omega)).trans (sh z hz)
 · omega
 · intro prep z
   obtain ⟨a,eq⟩:=(UniformResidualSpectators.extend (q*(w+1)) r
    (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp)).surjective z
   have val:=scatter a
   rw [eq,yp z] at val
   have same:=Option.some.inj val
   rw [same]
   exact UniformRecursivePreparedValues.selected (Nat.le_of_lt smaller) _ _ (prepared prep) a
end
end ExactFourierCircuits.UniformRecursiveResidualDirection
