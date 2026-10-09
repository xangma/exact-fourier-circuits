import UniformRecursivePreparedGroupLoop
import UniformRecursiveResidualChildren
import UniformRecursiveResidualFiberValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualChildren
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
namespace FV
export UniformRecursiveResidualFiberValues (input representative representative_value)
end FV
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
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B)
 (_low:3 ≤ F)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (recordAbove:stackTop ≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .inverseTest ∧
 UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
  (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
  (BG.groupCount q w r) (BG.groupCount q w r) u ∧
 UniformRecursiveGroupLoop.Bank q (BG.groupCount q w r) (F+4*2^(q*(w+1)+r))
  (BG.groupCount q w r) (FV.input q w r fits (edgeVectors edge j) p hp X) u ∧
 (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val)) ∧
 UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u ∧
 (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→u.scalarHeap z=s.scalarHeap z) ∧
 u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r) ∧
 u.natReg 4067=F+2*2^(q*(w+1)+r) ∧ u.natReg 4068=F+3*2^(q*(w+1)+r) ∧
 u.natReg 4062=T+8+j.val*(w+1) ∧
 UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u ∧
 u.natReg 2850=T ∧ u.natReg 4123=F ∧ u.natReg 4134=j.val ∧
 u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length ∧
 u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse ∧ u.natReg 4132=edge.dimension ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16+
  BG.groupCount q w r*(cost q+169)+1 ∧
 u.natReg 5300=q*(w+1)+r ∧ u.natReg 5301=r ∧ u.natReg 3389=s.natReg 3389 ∧
 (UniformRecursivePreparedValues.Prepared X→UniformRecursivePreparedValues.Prepared
  (UniformRecursiveGroupBank.array (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) u)):=by
 obtain ⟨p,hp,a,gt,gr,gpc,gc,gdata,goutside,gperm,gentries,gnat,gdst,gpermptr,gxorptr,gkeep,
  gend,ginv,gdim,gro,gout,gdir,gsource,gtime⟩:=UniformRecursiveResidualBoot.execution n B T nRoles R A F q w r stack depth
  x s emb role edge j X pc cursor printed index base original bits volume frontier rest st dp one data qp m2 rp fits bound code
  recordEnd widthBound arrayEnd poolEnd square
 have grouped:∀(g:Fin (BG.groupCount q w r))(i:Fin BG.W)(t:Fin (2^q)),
  a.scalarHeap (F+4*2^(q*(w+1)+r)+g.val*(BG.W*2^q)+i.val*2^q+t.val)=
   some (FV.input q w r fits (edgeVectors edge j) p hp X g i t):=by
  intro g i t
  have h:=gdata (FV.representative q w r fits (g,i)) t
  simpa only [FV.input,FV.representative_value,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h
 have ca:UniformBinaryCStageMachine.Constants a:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  exact ⟨(goutside 1 (Or.inl (by omega))).trans constants.1,(goutside 2 (Or.inl (by omega))).trans constants.2⟩
 have childSquare:(2^q)^2 ≤ B:=by
  have exp:q ≤ q*(w+1)+r:=Nat.le_of_lt smaller
  have pow:=Nat.pow_le_pow_right (by omega:1 ≤ 2) exp
  exact (Nat.pow_le_pow_left pow 2).trans square
 obtain ⟨u,steps,run,up,control,bank,kept,frame,cu,time,nativeBits,nativeRest⟩:=UniformRecursiveGroupLoop.loop_prepared
  (BG.groupCount q w r) (q*(w+1)+r) q (w+1) r n B reserve (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) A
  0 (BG.groupCount q w r) stack depth stackTop (F+5*2^(q*(w+1)+r)) cost x (FV.input q w r fits (edgeVectors edge j) p hp X) a
  ih smaller (by omega) gpc gc (UniformRecursiveGroupLoop.PreparedBank.initial grouped) (BG.partition q w r fits)
  (by omega) (by omega) stackRoom (by omega) room childSquare ca gr.final_bound code
 have nonempty:BG.groupCount q w r≠0:=by
  intro zero
  have part:=BG.partition q w r fits
  rw [zero,Nat.zero_mul] at part
  have positive:0<2^(q*(w+1)+r):=by positivity
  omega
 have reg(z:ℕ)(hz:z∈UniformRecursiveReturnStackMachine.fields)(ne:z≠4125):u.natReg z=a.natReg z:=kept z hz ne
 have physical:∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val):=by
  intro z
  rw [frame.nat _ (by have h:=z.isLt;omega) (Or.inr (by omega))]
  exact gperm z
 have smallTable:2^q*2^q ≤ 2^(q*(w+1)+r):=UniformRecursiveResidualGatherRecordMachine.table_fits q (w+1) r m2
 have entries:UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u:=by
  intro z hz
  rw [frame.nat _ (by omega) (Or.inr (by omega))]
  exact gentries z hz
 have source:UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u:=by
  intro z
  have dirEnd:=UniformRecursiveResidualGatherRecordMachine.direction_end T edge.dimension (w+1) j.val F j.isLt
   (by simpa only [UniformFixedNetworkScheduleMachine.Record.data_length,macroRecord,UniformFixedNetworkScheduleMachine.edgeBits_length,Nat.add_assoc] using recordEnd)
  rw [frame.nat _ (by have h:=z.isLt;omega) (Or.inr (by omega))]
  exact gsource z
 refine ⟨p,hp,u,gt+steps,gr.trans run,up,control,bank.toBank,physical,entries,?_,?_,
  (reg _ (by decide) (by omega)).trans gdst,(reg _ (by decide) (by omega)).trans gpermptr,
  (reg _ (by decide) (by omega)).trans gxorptr,(reg _ (by decide) (by omega)).trans gdir,source,
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans cursor),
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans frontier),
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans index),
  (reg _ (by decide) (by omega)).trans gend,(reg _ (by decide) (by omega)).trans ginv,
  (reg _ (by decide) (by omega)).trans gdim,cu,frame.roots.trans gro,frame.outputs.trans gout,?_,?_,?_,?_,?_⟩
 · intro z hz away;exact (frame.nat z (by omega) away).trans (gnat z hz)
 · intro z hz;exact (frame.scalar z (by omega) (Or.inl (by omega))).trans (goutside z (Or.inl (by omega)))
 · omega
 · simpa only [nonempty,ite_false] using nativeBits
 · simpa only [nonempty,ite_false] using nativeRest
 · exact (reg _ (by decide) (by omega)).trans (gkeep _ (by decide))
 · intro prep
   apply bank.complete (BG.partition q w r fits)
   intro g i t
   exact prep _
end
end ExactFourierCircuits.UniformRecursiveResidualChildren
