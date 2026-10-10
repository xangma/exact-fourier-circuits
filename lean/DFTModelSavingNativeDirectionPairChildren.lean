import DFTModelSavingNativeDirectionChildren

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

theorem paired_children (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (I:ℂ) (handler:Handler DFTModelSavingResidual.Port)
 (ih:DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
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
 (low:3 ≤ F)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (recordAbove:stackTop ≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B)
 (X0:Fin (2^(q*(w+1)+r))→Scalar) (s0:State) (same:StateMatch s s0)
 (data0:∀z,s0.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X0 z)) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u u0 ticks,
 ChildrenResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j X p hp fits s u ticks ∧
 ChildrenResult n B T nRoles R A F q w r stack depth stackTop cost (fun _=>0) emb role edge j X0 p hp fits s0 u0 ticks ∧
 StateMatch u u0 ∧
 DFTModelSavingResidualNativeGroup.PairBank q (BG.groupCount q w r) (F+4*2^(q*(w+1)+r))
  (BG.groupCount q w r) I handler (FV.input q w r fits (edgeVectors edge j) p hp X)
   (FV.input q w r fits (edgeVectors edge j) p hp X0) u u0 := by
 obtain ⟨p,hp,a,a0,gt,br,br0,matchedBoot⟩:=paired_boot n B T nRoles R A F q w r stack depth x s emb role edge j X
  pc cursor printed index base original bits volume frontier rest st dp one data qp m2 rp fits bound code
  recordEnd widthBound arrayEnd poolEnd square X0 s0 same data0
 have grouped:∀(g:Fin (BG.groupCount q w r))(i:Fin BG.W)(t:Fin (2^q)),
  a.scalarHeap (F+4*2^(q*(w+1)+r)+g.val*(BG.W*2^q)+i.val*2^q+t.val)=
   some (FV.input q w r fits (edgeVectors edge j) p hp X g i t):=by
  intro g i t
  have val:=br.data (FV.representative q w r fits (g,i)) t
  simpa only [FV.input,FV.representative_value,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using val
 have grouped0:∀(g:Fin (BG.groupCount q w r))(i:Fin BG.W)(t:Fin (2^q)),
  a0.scalarHeap (F+4*2^(q*(w+1)+r)+g.val*(BG.W*2^q)+i.val*2^q+t.val)=
   some (FV.input q w r fits (edgeVectors edge j) p hp X0 g i t):=by
  intro g i t
  have val:=br0.data (FV.representative q w r fits (g,i)) t
  simpa only [FV.input,FV.representative_value,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using val
 have ca:UniformBinaryCStageMachine.Constants a:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  exact ⟨(br.outside 1 (Or.inl (by omega))).trans constants.1,
   (br.outside 2 (Or.inl (by omega))).trans constants.2⟩
 have childSquare:(2^q)^2≤B:=by
  have exp:q≤q*(w+1)+r:=Nat.le_of_lt smaller
  have power:=Nat.pow_le_pow_right (by omega:1≤2) exp
  exact (Nat.pow_le_pow_left power 2).trans square
 obtain ⟨u,u0,steps,run,run0,last,up,control,pairBank,kept,frame,frame0,cu,time,nativeBits,nativeRest⟩:=
  DFTModelSavingResidualNativeGroup.pair_loop (BG.groupCount q w r) (q*(w+1)+r) q (w+1) r n B reserve
   (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) A 0 (BG.groupCount q w r) stack depth stackTop
   (F+5*2^(q*(w+1)+r)) cost x I handler (FV.input q w r fits (edgeVectors edge j) p hp X)
   (FV.input q w r fits (edgeVectors edge j) p hp X0) a a0 ih smaller matchedBoot (by omega) br.pc br.control
   (DFTModelSavingResidualNativeGroup.PairBank.initial grouped grouped0) (UniformRecursiveBatchGroupMachine.partition q w r fits)
   (by omega) (by omega) stackRoom (by omega) room childSquare ca br.run.final_bound code
 have nonempty:BG.groupCount q w r≠0:=Nat.ne_of_gt (UniformRecursiveBatchGroupMachine.groupCount_positive q w r)
 have native:u.natReg 5300=q*(w+1)+r:=by simpa only [nonempty,ite_false] using nativeBits
 have nativeR:u.natReg 5301=r:=by simpa only [nonempty,ite_false] using nativeRest
 have aResult:=children_of_loop n B T nRoles R A F q w r stack depth stackTop cost x s emb role edge j X p hp fits a u gt steps
  br run up control pairBank.actual kept frame cu time native nativeR cursor frontier index m2 recordEnd stackEnd recordAbove
 have kept0:∀z∈UniformRecursiveReturnStackMachine.fields,z≠4125→u0.natReg z=a0.natReg z:=by
  intro z hz ne
  exact (congrFun last.natReg z).trans ((kept z hz ne).trans (congrFun matchedBoot.natReg z).symm)
 have zResult:=children_of_loop n B T nRoles R A F q w r stack depth stackTop cost (fun _=>0) s0 emb role edge j X0 p hp fits a0 u0 gt steps
  br0 run0 (last.pc.trans up) (DFTModelSavingResidualNativeGroup.control_match control last) pairBank.zero kept0 frame0
  (DFTModelSavingResidualNativeGroup.constants_match last cu) time
  ((congrFun last.natReg 5300).trans native) ((congrFun last.natReg 5301).trans nativeR)
  (by rw [same.natReg];exact cursor) (by rw [same.natReg];exact frontier) (by rw [same.natReg];exact index)
  m2 recordEnd stackEnd recordAbove
 exact ⟨p,hp,u,u0,gt+steps,aResult,zResult,last,pairBank⟩

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
