import UniformRecursiveSmallBody
import UniformRecursivePreparedGroup
import UniformRecursiveGroupExecution
import UniformRecursiveActualRuntime
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSmallBody
open UniformMachine UniformBinaryTensorCoordinates
namespace P
export UniformRecursiveSavingProgram (program threshold)
end P
namespace S
export UniformRecursiveSelfCallMachine (W)
end S
noncomputable section

theorem execution_prepared (n B k A F stack stackTop depth reserve:ℕ)(x:Fin n→ℂ)
 (input:Fin S.W→Fin (2^k)→Scalar)(s:State)
 (thresholdFit:P.threshold≤reserve)(stackFit:34≤reserve)(small:k<P.threshold)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(size:s.natReg 4122=2^k)
 (frontier:s.natReg 4123=F)(sp:s.natReg 4150=stack)(dp:s.natReg 4151=depth)
 (data:∀(i:Fin S.W)(j:Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))
 (positive:1≤depth)(heapBase:3≤A)(arrayEnd:A+S.W*2^k≤F)
 (_stackRoom:stack+34*(depth+k+1)≤ stackTop)(_stackTop:stackTop≤F)
 (code:P.program.length≤B)(room:F+reserve*(k+1)*2^k≤B)(_square:(2^k)^2≤B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 UniformRecursiveGroupExecution.PreparedChildBody n B k A F stack stackTop depth
  (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit) x input s:=by
 have fb:F≤B:=by omega
 have literal:P.threshold≤B:=thresholdFit.trans (reserve_le room)
 have extent:A+S.W*2^k≤B:=arrayEnd.trans fb
 have countBound:S.W≤B:=by
  have h:=Nat.mul_le_mul_left S.W (show 1≤2^k from Nat.two_pow_pos k)
  simp only [Nat.mul_one] at h
  omega
 have present:∀w z,s.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k w.val+z.val)=some (input w z):=data
 obtain ⟨u,t,run,up,out,values,ef,frame,con,depthKeep,_,_,stackKeep⟩:=UniformRecursiveSmallEntry.execution
  n B k A F depth x s input pc bits base size frontier dp small present heapBase constants bound
  code literal countBound extent (stack_room stackFit room)
 have nonzero:depth≠0:=by omega
 rw [ite_eq_right nonzero] at up
 refine ⟨u,4+UniformRecursiveSmallBase.baseTicks S.W k,?_,up,
  (stackKeep nonzero).trans sp,depthKeep,?_,values,?_,?_,con,?_,?_,ticks_fit _ k small,?_⟩
 · simpa only [ite_eq_right nonzero] using run
 · intro i j
   change (u.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k i.val+j.val)).isSome=true
   rw [out i j]
   rfl
 · intro z _ _
   rw [frame.natHeap,ef.natHeap]
 · intro z _ hz
   exact (frame.scalarHeap z hz).trans (congrFun ef.scalarHeap z)
 · exact frame.outputs.trans ef.outputs
 · exact frame.roots.trans ef.roots

 · intro h i j
   change (u.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k i.val+j.val)).map Scalar.dependent=some false
   rw [out i j]
   exact congrArg some (UniformRecursivePreparedValues.batch (input i) (h i) j)
end
end ExactFourierCircuits.UniformRecursiveSmallBody
