import UniformRecursiveChildPackage
import UniformRecursiveLargeNode
import UniformRecursiveBodyGeometry
import UniformRecursiveReserve
import UniformRecursiveSmallEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveLargeChild
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformRecursiveNodePreparation
open UniformRecursiveGroupExecution (ChildBody SmallerBodies)
namespace P
export UniformRecursiveSavingProgram (program address threshold seedLength unitLength seedPrinterLength unitPrinterLength size)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable section

lemma native_return (depth pc:ℕ)
 (h:pc=(if depth=0 then UniformRecursiveLargeNode.P.address .halt else UniformRecursiveLargeNode.P.address .returnSite))
 (nz:depth≠0):pc=UniformRecursiveGroupExecution.P.address .returnSite:=by
 rw [ite_eq_right nz] at h
 exact h

lemma cost_trans (ticks named body cap:ℕ)(h:ticks ≤ 9+named+body)(fit:13+named+body ≤ cap):
 4+ticks ≤ cap:=by omega

/-- Positive-depth large child, from the actual common entry. The arithmetic
bound is separate from execution and is discharged by the fixed runtime reserve. -/
theorem execution (n B A F q rest stack stackTop depth:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (input:Fin W→Fin (2^(q*m+rest))→Scalar)(s:State)
 (childIH:SmallerBodies (q*m+rest) n B R.reserve stack stackTop cost x)
 (large:P.threshold ≤ q*m+rest)(qp:1 ≤ q)(rp:rest < m)(smaller:q < q*m+rest)
 (pc:s.pc=0)(bits:s.natReg 4120=q*m+rest)(base:s.natReg 4121=A)(size:s.natReg 4122=2^(q*m+rest))
 (frontier:s.natReg 4123=F)(sp:s.natReg 4150=stack)(dp:s.natReg 4151=depth)
 (data:∀i z,s.scalarHeap (A+i.val*2^(q*m+rest)+z.val)=some (input i z))
 (positive:1 ≤ depth)(heapBase:3 ≤ A)(extent:A+W*2^(q*m+rest) ≤ F)
 (stackRoom:stack+34*(depth+(q*m+rest)+1) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (code:P.program.length ≤ B)(room:F+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
 (square:(2^(q*m+rest))^2 ≤ B)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (timeBound:13+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)+
  UniformRecursivePrintedBody.bodyTicks q rest cost ≤ cost (q*m+rest)):
 ChildBody n B (q*m+rest) A F stack stackTop depth cost x input s:=by
 have nonzero:depth≠0:=by omega
 have stackExtent:=UniformRecursiveReserve.stack_room room
 obtain ⟨t,entry,tp,nk,na,tk,ta,tv,td,oneHeader,tf,_,ef⟩:=UniformRecursiveSavingExecution.entry_execution
  n B (q*m+rest) A (2^(q*m+rest)) F depth x s pc bits base size frontier dp bound code stackExtent
 have entry4:BoundedRuns P.program n x B s 4 t:=by simpa only [nonzero,ite_false] using entry
 have current:t.natReg 4123=F:=by simpa only [nonzero,ite_false] using tf
 have stackHeader:t.natReg 4150=stack:=(UniformRecursiveSmallEntry.nonroot_stack n B (q*m+rest) A depth x s t
  pc bits base dp bound code nonzero entry4).trans sp
 have incoming:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest)) input t:=by
  intro i z;rw [ef.scalarHeap];exact data i z
 have ct:UniformBinaryCStageMachine.Constants t:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  rw [ef.scalarHeap];exact constants
 have rb:R.reserve ≤ B:=UniformRecursiveBodyGeometry.reserve_le room
 have fit:=UniformRecursiveReserve.payload_fit
 have geom:=UniformRecursiveBodyGeometry.geometry B A F P.seedLength P.unitLength q rest stack depth stackTop R.reserve
  qp rp smaller fit UniformRecursiveReserve.width_fit room extent heapBase stackRoom square code
 obtain ⟨u,ticks,g,run,up,out,values,us,ud,nh,sh,cu,roots,outputs,ticksBound⟩:=UniformRecursiveLargeNode.execution
  n B F P.seedLength P.unitLength A q rest stack depth stackTop R.reserve F cost x t input rfl rfl childIH geom large
  (UniformRecursiveReserve.threshold_fit.trans rb) tp tk ta tv current na nk stackHeader td oneHeader incoming stackEnd (by omega)
  (UniformRecursiveReserve.literals_fit.trans rb) ct entry4.final_bound
 have finalPC:=native_return depth u.pc up nonzero
 exact UniformRecursiveChildPackage.execution n B (q*m+rest) A F stack stackTop depth cost x input g s t u ticks
  entry4 run finalPC us ud out values nh sh cu outputs roots ef (cost_trans ticks _ _ _ ticksBound timeBound)
end
end ExactFourierCircuits.UniformRecursiveLargeChild
