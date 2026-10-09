import UniformRecursivePreparedGroup
import UniformRecursiveGroupBank
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveGroupLoop
open UniformMachine UniformBinaryTensorCoordinates UniformRecursivePreparedValues
noncomputable section
structure PreparedBank (q groups D doneCount:ℕ) (input:Fin groups→Fin W→Fin (2^q)→Scalar) (s:State) : Prop
 extends Bank q groups D doneCount input s where
 prepared:∀g:Fin groups,g.val<doneCount→Prepared2 (input g)→∀(j:Fin W)(t:Fin (2^q)),
  (s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)).map Scalar.dependent=some false
lemma PreparedBank.withPC {q groups D doneCount:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s:State}
 (h:PreparedBank q groups D doneCount input s) (pc:ℕ):PreparedBank q groups D doneCount input {s with pc:=pc}:=
 ⟨h.toBank.withPC pc,h.prepared⟩
lemma PreparedBank.initial {q groups D:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s:State}
 (h:∀(g:Fin groups)(j:Fin W)(t:Fin (2^q)),s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=some (input g j t)):
 PreparedBank q groups D 0 input s:=⟨Bank.initial h,fun _ h=>by omega⟩
lemma PreparedBank.advance {q groups D V F i:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s u:State}
 (old:PreparedBank q groups D i input s) (hi:i<groups) (partition:groups*(W*2^q)=V) (endptr:D+V≤F)
 (present:∀(j:Fin W)(t:Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).isSome=true)
 (values:∀(j:Fin W)(t:Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).map Scalar.value=
  some ((physicalMatrix q).mulVec (fun z=>(input ⟨i,hi⟩ j z).value) t))
 (frame:∀z,z<F→(z<D+i*(W*2^q)∨D+(i+1)*(W*2^q)≤z)→u.scalarHeap z=s.scalarHeap z)
 (prepared:Prepared2 (input ⟨i,hi⟩)→∀(j:Fin W)(t:Fin (2^q)),
  (u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).map Scalar.dependent=some false):
 PreparedBank q groups D (i+1) input u:=by
 refine ⟨old.toBank.advance hi partition endptr present values frame,?_⟩
 intro g processed prep j t
 by_cases eq:g.val=i
 · have same:g=⟨i,hi⟩:=Fin.ext eq
   subst g;exact prepared prep j t
 · rw [frame _ ((point_in_bank partition g j t).trans_le endptr) (other_group g j t eq)]
   exact old.prepared g (by omega) prep j t

lemma PreparedBank.complete {q groups D V:ℕ}{input:Fin groups→Fin W→Fin (2^q)→Scalar}{s:State}
 (partition:groups*(W*2^q)=V)(bank:PreparedBank q groups D groups input s)
 (prep:∀g,Prepared2 (input g)):
 Prepared (UniformRecursiveGroupBank.array D V s):=by
 intro z
 obtain ⟨⟨g,⟨i,t⟩⟩,eq⟩:=(UniformRecursiveGroupBank.flatten groups W (2^q) V partition).surjective z
 subst z
 have h:=bank.prepared g g.isLt (prep g) i t
 have read:=UniformRecursiveGroupBank.complete_array partition bank.toBank
  (UniformRecursiveGroupBank.flatten groups W (2^q) V partition (g,(i,t)))
 rw [UniformRecursiveGroupBank.flatten_value] at read
 simp only [Nat.add_assoc] at h read
 rw [read,Option.map_some] at h
 exact Option.some.inj h
theorem loop_prepared
 (remaining k q m r n B reserve D V A i groups stack depth stackTop F:ℕ)
 (cost:ℕ→ℕ) (x:Fin n→ℂ) (input:Fin groups→Fin W→Fin (2^q)→Scalar) (s:State)
 (ih:UniformRecursiveGroupExecution.PreparedSmallerBodies k n B reserve stack stackTop cost x) (smaller:q < k)
 (left:i+remaining=groups) (pc:s.pc=P.address .groupTest)
 (control:Control k q m r A D V F stack depth groups i s) (bank:PreparedBank q groups D i input s)
 (partition:groups*(W*2^q)=V) (dataBase:3 ≤ D) (dataEnd:D+V ≤ F)
 (stackRoom:stack+34*(depth+q+2) ≤ stackTop) (stackEnd:stackTop ≤ F)
 (room:F+reserve*(q+1)*2^q ≤ B) (square:(2^q)^2 ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s) (bound:WordBound B s) (code:P.program.length ≤ B):∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .inverseTest ∧
 Control k q m r A D V F stack depth groups groups u ∧ PreparedBank q groups D groups input u ∧
 (∀j∈UniformRecursiveReturnStackMachine.fields,j ≠ 4125→u.natReg j=s.natReg j) ∧
 Frame D V F stack depth stackTop s u ∧ UniformBinaryCStageMachine.Constants u ∧
 ticks ≤ remaining*(cost q+169)+1 ∧
 u.natReg 5300=(if remaining=0 then s.natReg 5300 else k) ∧
 u.natReg 5301=(if remaining=0 then s.natReg 5301 else r):=by
 induction remaining generalizing i s with
 | zero=>
   have eq:i=groups:=by omega
   subst i
   let u:State:={s with pc:=P.address .inverseTest}
   have branch:=UniformRecursiveBatchGroupMachine.branch_execution P.program (P.address .groupTest)
    (P.address .call) (P.address .inverseTest) n B groups groups x s UniformRecursiveGroupExecution.group_branch
    pc control.index control.count bound (UniformRecursiveParentReturn.start_bound .call B code)
    (UniformRecursiveParentReturn.start_bound .inverseTest B code)
   have run:BoundedRuns P.program n x B s 1 u:=by simpa only [lt_self_iff_false,ite_false] using branch
   exact ⟨u,1,run,rfl,control.withPC _,bank.withPC _,fun _ _ _=>rfl,
    ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩,constants_withPC constants _,by omega,rfl,rfl⟩
 | succ remaining induct=>
   have hi:i < groups:=by omega
   have data:∀(j:Fin W)(t:Fin (2^q)),s.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)=some (input ⟨i,hi⟩ j t):=
    bank.remaining ⟨i,hi⟩ (by rfl)
   obtain ⟨a,steps,run,ap,index,count,sp,dep,globalOne,fields,size,volume,one,bits,rest,present,values,scalar,nat,ac,out,roots,time,prepared⟩:=
    UniformRecursiveGroupExecution.one_group_prepared k q m r n B reserve D V A i groups stack depth stackTop F cost x s
     (input ⟨i,hi⟩) ih smaller pc control.index control.count control.columns control.size control.savedSize
     control.dataBase control.frontier control.stack control.depth control.bits control.rest control.original
     control.volume control.width control.nativeBase partition hi data dataBase dataEnd stackRoom stackEnd room square constants bound code
   have nextControl:=control.advance index sp dep globalOne size fields
   have nextBank:=bank.advance hi partition dataEnd present values scalar prepared
   have frame:=frame_of_group partition hi scalar nat out roots
   obtain ⟨u,tailTicks,tailRun,up,uc,ub,kept,uf,us,timeTail,nativeBits,nativeRest⟩:=induct (i+1) a (by omega) ap nextControl nextBank ac run.final_bound
   have keptAll:∀j∈UniformRecursiveReturnStackMachine.fields,j ≠ 4125→u.natReg j=s.natReg j:=by
    intro j hj ne
    exact (kept j hj ne).trans (by simpa only [ne,ite_false] using fields j hj)
   refine ⟨u,steps+tailTicks,run.trans tailRun,up,uc,ub,keptAll,frame.trans uf,us,?_,?_,?_⟩
   · rw [Nat.succ_mul];omega
   · simpa only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,ite_false] using
      nativeBits.trans (by split <;> simp_all)
   · simpa only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,ite_false] using
      nativeRest.trans (by split <;> simp_all)
end
end ExactFourierCircuits.UniformRecursiveGroupLoop
