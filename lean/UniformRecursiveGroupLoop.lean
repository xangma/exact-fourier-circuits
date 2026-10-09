import UniformRecursiveGroupExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveGroupLoop
open UniformMachine UniformBinaryTensorCoordinates
namespace G
export UniformRecursiveGroupExecution (SmallerBodies one_group_of_induction)
end G
namespace P
export UniformRecursiveSavingProgram (program address Part)
end P
abbrev W:=UniformRecursiveSelfCallMachine.W
noncomputable section

structure Control (k q m r A D V F stack depth groups i:ℕ) (s:State):Prop where
 index:s.natReg 4125=i
 count:s.natReg 4126=groups
 columns:s.natReg 4060=q
 size:s.natReg 4015=2^q
 savedSize:s.natReg 4124=2^q
 dataBase:s.natReg 4091=D
 frontier:s.natReg 4133=F
 stack:s.natReg 4150=stack
 depth:s.natReg 4151=depth
 one:s.natReg 4153=1
 bits:s.natReg 4120=k
 rest:s.natReg 4127=r
 original:s.natReg 4121=A
 volume:s.natReg 4122=V
 width:s.natReg 4061=m
 nativeBase:s.natReg 3300=A

lemma Control.withPC {k q m r A D V F stack depth groups i:ℕ} {s:State}
 (h:Control k q m r A D V F stack depth groups i s) (pc:ℕ):
 Control k q m r A D V F stack depth groups i {s with pc:=pc}:=
 ⟨h.index,h.count,h.columns,h.size,h.savedSize,h.dataBase,h.frontier,h.stack,h.depth,h.one,
  h.bits,h.rest,h.original,h.volume,h.width,h.nativeBase⟩

/-- A physical bank invariant: completed groups contain true tensor values;
unvisited groups retain their exact incoming Scalar flags. -/
structure Bank (q groups D doneCount:ℕ) (input:Fin groups→Fin W→Fin (2^q)→Scalar) (s:State):Prop where
 present:∀(g:Fin groups),g.val < doneCount→∀(j:Fin W)(t:Fin (2^q)),
  (s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)).isSome=true
 values:∀(g:Fin groups),g.val < doneCount→∀(j:Fin W)(t:Fin (2^q)),
  (s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)).map Scalar.value=
   some ((physicalMatrix q).mulVec (fun z=>(input g j z).value) t)
 remaining:∀(g:Fin groups),doneCount ≤ g.val→∀(j:Fin W)(t:Fin (2^q)),
  s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=some (input g j t)

lemma Bank.withPC {q groups D doneCount:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s:State}
 (h:Bank q groups D doneCount input s) (pc:ℕ):Bank q groups D doneCount input {s with pc:=pc}:=
 ⟨h.present,h.values,h.remaining⟩
lemma constants_withPC {s:State} (h:UniformBinaryCStageMachine.Constants s) (pc:ℕ):
 UniformBinaryCStageMachine.Constants {s with pc:=pc}:=h

lemma Bank.initial {q groups D:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s:State}
 (h:∀(g:Fin groups)(j:Fin W)(t:Fin (2^q)),s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=some (input g j t)):
 Bank q groups D 0 input s:=⟨fun _ h=>by omega,fun _ h=>by omega,fun g _=>h g⟩

lemma point_bounds (b T i j t:ℕ) (hj:j < b) (ht:t < T):
 i*(b*T) ≤ i*(b*T)+j*T+t ∧ i*(b*T)+j*T+t < (i+1)*(b*T):=by
 have small:j*T+t < (j+1)*T:=by rw [Nat.succ_mul];omega
 have up:(j+1)*T ≤ b*T:=Nat.mul_le_mul_right T (Nat.succ_le_of_lt hj)
 constructor
 · omega
 · rw [Nat.succ_mul]
   omega

lemma point_in_bank {q groups D V:ℕ} (partition:groups*(W*2^q)=V)
 (g:Fin groups)(j:Fin W)(t:Fin (2^q)):
 D+g.val*(W*2^q)+j.val*2^q+t.val < D+V:=by
 have h:=(point_bounds W (2^q) g.val j.val t.val j.isLt t.isLt).2
 have up:(g.val+1)*(W*2^q) ≤ V:=
  (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt g.isLt)).trans_eq partition
 omega

lemma other_group {q groups D i:ℕ} (g:Fin groups)(j:Fin W)(t:Fin (2^q)) (different:g.val  ≠  i):
 D+g.val*(W*2^q)+j.val*2^q+t.val < D+i*(W*2^q) ∨
 D+(i+1)*(W*2^q) ≤ D+g.val*(W*2^q)+j.val*2^q+t.val:=by
 have bounds:=point_bounds W (2^q) g.val j.val t.val j.isLt t.isLt
 rcases lt_or_gt_of_ne different with less|more
 · left
   have h:(g.val+1)*(W*2^q) ≤ i*(W*2^q):=Nat.mul_le_mul_right _ (Nat.succ_le_of_lt less)
   omega
 · right
   have h:(i+1)*(W*2^q) ≤ g.val*(W*2^q):=Nat.mul_le_mul_right _ (Nat.succ_le_of_lt more)
   omega

lemma Bank.advance {q groups D V F i:ℕ} {input:Fin groups→Fin W→Fin (2^q)→Scalar} {s u:State}
 (old:Bank q groups D i input s) (hi:i < groups) (partition:groups*(W*2^q)=V) (endptr:D+V ≤ F)
 (present:∀(j:Fin W)(t:Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).isSome=true)
 (values:∀(j:Fin W)(t:Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).map Scalar.value=
  some ((physicalMatrix q).mulVec (fun z=>(input ⟨i,hi⟩ j z).value) t))
 (frame:∀z,z < F→(z < D+i*(W*2^q)∨D+(i+1)*(W*2^q) ≤ z)→u.scalarHeap z=s.scalarHeap z):
 Bank q groups D (i+1) input u:=by
 have outside (g:Fin groups)(j:Fin W)(t:Fin (2^q))(ne:g.val  ≠  i):
  u.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val):=
  frame _ ((point_in_bank partition g j t).trans_le endptr) (other_group g j t ne)
 refine ⟨?_,?_,?_⟩
 · intro g processed j t
   by_cases eq:g.val=i
   · have same:g=⟨i,hi⟩:=Fin.ext eq
     subst g;exact present j t
   · rw [outside g j t eq]
     exact old.present g (by omega) j t
 · intro g processed j t
   by_cases eq:g.val=i
   · have same:g=⟨i,hi⟩:=Fin.ext eq
     subst g;exact values j t
   · rw [outside g j t eq]
     exact old.values g (by omega) j t
 · intro g fresh j t
   rw [outside g j t (by omega)]
   exact old.remaining g (by omega) j t

structure Frame (D V F stack depth stackTop:ℕ) (s u:State):Prop where
 scalar:∀z,z < F→(z < D∨D+V ≤ z)→u.scalarHeap z=s.scalarHeap z
 nat:∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
lemma Frame.refl (D V F stack depth stackTop:ℕ) (s:State):Frame D V F stack depth stackTop s s:=
 ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
lemma Frame.trans {D V F stack depth stackTop:ℕ} {s u v:State}
 (a:Frame D V F stack depth stackTop s u) (b:Frame D V F stack depth stackTop u v):
 Frame D V F stack depth stackTop s v:=
 ⟨fun z hz out=>(b.scalar z hz out).trans (a.scalar z hz out),
  fun z hz out=>(b.nat z hz out).trans (a.nat z hz out),b.outputs.trans a.outputs,b.roots.trans a.roots⟩
lemma Control.advance {k q m r A D V F stack depth groups i:ℕ} {s u:State}
 (c:Control k q m r A D V F stack depth groups i s)
 (index:u.natReg 4125=i+1) (sp:u.natReg 4150=stack) (dep:u.natReg 4151=depth) (globalOne:u.natReg 4153=1)
 (size:u.natReg 4015=2^q)
 (fields:∀j∈UniformRecursiveReturnStackMachine.fields,u.natReg j=if j=4125 then s.natReg j+1 else s.natReg j):
 Control k q m r A D V F stack depth groups (i+1) u:=by
 have keep(j:ℕ)(member:j∈UniformRecursiveReturnStackMachine.fields)(ne:j ≠ 4125):u.natReg j=s.natReg j:=by
  simpa only [ne,ite_false] using fields j member
 exact ⟨index,(keep 4126 (by decide) (by omega)).trans c.count,
  (keep 4060 (by decide) (by omega)).trans c.columns,size,
  (keep 4124 (by decide) (by omega)).trans c.savedSize,(keep 4091 (by decide) (by omega)).trans c.dataBase,
  (keep 4133 (by decide) (by omega)).trans c.frontier,sp,dep,globalOne,
  (keep 4120 (by decide) (by omega)).trans c.bits,(keep 4127 (by decide) (by omega)).trans c.rest,
  (keep 4121 (by decide) (by omega)).trans c.original,(keep 4122 (by decide) (by omega)).trans c.volume,
  (keep 4061 (by decide) (by omega)).trans c.width,(keep 3300 (by decide) (by omega)).trans c.nativeBase⟩

lemma frame_of_group {D V F stack depth stackTop q i groups:ℕ} {s u:State}
 (partition:groups*(W*2^q)=V) (hi:i < groups)
 (scalar:∀z,z < F→(z < D+i*(W*2^q)∨D+(i+1)*(W*2^q) ≤ z)→u.scalarHeap z=s.scalarHeap z)
 (nat:∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z)
 (out:u.outputs=s.outputs) (roots:u.rootOrders=s.rootOrders):Frame D V F stack depth stackTop s u:=by
 have ep:D+(i+1)*(W*2^q) ≤ D+V:=
  Nat.add_le_add_left ((Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)).trans_eq partition) D
 exact ⟨fun z hz away=>scalar z hz (by rcases away with h|h;left;omega;right;omega),nat,out,roots⟩

/-- The finite complete-W group loop executes real self-call and return
instructions, charging each comparison, stack save/load and resumed cursor.
This is an operational induction lemma; the final strong induction still
must prove its smaller-body hypothesis. -/
theorem loop_of_induction
 (remaining k q m r n B reserve D V A i groups stack depth stackTop F:ℕ)
 (cost:ℕ→ℕ) (x:Fin n→ℂ) (input:Fin groups→Fin W→Fin (2^q)→Scalar) (s:State)
 (ih:G.SmallerBodies k n B reserve stack stackTop cost x) (smaller:q < k)
 (left:i+remaining=groups) (pc:s.pc=P.address .groupTest)
 (control:Control k q m r A D V F stack depth groups i s) (bank:Bank q groups D i input s)
 (partition:groups*(W*2^q)=V) (dataBase:3 ≤ D) (dataEnd:D+V ≤ F)
 (stackRoom:stack+34*(depth+q+2) ≤ stackTop) (stackEnd:stackTop ≤ F)
 (room:F+reserve*(q+1)*2^q ≤ B) (square:(2^q)^2 ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s) (bound:WordBound B s) (code:P.program.length ≤ B):∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .inverseTest ∧
 Control k q m r A D V F stack depth groups groups u ∧ Bank q groups D groups input u ∧
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
   obtain ⟨a,steps,run,ap,index,count,sp,dep,globalOne,fields,size,volume,one,bits,rest,present,values,scalar,nat,ac,out,roots,time⟩:=
    G.one_group_of_induction k q m r n B reserve D V A i groups stack depth stackTop F cost x s
     (input ⟨i,hi⟩) ih smaller pc control.index control.count control.columns control.size control.savedSize
     control.dataBase control.frontier control.stack control.depth control.bits control.rest control.original
     control.volume control.width control.nativeBase partition hi data dataBase dataEnd stackRoom stackEnd room square constants bound code
   have nextControl:=control.advance index sp dep globalOne size fields
   have nextBank:=bank.advance hi partition dataEnd present values scalar
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
