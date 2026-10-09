import UniformRecursiveParentReturn
import UniformNativeCopiedInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveGroupExecution
open UniformMachine UniformAssembly UniformBinaryTensorCoordinates
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace P
export UniformRecursiveSavingProgram (Part program address size)
end P
namespace S
export UniformRecursiveSelfCallMachine (W)
end S
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace Stack
export UniformRecursiveReturnStackMachine (fields Bank)
end Stack
noncomputable section

/-- Operational induction motive for a positive-depth child. It names the
same literal Program, not an arbitrary transform callback. The lower stack
and all earlier external banks are explicitly retained. -/
def ChildBody (n B k A F stack stackTop depth : ℕ) (cost:ℕ→ℕ) (x : Fin n→ℂ)
 (input : Fin S.W→Fin (2^k)→Scalar) (s : State) : Prop := ∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .returnSite ∧
 u.natReg 4150=stack ∧ u.natReg 4151=depth ∧
 (∀(i:Fin S.W) (j:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+j.val)).isSome=true) ∧
 (∀(i:Fin S.W) (j:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+j.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun z=>(input i z).value) j)) ∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z<F→(z<A∨A+S.W*2^k≤z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ticks≤cost k

/-- Only the well-founded induction will discharge this proposition: every
smaller exponent executes this exact Program from its physically installed
headers. No arbitrary handler, matrix-action or returned-bank premise occurs
inside the child entry contract. -/
def SmallerBodies (parent n B reserve stack stackTop : ℕ) (cost:ℕ→ℕ) (x : Fin n→ℂ) : Prop :=
 ∀k,k<parent→∀(A F depth:ℕ) (input:Fin S.W→Fin (2^k)→Scalar) (s:State),
 s.pc=0→s.natReg 4120=k→s.natReg 4121=A→s.natReg 4122=2^k→s.natReg 4123=F→
 s.natReg 4150=stack→s.natReg 4151=depth→
 (∀(i:Fin S.W) (j:Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))→
 1≤depth→3≤A→A+S.W*2^k≤F→stack+34*(depth+k+1) ≤ stackTop→stackTop ≤ F→
 P.program.length≤B→F+reserve*(k+1)*2^k≤B→(2^k)^2≤B→
 UniformBinaryCStageMachine.Constants s→WordBound B s→ChildBody n B k A F stack stackTop depth cost x input s

lemma zero_cell (p:Program) (start:ℕ) (value:Instruction) (rhs:Program)
 (h:p[start+0]?=rhs[0]?) (cell:rhs[0]?=some value) : p[start]?=some value:=by
 simpa only [Nat.add_zero] using h.trans cell
lemma group_branch : P.program[P.address .groupTest]?=
 some (.branchLT 4125 4126 (P.address .call) (P.address .inverseTest)):=
 zero_cell P.program (P.address .groupTest) _ _
  (UniformRecursiveSavingExecution.part_at .groupTest 0 (by decide)) rfl

open UniformRecursiveSelfCallMachine

theorem call_with_stack (p:Program) (start n B q T D V i groups stack depth frontier:ℕ)
 (x:Fin n→ℂ) (s:State) (code:CallAt p start) (pc:s.pc=start)
 (hq:s.natReg 4060=q) (size:s.natReg 4015=T) (tp:0<T)
 (dataBase:s.natReg 4091=D) (index:s.natReg 4125=i) (fresh:s.natReg 4133=frontier)
 (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (partition:groups*(W*T)=V) (hi:i<groups) (dataEnd:D+V≤B)
 (bound:WordBound B s) (extent:start+83≤B) (stackEnd:stack+34*(depth+1)≤B) :
 ∃u,BoundedRuns p n x B s 83 u ∧ u.pc=0 ∧
 u.natReg 4120=q ∧ u.natReg 4121=D+i*(W*T) ∧ u.natReg 4122=T ∧ u.natReg 4123=frontier ∧
 u.natReg 4150=stack ∧ u.natReg 4151=depth+1 ∧ Stack.Bank Stack.fields (stack+34*depth) s.natReg u ∧
 (∀z,z<stack+34*depth∨stack+34*(depth+1)≤z→u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mulB:=UniformRecursiveBaseCallMachine.product_bound stack depth B stackEnd
 have ptrB:=UniformRecursiveBaseCallMachine.frame_base_bound stack depth B stackEnd
 have endB:=UniformRecursiveBaseCallMachine.frame_extent stack depth B stackEnd
 have depthB:=UniformRecursiveBaseCallMachine.depth_bound stack depth B stackEnd
 have safe:readable UniformRecursiveBaseCallMachine.pushSetup s ∧ peak UniformRecursiveBaseCallMachine.pushSetup s≤B:=by
  simp [UniformRecursiveBaseCallMachine.pushSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,sp,dp,ptrB]
  omega
 have push:=block_runs UniformRecursiveBaseCallMachine.pushSetup p start n B x s (push_code code) pc bound
  (by change start+4≤B;omega) safe.1 safe.2
 let installed:=applyBlock UniformRecursiveBaseCallMachine.pushSetup s
 let child:State:={installed with pc:=0}
 have ib:=changePC_bound B installed 0 push.final_bound (by omega)
 have ptr:child.natReg 4152=stack+34*depth:=by simp [child,installed,UniformRecursiveBaseCallMachine.pushSetup,applyBlock,Op.apply,evalNat,writeNat,next,sp,dp,Nat.mul_comm]
 have one:child.natReg 4153=1:=by simp [child,installed,UniformRecursiveBaseCallMachine.pushSetup,applyBlock,Op.apply,evalNat,writeNat,next]
 obtain ⟨saved,sr,savedPC,bank,savedPtr,nh,nr,sh,ss,ou,ro⟩:=UniformRecursiveReturnStackMachine.save_execution
  n B (stack+34*depth) x child rfl ptr one ib (by omega) endB
 have halt:BoundedExecution Stack.saveProgram n x B child 69 saved:=by
  convert sr.executes (.halt sr.final_bound (by simp [step,savedPC,UniformRecursiveBaseCallMachine.save_halt])) using 1
 have save:=UniformBoundedAssembly.boundedExecution_placed (save_code code) (by change start+4+69≤B;omega) (by omega) halt
 have ip:installed.pc=start+4:=by simp [installed,UniformRecursiveBaseCallMachine.pushSetup,applyBlock,Op.apply,writeNat,next,pc] <;> omega
 have same:placed (start+4) child=installed:=by change {installed with pc:=start+4}=installed;rw [←ip]
 rw [same] at save
 let atInc:State:={saved with pc:=start+73}
 have dnow:saved.natReg 4151=depth:=by simpa [child,installed,UniformRecursiveBaseCallMachine.pushSetup,applyBlock,Op.apply,evalNat,writeNat,next,dp] using nr 4151 (by omega)
 have onow:saved.natReg 4153=1:=(nr _ (by omega)).trans one
 have incSafe:readable UniformRecursiveBaseCallMachine.increment atInc ∧ peak UniformRecursiveBaseCallMachine.increment atInc≤B:=by
  simp [UniformRecursiveBaseCallMachine.increment,readable,peak,Op.readable,Op.peak,evalNat,atInc,dnow,onow,depthB]
 have inc:=block_runs UniformRecursiveBaseCallMachine.increment p (start+73) n B x atInc (inc_code code) rfl save.final_bound
  (by change start+74≤B;omega) incSafe.1 incSafe.2
 let atSetup:=applyBlock UniformRecursiveBaseCallMachine.increment atInc
 have keep(i:ℕ)(hi:i≠4151 ∧ i≠4152 ∧ i≠4153 ∧ i≠4154):atSetup.natReg i=s.natReg i:=by
  simpa [atSetup,UniformRecursiveBaseCallMachine.increment,applyBlock,Op.apply,evalNat,writeNat,next,atInc,child,installed,UniformRecursiveBaseCallMachine.pushSetup,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2] using nr i hi.2.1
 have spNow:atSetup.natReg 4150=stack:=(keep _ (by omega)).trans sp
 have qNow:atSetup.natReg 4060=q:=(keep _ (by omega)).trans hq
 have tNow:atSetup.natReg 4015=T:=(keep _ (by omega)).trans size
 have dNow:atSetup.natReg 4091=D:=(keep _ (by omega)).trans dataBase
 have iNow:atSetup.natReg 4125=i:=(keep _ (by omega)).trans index
 have fNow:atSetup.natReg 4133=frontier:=(keep _ (by omega)).trans fresh
 have oNow:atSetup.natReg 4153=1:=by simpa [atSetup,UniformRecursiveBaseCallMachine.increment,applyBlock,Op.apply,evalNat,writeNat,next,atInc] using onow
 have gb:=group_bounds D V T i groups B partition hi dataEnd tp
 have qb:q≤B:=by have h:=bound.2.1 4060;rwa [hq] at h
 have tb:T≤B:=by have h:=bound.2.1 4015;rwa [size] at h
 have fb:frontier≤B:=by have h:=bound.2.1 4133;rwa [fresh] at h
 have setupSafe:readable childSetup atSetup ∧ peak childSetup atSetup≤B:=by
  simp [childSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,qNow,tNow,dNow,iNow,fNow,oNow,max_le_iff,gb.1,gb.2.1,gb.2.2.1,gb.2.2.2,qb,tb,fb]
 have setupPC:atSetup.pc=start+74:=by simp [atSetup,UniformRecursiveBaseCallMachine.increment,applyBlock,Op.apply,writeNat,next,atInc] <;> omega
 have setup:=block_runs childSetup p (start+74) n B x atSetup (setup_code code) setupPC inc.final_bound
  (by change start+82≤B;omega) setupSafe.1 setupSafe.2
 let advanced:=applyBlock childSetup atSetup
 let u:State:={advanced with pc:=0}
 have ub:=changePC_bound B advanced 0 setup.final_bound (by omega)
 have advancedPC:advanced.pc=start+82:=by simp [advanced,childSetup,applyBlock,Op.apply,writeNat,next,setupPC] <;> omega
 have jump:BoundedRuns p n x B advanced 1 u:=.next setup.final_bound
  (by simp [step,advancedPC,jump_at code,u]) (.refl ub)
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,sh,ss,ou,ro⟩
 · convert push.trans (save.trans (inc.trans (setup.trans jump))) using 1
   simp [UniformRecursiveBaseCallMachine.pushSetup,UniformRecursiveBaseCallMachine.increment,childSetup] <;> omega
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,qNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,dNow,iNow,tNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,tNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,fNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,spNow]
 · simp [u,advanced,childSetup,atSetup,UniformRecursiveBaseCallMachine.increment,applyBlock,Op.apply,evalNat,writeNat,next,atInc,dnow,onow]
 · intro j hj
   have b:=bank j hj
   have fi:Stack.fields[j]'hj≠4152 ∧ Stack.fields[j]'hj≠4153:=UniformRecursiveReturnStackMachine.fields_safe _ (List.getElem_mem hj)
   have all4:∀i∈Stack.fields,i≠4154:=by decide
   have f4:=all4 _ (List.getElem_mem hj)
   simpa [u,advanced,childSetup,atSetup,UniformRecursiveBaseCallMachine.increment,applyBlock,Op.apply,evalNat,writeNat,next,atInc,child,installed,UniformRecursiveBaseCallMachine.pushSetup,fi.1,fi.2,f4] using b
 · intro z hz
   have hz':z<stack+34*depth∨stack+34*depth+34≤z:=by
    rcases hz with h|h
    · exact Or.inl h
    · right;simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h
   exact nh z hz'

/-- The actual positive group branch and fixed self-call fragment. The
complete-W data is copied unchanged into the child's real entry headers. -/
theorem call_from_group (n B q D V i groups stack depth F : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .groupTest) (index:s.natReg 4125=i) (total:s.natReg 4126=groups)
 (columns:s.natReg 4060=q) (size:s.natReg 4015=2^q) (base:s.natReg 4091=D)
 (fresh:s.natReg 4133=F) (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (partition:groups*(S.W*2^q)=V) (hi:i<groups) (bound:WordBound B s) (code:P.program.length≤B)
 (dataEnd:D+V≤B) (stackEnd:stack+34*(depth+1)≤B) : ∃u,
 BoundedRuns P.program n x B s 84 u ∧ u.pc=0 ∧
 u.natReg 4120=q ∧ u.natReg 4121=D+i*(S.W*2^q) ∧ u.natReg 4122=2^q ∧ u.natReg 4123=F ∧
 u.natReg 4150=stack ∧ u.natReg 4151=depth+1 ∧ Stack.Bank Stack.fields (stack+34*depth) s.natReg u ∧
 (∀z,z<stack+34*depth∨stack+34*(depth+1)≤z→u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders:=by
 let atCall:State:={s with pc:=P.address .call}
 have branch:=UniformRecursiveBatchGroupMachine.branch_execution P.program (P.address .groupTest) (P.address .call)
  (P.address .inverseTest) n B i groups x s group_branch pc index total bound
  (R.start_bound .call B code) (R.start_bound .inverseTest B code)
 have first:BoundedRuns P.program n x B s 1 atCall:=by simpa only [hi,ite_true] using branch
 obtain ⟨u,run,up,k,a,t,f,stackPtr,dep,bank,heap,scalar,regs,out,roots⟩:=call_with_stack
  P.program (P.address .call) n B q (2^q) D V i groups stack depth F x atCall
  UniformRecursiveSavingProgram.call_code rfl columns size (Nat.two_pow_pos _) base index fresh sp dp partition hi
  dataEnd first.final_bound (R.code_bound .call 83 B rfl code) stackEnd
 exact ⟨u,by simpa only [Nat.add_comm] using first.trans run,up,k,a,t,f,stackPtr,dep,bank,heap,scalar,regs,out,roots⟩
/-- One complete-W recursive group, as a step of the eventual well-founded
proof. The induction hypothesis is invoked on the actual state reached by
call83 and on this same Program; its return is followed by the real stack
load and group-cursor increment. This lemma alone does not discharge the
induction hypothesis or claim the full saving transform. -/
theorem one_group_of_induction
 (k q m r n B reserve D V A i groups stack depth stackTop F:ℕ) (cost:ℕ→ℕ) (x:Fin n→ℂ)
 (s:State) (input:Fin S.W→Fin (2^q)→Scalar)
 (ih:SmallerBodies k n B reserve stack stackTop cost x) (smaller:q<k)
 (pc:s.pc=P.address .groupTest) (index:s.natReg 4125=i) (total:s.natReg 4126=groups)
 (columns:s.natReg 4060=q) (size:s.natReg 4015=2^q) (savedSize:s.natReg 4124=2^q)
 (base:s.natReg 4091=D) (fresh:s.natReg 4133=F) (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (bits:s.natReg 4120=k) (rest:s.natReg 4127=r) (original:s.natReg 4121=A)
 (volume:s.natReg 4122=V) (width:s.natReg 4061=m) (baseAlias:s.natReg 3300=A)
 (partition:groups*(S.W*2^q)=V) (hi:i<groups)
 (data:∀(j:Fin S.W) (t:Fin (2^q)),s.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)=some (input j t))
 (dataBase:3≤D) (dataEnd:D+V≤F) (stackRoom:stack+34*(depth+q+2)≤ stackTop) (stackEnd:stackTop≤F)
 (room:F+reserve*(q+1)*2^q≤B) (square:(2^q)^2≤B)
 (constants:UniformBinaryCStageMachine.Constants s) (bound:WordBound B s) (code:P.program.length≤B):∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .groupTest ∧
 u.natReg 4125=i+1 ∧ u.natReg 4126=groups ∧ u.natReg 4150=stack ∧ u.natReg 4151=depth ∧ u.natReg 4153=1 ∧
 (∀j∈Stack.fields,u.natReg j=if j=4125 then s.natReg j+1 else s.natReg j) ∧
 u.natReg 4015=2^q ∧ u.natReg 4023=V ∧ u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧
 (∀(j:Fin S.W) (t:Fin (2^q)),(u.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)).isSome=true) ∧
 (∀(j:Fin S.W) (t:Fin (2^q)),(u.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)).map Scalar.value=
  some ((physicalMatrix q).mulVec (fun z=>(input j z).value) t)) ∧
 (∀z,z<F→(z<D+i*(S.W*2^q)∨D+(i+1)*(S.W*2^q)≤z)→u.scalarHeap z=s.scalarHeap z) ∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ticks≤cost q+169:=by
 have fb:F≤B:=by omega
 have localStack:stack+34*(depth+1)≤B:=by nlinarith only [stackRoom,stackEnd,fb]
 obtain ⟨c,call,cp,ck,ca,ct,cf,csp,cdp,bank,nh,sh,sr,ou,ro⟩:=call_from_group
  n B q D V i groups stack depth F x s pc index total columns size base fresh sp dp partition hi
  bound code (dataEnd.trans fb) localStack
 have partEnd:(i+1)*(S.W*2^q)≤V:=
  (Nat.mul_le_mul_right (S.W*2^q) (Nat.succ_le_of_lt hi)).trans_eq partition
 have addEnd:D+i*(S.W*2^q)+S.W*2^q≤F:=by
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact Nat.add_le_add_left partEnd D |>.trans dataEnd
 have childData:∀(j:Fin S.W) (t:Fin (2^q)),c.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)=some (input j t):=by
  intro j t;rw [sh];exact data j t
 have childConst:UniformBinaryCStageMachine.Constants c:=by
  simpa only [UniformBinaryCStageMachine.Constants,sh] using constants
 obtain ⟨v,ticks,child,vp,vsp,vdp,present,values,natFrame,scalarFrame,vc,vo,vr,timeBound⟩:=
  ih q smaller (D+i*(S.W*2^q)) F (depth+1) input c cp ck ca ct cf csp cdp childData (by omega)
   (by omega) addEnd (by convert stackRoom using 1 <;> omega) stackEnd code room square childConst call.final_bound
 have savedBank:Stack.Bank Stack.fields (stack+34*depth) s.natReg v:=by
  intro j hj
  have jl:j<34:=by simpa only [UniformRecursiveReturnStackMachine.fields_length] using hj
  have below:stack+34*depth+j<F:=by nlinarith only [stackRoom,stackEnd,jl]
  rw [natFrame _ below (Or.inl (by omega))]
  exact bank j hj
 have next:i+1≤B:=by
  have gp:0<S.W*2^q:=Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos _)
  have gb:groups≤V:=(Nat.le_mul_of_pos_right _ gp).trans_eq partition
  omega
 obtain ⟨u,ret,up,fields,usp,udp,globalOne,ut,uv,uone,uk,ur,uq,um,unh,ush,usr,uou,uro⟩:=
  UniformRecursiveParentReturn.resume_fields n B k q m r A V (2^q) stack depth s.natReg x v
   vp vsp vdp savedBank (fun j _=>bound.2.1 j) (by rwa [index]) savedSize volume bits rest original columns width baseAlias
   child.final_bound code localStack
 refine ⟨u,84+ticks+(76+P.size .restored),call.trans (child.trans ret),up,?_,?_,usp,udp,globalOne,fields,
  ut,uv,uone,uk,ur,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only [ite_true,index] using fields 4125 (by decide)
 · simpa only [show (4126:ℕ)≠4125 from by omega,ite_false,total] using fields 4126 (by decide)
 · intro j t;rw [ush];exact present j t
 · intro j t;rw [ush];exact values j t
 · intro z hz out
   rw [ush,scalarFrame z hz (by
    rcases out with out|out
    · exact Or.inl out
    · right;rw [Nat.add_assoc,←Nat.succ_mul];exact out),sh]
 · intro z hz out
   rw [unh,natFrame z hz (by rcases out with h|h;exact Or.inl (by omega);exact Or.inr h)]
   exact nh z (by rcases out with h|h;exact Or.inl h;right;nlinarith only [stackRoom,h])
 · simpa only [UniformBinaryCStageMachine.Constants,ush] using vc
 · exact uou.trans (vo.trans ou)
 · exact uro.trans (vr.trans ro)
 · change 84+ticks+(76+9)≤cost q+169
   omega

end
end ExactFourierCircuits.UniformRecursiveGroupExecution
