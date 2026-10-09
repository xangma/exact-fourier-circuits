import UniformRecursiveNodeJoin
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveParentReturn
open UniformMachine UniformAssembly UniformNatBlockMachine
namespace P
export UniformRecursiveSavingProgram (Part program piece address size part_slice)
end P
noncomputable section

/-- Change a symbolic fixed code length without expanding its starting PC. -/
lemma add_bound_replace (a u v B : ℕ) (eq:u=v) (h:a+u≤B) : a+v≤B:=by rw [←eq];exact h
lemma start_bound (a : P.Part) (B : ℕ) (code:P.program.length≤B) : P.address a≤B:=
 (Nat.le_add_right _ _).trans ((UniformRecursiveSavingExecution.part_bound a).trans code)
lemma code_bound (a : P.Part) (len B : ℕ) (eq:P.size a=len) (code:P.program.length≤B) : P.address a+len≤B:=
 add_bound_replace _ _ _ _ eq ((UniformRecursiveSavingExecution.part_bound a).trans code)

lemma return_code : UniformRecursiveSelfCallMachine.ReturnAt P.program (P.address .returnSite) (P.address .restored):=by
 intro i hi
 apply P.part_slice .returnSite i
 simpa only [P.piece,UniformRecursiveSelfCallMachine.returnCode_length] using hi

def restoredOps : List Op := [.binary .mul 4015 4124 4153,.binary .mul 4023 4122 4153,
 .binary .mul 4069 4153 4153,.binary .mul 5300 4120 4153,
 .binary .mul 5301 4127 4153,.binary .mul 3300 4121 4153,
 .binary .mul 2852 4060 4153,.binary .mul 2853 4061 4153]
lemma restored_length : restoredOps.length=8:=rfl
lemma restored_code : BlockAt restoredOps P.program (P.address .restored):=
 UniformRecursiveSavingExecution.part_block .restored _ _ rfl
lemma restored_jump : P.program[P.address .restored+8]?=some (.jump (P.address .groupTest)):=
 UniformRecursiveSavingExecution.part_at .restored 8 (by decide)

def Changed (i : ℕ) : Prop := i=4015∨i=4023∨i=4069∨i=5300∨i=5301∨i=3300∨i=2852∨i=2853
structure Frame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬Changed i→u.natReg i=s.natReg i
lemma restored_frame (s : State) : Frame s (applyBlock restoredOps s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 unfold Changed at hi
 simp (disch:=omega) [restoredOps,applyBlock,Op.apply,evalNat,writeNat,next]

theorem restored_generic_execution (p : Program) (start ret total n B k q m r A V T : ℕ) (x : Fin n→ℂ) (s : State)
 (len:total=9) (atCode:BlockAt restoredOps p start) (atJump:p[start+8]?=some (.jump ret))
 (pc:s.pc=start) (one:s.natReg 4153=1) (size:s.natReg 4124=T) (volume:s.natReg 4122=V)
 (bits:s.natReg 4120=k) (rest:s.natReg 4127=r) (base:s.natReg 4121=A)
 (columns:s.natReg 4060=q) (width:s.natReg 4061=m) (bound:WordBound B s)
 (extent:start+total≤B) (retBound:ret≤B) : ∃u,
 BoundedRuns p n x B s total u ∧ u.pc=ret ∧ u.natReg 4015=T ∧ u.natReg 4023=V ∧
 u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧ u.natReg 3300=A ∧
 u.natReg 2852=q ∧ u.natReg 2853=m ∧ Frame s u:=by
 have vb:V≤B:=by have h:=bound.2.1 4122;rwa [volume] at h
 have tb:T≤B:=by have h:=bound.2.1 4124;rwa [size] at h
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have rb:r≤B:=by have h:=bound.2.1 4127;rwa [rest] at h
 have ab:A≤B:=by have h:=bound.2.1 4121;rwa [base] at h
 have qb:q≤B:=by have h:=bound.2.1 4060;rwa [columns] at h
 have mb:m≤B:=by have h:=bound.2.1 4061;rwa [width] at h
 have ob:1≤B:=by have h:=bound.2.1 4153;rwa [one] at h
 have safe:readable restoredOps s∧peak restoredOps s≤B:=by
  simp [restoredOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,size,volume,bits,rest,base,columns,width,
   vb,tb,kb,rb,ab,qb,mb,ob]
 have run:=block_runs restoredOps p start n B x s atCode pc bound (by rw [restored_length];omega) safe.1 safe.2
 let t:=applyBlock restoredOps s
 let u:State:={t with pc:=ret}
 have tp:t.pc=start+8:=by rw [UniformRecursiveNodePreparation.block_pc,pc,restored_length]
 have ub:=changePC_bound B t ret run.final_bound retBound
 have jump:BoundedRuns p n x B t 1 u:=.next run.final_bound (by simp [step,tp,atJump,u]) (.refl ub)
 have fr:Frame s u:=by
  have h:=restored_frame s
  exact ⟨h.natHeap,h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,fr⟩
 · simpa only [restored_length,len] using run.trans jump
 all_goals simp [u,t,restoredOps,applyBlock,Op.apply,evalNat,writeNat,next,one,size,volume,bits,rest,base,columns,width]

theorem restored_execution (n B k q m r A V T : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .restored) (one:s.natReg 4153=1) (size:s.natReg 4124=T) (volume:s.natReg 4122=V)
 (bits:s.natReg 4120=k) (rest:s.natReg 4127=r) (base:s.natReg 4121=A)
 (columns:s.natReg 4060=q) (width:s.natReg 4061=m) (bound:WordBound B s) (code:P.program.length≤B) : ∃u,
 BoundedRuns P.program n x B s (P.size .restored) u ∧ u.pc=P.address .groupTest ∧
 u.natReg 4015=T ∧ u.natReg 4023=V ∧ u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧
 u.natReg 3300=A ∧ u.natReg 2852=q ∧ u.natReg 2853=m ∧ Frame s u:=
 restored_generic_execution P.program (P.address .restored) (P.address .groupTest) (P.size .restored)
 n B k q m r A V T x s rfl restored_code restored_jump pc one size volume bits rest base columns width bound
 ((UniformRecursiveSavingExecution.part_bound .restored).trans code) (start_bound .groupTest B code)
namespace Stack
export UniformRecursiveReturnStackMachine (fields Bank loadProgram)
end Stack
open UniformRecursiveSelfCallMachine

/-- The physical return also certifies the unit register needed by the real
reload fragment; this is the existing return proof with that output retained. -/
theorem return_with_one (p:Program) (start loop n B stack depth:ℕ) (v:ℕ→ℕ)
 (x:Fin n→ℂ) (s:State) (code:ReturnAt p start loop) (pc:s.pc=start)
 (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth+1)
 (bank:Stack.Bank Stack.fields (stack+34*depth) v s)
 (values:∀i∈Stack.fields,v i≤B) (nextIndex:v 4125+1≤B)
 (bound:WordBound B s) (extent:start+76≤B) (loopBound:loop≤B) (stackEnd:stack+34*(depth+1)≤B) :
 ∃u,BoundedRuns p n x B s 76 u ∧ u.pc=loop ∧
 (∀i∈Stack.fields,u.natReg i=if i=4125 then v i+1 else v i) ∧
 u.natReg 4153=1 ∧ u.natReg 4150=stack ∧ u.natReg 4151=depth ∧ u.natHeap=s.natHeap ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have ptrB:=UniformRecursiveBaseCallMachine.frame_base_bound stack depth B stackEnd
 have endB:=UniformRecursiveBaseCallMachine.frame_extent stack depth B stackEnd
 have popSafe:readable UniformRecursiveBaseCallMachine.popSetup s ∧ peak UniformRecursiveBaseCallMachine.popSetup s≤B:=by
  simp [UniformRecursiveBaseCallMachine.popSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,sp,dp,ptrB]
  omega
 have pop:=block_runs UniformRecursiveBaseCallMachine.popSetup p start n B x s (pop_code code) pc bound
  (by change start+5≤B;omega) popSafe.1 popSafe.2
 let installed:=applyBlock UniformRecursiveBaseCallMachine.popSetup s
 let child:State:={installed with pc:=0}
 have cb:=changePC_bound B installed 0 pop.final_bound (by omega)
 have ptr:child.natReg 4152=stack+34*depth:=by simp [child,installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,evalNat,writeNat,next,sp,dp,Nat.mul_comm]
 have one:child.natReg 4153=1:=by simp [child,installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,evalNat,writeNat,next]
 obtain ⟨restored,rr,rpc,rvals,rptr,rheap,rregs,rsh,rsr,ro,rro⟩:=UniformRecursiveReturnStackMachine.load_execution
  n B (stack+34*depth) v x child rfl ptr one bank values cb (by omega) endB
 have halting:BoundedExecution UniformRecursiveReturnStackMachine.loadProgram n x B child 69 restored:=by
  convert rr.executes (.halt rr.final_bound (by simp [step,rpc,UniformRecursiveBaseCallMachine.load_halt])) using 1
 have load:=UniformBoundedAssembly.boundedExecution_placed (load_code code) (by change start+5+69≤B;omega) (by omega) halting
 have ip:installed.pc=start+5:=by simp [installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,writeNat,next,pc] <;> omega
 have placedLoad:placed (start+5) child=installed:=by change {installed with pc:=start+5}=installed;rw [←ip]
 rw [placedLoad] at load
 let atAdvance:State:={restored with pc:=start+74}
 have index:atAdvance.natReg 4125=v 4125:=rvals _ (by decide)
 have rone:restored.natReg 4153=1:=(rregs _ (by omega) (by decide)).trans one
 have rindex:restored.natReg 4125=v 4125:=rvals _ (by decide)
 have o:atAdvance.natReg 4153=1:=rone
 have asafe:readable advanceGroup atAdvance ∧ peak advanceGroup atAdvance≤B:=by
  simp [advanceGroup,readable,peak,Op.readable,Op.peak,evalNat,atAdvance,rindex,rone,nextIndex]
 have advance:=block_runs advanceGroup p (start+74) n B x atAdvance (advance_code code) rfl load.final_bound
  (by change start+75≤B;omega) asafe.1 asafe.2
 let advanced:=applyBlock advanceGroup atAdvance
 let u:State:={advanced with pc:=loop}
 have ub:=changePC_bound B advanced loop advance.final_bound loopBound
 have ap:advanced.pc=start+75:=by simp [advanced,advanceGroup,applyBlock,Op.apply,writeNat,next,atAdvance]
 have jump:BoundedRuns p n x B advanced 1 u:=.next advance.final_bound
  (by simp [step,ap,return_jump code,u]) (.refl ub)
 refine ⟨u,?_,rfl,?_,?_,?_,?_,rheap,rsh,rsr,ro,rro⟩
 · convert pop.trans (load.trans (advance.trans jump)) using 1
   simp [UniformRecursiveBaseCallMachine.popSetup,advanceGroup]
 · intro i hi
   have old:=rvals i hi
   by_cases eq:i=4125
   · subst i;simp [u,advanced,advanceGroup,applyBlock,Op.apply,evalNat,writeNat,next,atAdvance,rindex,rone]
   · simpa [u,advanced,advanceGroup,applyBlock,Op.apply,evalNat,writeNat,next,atAdvance,eq] using old
 · simp [u,advanced,advanceGroup,applyBlock,Op.apply,evalNat,writeNat,next,atAdvance,rone]
 · have d:=rregs 4150 (by omega) (by decide)
   simpa [u,advanced,advanceGroup,atAdvance,child,installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,evalNat,writeNat,next,sp] using d
 · have d:=rregs 4151 (by omega) (by decide)
   simpa [u,advanced,advanceGroup,atAdvance,child,installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,evalNat,writeNat,next,dp] using d


/-- A completed child enters the real fixed return site. Parent controls are
loaded from the actual saved frame and the next complete-W group is selected
by the real reload fragment. Child scalar outputs are unchanged by this run. -/
theorem execution (n B k q m r A V T stack depth : ℕ) (saved : ℕ→ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .returnSite) (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth+1)
 (bank:Stack.Bank Stack.fields (stack+34*depth) saved s) (values:∀i∈Stack.fields,saved i≤B)
 (next:saved 4125+1≤B) (hT:saved 4124=T) (hV:saved 4122=V) (hk:saved 4120=k)
 (hr:saved 4127=r) (hA:saved 4121=A) (hq:saved 4060=q) (hm:saved 4061=m)
 (bound:WordBound B s) (code:P.program.length≤B) (stackEnd:stack+34*(depth+1)≤B) : ∃u,
 BoundedRuns P.program n x B s (76+P.size .restored) u ∧ u.pc=P.address .groupTest ∧
 u.natReg 4125=saved 4125+1 ∧ u.natReg 4126=saved 4126 ∧ u.natReg 4151=depth ∧
 u.natReg 4015=T ∧ u.natReg 4023=V ∧ u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧
 u.natReg 3300=A ∧ u.natReg 2852=q ∧ u.natReg 2853=m ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧
 u.rootOrders=s.rootOrders:=by
 obtain ⟨a,ra,pa,av,one,spAfter,depthVal,heap,scalar,regs,out,roots⟩:=return_with_one P.program (P.address .returnSite)
  (P.address .restored) n B stack depth saved x s return_code pc sp dp bank values next bound
  (code_bound .returnSite 76 B rfl code) (start_bound .restored B code) stackEnd
 have restoredValue (i : ℕ) (hi:i∈Stack.fields) (ne:i≠4125) : a.natReg i=saved i:=by
  simpa only [ne,ite_false] using av i hi
 have t:a.natReg 4124=T:=(restoredValue 4124 (by decide) (by omega)).trans hT
 have v:a.natReg 4122=V:=(restoredValue 4122 (by decide) (by omega)).trans hV
 have b:a.natReg 4120=k:=(restoredValue 4120 (by decide) (by omega)).trans hk
 have rem:a.natReg 4127=r:=(restoredValue 4127 (by decide) (by omega)).trans hr
 have base:a.natReg 4121=A:=(restoredValue 4121 (by decide) (by omega)).trans hA
 have columns:a.natReg 4060=q:=(restoredValue 4060 (by decide) (by omega)).trans hq
 have width:a.natReg 4061=m:=(restoredValue 4061 (by decide) (by omega)).trans hm
 obtain ⟨u,ru,pu,ut,uv,uo,uk,ur,ub,uq,um,frame⟩:=restored_execution n B k q m r A V T x a pa one t v b rem base columns width ra.final_bound code
 have index:u.natReg 4125=saved 4125+1:=by
  rw [frame.natReg 4125 (by unfold Changed;omega)]
  simpa only [ite_true] using av 4125 (by decide)
 have count:u.natReg 4126=saved 4126:=
  (frame.natReg 4126 (by unfold Changed;omega)).trans (restoredValue 4126 (by decide) (by omega))
 have dep:u.natReg 4151=depth:=(frame.natReg 4151 (by unfold Changed;omega)).trans depthVal
 exact ⟨u,ra.trans ru,pu,index,count,dep,ut,uv,uo,uk,ur,ub,uq,um,
  frame.natHeap.trans heap,frame.scalarHeap.trans scalar,frame.scalarReg.trans regs,frame.outputs.trans out,frame.roots.trans roots⟩
/-- Restore every saved parent field, retaining the cached native-base alias
that the real reload reconstructs from saved field 4121. -/
theorem resume_fields (n B k q m r A V T stack depth:ℕ) (saved:ℕ→ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=P.address .returnSite) (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth+1)
 (bank:Stack.Bank Stack.fields (stack+34*depth) saved s) (values:∀i∈Stack.fields,saved i≤B)
 (next:saved 4125+1≤B) (hT:saved 4124=T) (hV:saved 4122=V) (hk:saved 4120=k)
 (hr:saved 4127=r) (hA:saved 4121=A) (hq:saved 4060=q) (hm:saved 4061=m) (baseAlias:saved 3300=A)
 (bound:WordBound B s) (code:P.program.length≤B) (stackEnd:stack+34*(depth+1)≤B):∃u,
 BoundedRuns P.program n x B s (76+P.size .restored) u ∧ u.pc=P.address .groupTest ∧
 (∀i∈Stack.fields,u.natReg i=if i=4125 then saved i+1 else saved i) ∧
 u.natReg 4150=stack ∧ u.natReg 4151=depth ∧ u.natReg 4153=1 ∧
 u.natReg 4015=T ∧ u.natReg 4023=V ∧ u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧
 u.natReg 2852=q ∧ u.natReg 2853=m ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧
 u.rootOrders=s.rootOrders:=by
 obtain ⟨a,ra,pa,av,one,spAfter,depthVal,heap,scalar,regs,out,roots⟩:=return_with_one P.program (P.address .returnSite)
  (P.address .restored) n B stack depth saved x s return_code pc sp dp bank values next bound
  (code_bound .returnSite 76 B rfl code) (start_bound .restored B code) stackEnd
 have rv(i:ℕ)(hi:i∈Stack.fields)(ne:i≠4125):a.natReg i=saved i:=by
  simpa only [ne,ite_false] using av i hi
 obtain ⟨u,ru,pu,ut,uv,uo,uk,ur,ub,uq,um,frame⟩:=restored_execution n B k q m r A V T x a pa one
  ((rv 4124 (by decide) (by omega)).trans hT) ((rv 4122 (by decide) (by omega)).trans hV)
  ((rv 4120 (by decide) (by omega)).trans hk) ((rv 4127 (by decide) (by omega)).trans hr)
  ((rv 4121 (by decide) (by omega)).trans hA) ((rv 4060 (by decide) (by omega)).trans hq)
  ((rv 4061 (by decide) (by omega)).trans hm) ra.final_bound code
 have restored(i:ℕ)(hi:i∈Stack.fields):u.natReg i=if i=4125 then saved i+1 else saved i:=by
  by_cases eq:i=3300
  · subst i;simpa only [show (3300:ℕ)≠4125 from by omega,ite_false,baseAlias] using ub
  · have ne:¬Changed i:=by
     have safe:∀i∈Stack.fields,i=3300∨¬Changed i:=by unfold Changed;decide
     exact (safe i hi).resolve_left eq
    exact (frame.natReg i ne).trans (av i hi)
 have dep:u.natReg 4151=depth:=(frame.natReg 4151 (by unfold Changed;omega)).trans depthVal
 have stackPtr:u.natReg 4150=stack:=(frame.natReg 4150 (by unfold Changed;omega)).trans spAfter
 have globalOne:u.natReg 4153=1:=(frame.natReg 4153 (by unfold Changed;omega)).trans one
 exact ⟨u,ra.trans ru,pu,restored,stackPtr,dep,globalOne,ut,uv,uo,uk,ur,uq,um,
  frame.natHeap.trans heap,frame.scalarHeap.trans scalar,frame.scalarReg.trans regs,frame.outputs.trans out,frame.roots.trans roots⟩

end
end ExactFourierCircuits.UniformRecursiveParentReturn
