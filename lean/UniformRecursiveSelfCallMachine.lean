import UniformRecursiveBaseCallMachine
import UniformBatching
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSelfCallMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace Stack
export UniformRecursiveReturnStackMachine (fields Bank saveProgram)
end Stack
noncomputable section

/-- The fixed group size is exactly the padded seed width. -/
def W : ℕ := ExplicitSeedBudget.paddedRoles
lemma W_positive : 0<W:=by
 change 0<UniformBatching.width
 rw [UniformBatching.width_eq_pow]
 exact Nat.two_pow_pos _
/-- All operands are actual registers from the generated parent gather.
The child exponent is q; spectator bits affect the number of groups only. -/
def childSetup : List Op := [.literal 4164 W,.binary .mul 4165 4164 4015,
 .binary .mul 4166 4125 4165,.binary .add 4167 4091 4166,
 .binary .mul 4120 4060 4153,.binary .mul 4121 4167 4153,
 .binary .mul 4122 4015 4153,.binary .mul 4123 4133 4153]
/-- This is a literal fragment of the one recursive program. Its final jump
always returns to that same program's PC0; there is no dynamic callback. -/
def callCode (start:ℕ) : Program := UniformRecursiveBaseCallMachine.pushSetup.map Op.code++
 Stack.saveProgram.map (relocate (start+4) (start+73))++
 UniformRecursiveBaseCallMachine.increment.map Op.code++childSetup.map Op.code++[.jump 0]
lemma callCode_length (start:ℕ) : (callCode start).length=83:=by
 simp only [callCode,List.length_append,List.length_map,UniformRecursiveBaseCallMachine.pushSetup,
 UniformRecursiveBaseCallMachine.increment,childSetup,List.length_cons,List.length_nil,UniformRecursiveReturnStackMachine.saveProgram_length]
/-- An instruction-range fact, not a child execution/action assumption. -/
def CallAt (p:Program) (start:ℕ) : Prop := ∀i,i<83→p[start+i]?=(callCode start)[i]?
lemma push_code {p:Program} {start:ℕ} (code:CallAt p start) :
 BlockAt UniformRecursiveBaseCallMachine.pushSetup p start:=by
 intro i hi
 rw [code i (by change i<4 at hi;omega)]
 simp only [callCode,List.append_assoc]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma save_code {p:Program} {start:ℕ} (code:CallAt p start) : CodeAt Stack.saveProgram p (start+4) (start+73):=by
 intro i hi
 rw [show start+4+i=start+(4+i) from by omega,code (4+i) (by rw [UniformRecursiveReturnStackMachine.saveProgram_length] at hi;omega)]
 simp only [callCode,List.append_assoc]
 rw [List.getElem?_append_right (by change 4≤4+i;omega)]
 simp only [List.length_map,show UniformRecursiveBaseCallMachine.pushSetup.length=4 from rfl,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
lemma inc_code {p:Program} {start:ℕ} (code:CallAt p start) :
 BlockAt UniformRecursiveBaseCallMachine.increment p (start+73):=by
 intro i hi
 have hi1:i<1:=hi
 have eq:i=0:=by omega
 subst i
 rw [show start+73+0=start+73 from by omega,code 73 (by omega)]
 simp [callCode,UniformRecursiveBaseCallMachine.pushSetup,UniformRecursiveBaseCallMachine.increment,
  List.getElem?_append_right,UniformRecursiveReturnStackMachine.saveProgram_length]
lemma setup_code {p:Program} {start:ℕ} (code:CallAt p start) : BlockAt childSetup p (start+74):=by
 intro i hi
 rw [show start+74+i=start+(74+i) from by omega,code (74+i) (by change i<8 at hi;omega)]
 let pre:=UniformRecursiveBaseCallMachine.pushSetup.map Op.code++Stack.saveProgram.map (relocate (start+4) (start+73))++UniformRecursiveBaseCallMachine.increment.map Op.code
 have len:pre.length=74:=by simp [pre,UniformRecursiveBaseCallMachine.pushSetup,UniformRecursiveBaseCallMachine.increment,UniformRecursiveReturnStackMachine.saveProgram_length]
 have eq:callCode start=pre++(childSetup.map Op.code++[.jump 0]):=by simp only [callCode,pre,List.append_assoc]
 rw [eq,List.getElem?_append_right (by omega),len,Nat.add_sub_cancel_left,
  List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma jump_at {p:Program} {start:ℕ} (code:CallAt p start) : p[start+82]?=some (.jump 0):=by
 rw [code 82 (by omega)]
 let pre:=UniformRecursiveBaseCallMachine.pushSetup.map Op.code++Stack.saveProgram.map (relocate (start+4) (start+73))++UniformRecursiveBaseCallMachine.increment.map Op.code++childSetup.map Op.code
 have len:pre.length=82:=by simp [pre,UniformRecursiveBaseCallMachine.pushSetup,UniformRecursiveBaseCallMachine.increment,childSetup,UniformRecursiveReturnStackMachine.saveProgram_length]
 have eq:callCode start=pre++[.jump 0]:=by simp only [callCode,pre,List.append_assoc]
 rw [eq,List.getElem?_append_right (by omega),len];rfl

lemma group_bounds (D V T i groups B:ℕ) (partition:groups*(W*T)=V) (hi:i<groups) (endptr:D+V≤B) (tp:0<T) :
 W≤B ∧ W*T≤B ∧ i*(W*T)≤B ∧ D+i*(W*T)≤B:=by
 have hmul:W*T≤V:=by
  have positive:1≤groups:=by omega
  have h:=Nat.mul_le_mul_right (W*T) positive
  simpa only [Nat.one_mul,partition] using h
 have stride:T≤W*T:=by exact Nat.le_mul_of_pos_left _ W_positive
 have offset:i*(W*T)≤V:=(Nat.mul_le_mul_right (W*T) (by omega: i≤groups)).trans_eq partition
 have wp:W≤W*T:=Nat.le_mul_of_pos_right _ tp
 exact ⟨wp.trans (hmul.trans (by omega)),hmul.trans (by omega),offset.trans (by omega),by omega⟩

/-- An actual same-program self-call segment: save parent controls, compute
one complete W-array base, install q/base/size/frontier, and physically jump0.
No transform, handler or child-return premise is accepted. -/
theorem call_execution (p:Program) (start n B q T D V i groups stack depth frontier:ℕ)
 (x:Fin n→ℂ) (s:State) (code:CallAt p start) (pc:s.pc=start)
 (hq:s.natReg 4060=q) (size:s.natReg 4015=T) (tp:0<T)
 (dataBase:s.natReg 4091=D) (index:s.natReg 4125=i) (fresh:s.natReg 4133=frontier)
 (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (partition:groups*(W*T)=V) (hi:i<groups) (dataEnd:D+V≤B)
 (bound:WordBound B s) (extent:start+83≤B) (stackEnd:stack+34*(depth+1)≤B) :
 ∃u,BoundedRuns p n x B s 83 u ∧ u.pc=0 ∧
 u.natReg 4120=q ∧ u.natReg 4121=D+i*(W*T) ∧ u.natReg 4122=T ∧ u.natReg 4123=frontier ∧
 u.natReg 4151=depth+1 ∧ Stack.Bank Stack.fields (stack+34*depth) s.natReg u ∧
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
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,sh,ss,ou,ro⟩
 · convert push.trans (save.trans (inc.trans (setup.trans jump))) using 1
   simp [UniformRecursiveBaseCallMachine.pushSetup,UniformRecursiveBaseCallMachine.increment,childSetup] <;> omega
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,qNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,dNow,iNow,tNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,tNow,oNow]
 · simp [u,advanced,childSetup,applyBlock,Op.apply,evalNat,writeNat,next,fNow,oNow]
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

/-- One fixed return site restores the suspended parent, increments the actual
complete-group counter, and jumps to the parent's fixed group-loop PC. -/
def advanceGroup : List Op := [.binary .add 4125 4125 4153]
def returnCode (start loop:ℕ) : Program := UniformRecursiveBaseCallMachine.popSetup.map Op.code++
 UniformRecursiveReturnStackMachine.loadProgram.map (relocate (start+5) (start+74))++
 advanceGroup.map Op.code++[.jump loop]
lemma returnCode_length (start loop:ℕ) : (returnCode start loop).length=76:=by
 simp only [returnCode,List.length_append,List.length_map,UniformRecursiveBaseCallMachine.popSetup,
  UniformRecursiveReturnStackMachine.loadProgram_length,advanceGroup,List.length_cons,List.length_nil]
def ReturnAt (p:Program) (start loop:ℕ) : Prop := ∀i,i<76→p[start+i]?=(returnCode start loop)[i]?
lemma pop_code {p:Program} {start loop:ℕ} (code:ReturnAt p start loop) :
 BlockAt UniformRecursiveBaseCallMachine.popSetup p start:=by
 intro i hi
 rw [code i (by change i<5 at hi;omega)]
 simp only [returnCode,List.append_assoc]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma load_code {p:Program} {start loop:ℕ} (code:ReturnAt p start loop) :
 CodeAt UniformRecursiveReturnStackMachine.loadProgram p (start+5) (start+74):=by
 intro i hi
 rw [show start+5+i=start+(5+i) from by omega,code (5+i) (by rw [UniformRecursiveReturnStackMachine.loadProgram_length] at hi;omega)]
 simp only [returnCode,List.append_assoc]
 rw [List.getElem?_append_right (by change 5≤5+i;omega)]
 simp only [List.length_map,show UniformRecursiveBaseCallMachine.popSetup.length=5 from rfl,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
lemma advance_code {p:Program} {start loop:ℕ} (code:ReturnAt p start loop) :
 BlockAt advanceGroup p (start+74):=by
 intro i hi
 have h1:i<1:=hi
 have eq:i=0:=by omega
 subst i
 rw [show start+74+0=start+74 from by omega,code 74 (by omega)]
 simp [returnCode,UniformRecursiveBaseCallMachine.popSetup,advanceGroup,List.getElem?_append_right,
  UniformRecursiveReturnStackMachine.loadProgram_length]
lemma return_jump {p:Program} {start loop:ℕ} (code:ReturnAt p start loop) : p[start+75]?=some (.jump loop):=by
 rw [code 75 (by omega)]
 let pre:=UniformRecursiveBaseCallMachine.popSetup.map Op.code++UniformRecursiveReturnStackMachine.loadProgram.map (relocate (start+5) (start+74))++advanceGroup.map Op.code
 have len:pre.length=75:=by simp [pre,UniformRecursiveBaseCallMachine.popSetup,advanceGroup,UniformRecursiveReturnStackMachine.loadProgram_length]
 have eq:returnCode start loop=pre++[.jump loop]:=by simp only [returnCode,pre,List.append_assoc]
 rw [eq,List.getElem?_append_right (by omega),len];rfl

/-- This theorem reads the saved physical frame. It accepts no child action or
execution premise and preserves the actual current child scalar bank. -/
theorem return_execution (p:Program) (start loop n B stack depth:ℕ) (v:ℕ→ℕ)
 (x:Fin n→ℂ) (s:State) (code:ReturnAt p start loop) (pc:s.pc=start)
 (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth+1)
 (bank:Stack.Bank Stack.fields (stack+34*depth) v s)
 (values:∀i∈Stack.fields,v i≤B) (nextIndex:v 4125+1≤B)
 (bound:WordBound B s) (extent:start+76≤B) (loopBound:loop≤B) (stackEnd:stack+34*(depth+1)≤B) :
 ∃u,BoundedRuns p n x B s 76 u ∧ u.pc=loop ∧
 (∀i∈Stack.fields,u.natReg i=if i=4125 then v i+1 else v i) ∧
 u.natReg 4151=depth ∧ u.natHeap=s.natHeap ∧
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
 refine ⟨u,?_,rfl,?_,?_,rheap,rsh,rsr,ro,rro⟩
 · convert pop.trans (load.trans (advance.trans jump)) using 1
   simp [UniformRecursiveBaseCallMachine.popSetup,advanceGroup]
 · intro i hi
   have old:=rvals i hi
   by_cases eq:i=4125
   · subst i;simp [u,advanced,advanceGroup,applyBlock,Op.apply,evalNat,writeNat,next,atAdvance,rindex,rone]
   · simpa [u,advanced,advanceGroup,applyBlock,Op.apply,evalNat,writeNat,next,atAdvance,eq] using old
 · have d:=rregs 4151 (by omega) (by decide)
   simpa [u,advanced,advanceGroup,atAdvance,child,installed,UniformRecursiveBaseCallMachine.popSetup,applyBlock,Op.apply,evalNat,writeNat,next,dp] using d

end
end ExactFourierCircuits.UniformRecursiveSelfCallMachine
