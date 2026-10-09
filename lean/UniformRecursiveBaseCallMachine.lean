import UniformRecursiveReturnStackMachine
import UniformBinaryBatchCMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveBaseCallMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace Stack
export UniformRecursiveReturnStackMachine (fields Bank saveFields loadFields saveProgram loadProgram)
end Stack
noncomputable section

def pushSetup : List Op := [.literal 4153 1,.literal 4154 34,
 .binary .mul 4152 4151 4154,.binary .add 4152 4150 4152]
def increment : List Op := [.binary .add 4151 4151 4153]
def popSetup : List Op := [.literal 4153 1,.literal 4154 34,
 .binary .sub 4151 4151 4153,.binary .mul 4152 4151 4154,.binary .add 4152 4150 4152]
/-- One genuine recursive-call base path. It saves the parent fields physically,
executes fixed54 on the entire real batch, then returns via actual heap loads.
The large-node record branch is still a separate obligation. -/
def program : Program := pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++
 increment.map Op.code++UniformBinaryBatchCMachine.program.map (relocate 74 128)++
 popSetup.map Op.code++Stack.loadProgram.map (relocate 133 202)++[.halt]
lemma program_length : program.length=203 := by simp only [program,List.length_append,List.length_map,
 UniformRecursiveReturnStackMachine.saveProgram_length,UniformRecursiveReturnStackMachine.loadProgram_length,
 UniformBinaryBatchCMachine.program_length,pushSetup,popSetup,increment,List.length_cons,List.length_nil]
lemma push_code : BlockAt pushSetup program 0 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma preSave_length : (pushSetup.map Op.code).length=4 := rfl
lemma save_code : CodeAt Stack.saveProgram program 4 73 := by
 have h:=embed_code (pushSetup.map Op.code) Stack.saveProgram
  (increment.map Op.code++UniformBinaryBatchCMachine.program.map (relocate 74 128)++popSetup.map Op.code++Stack.loadProgram.map (relocate 133 202)++[.halt]) 73
 unfold embed at h;rw [preSave_length] at h
 simpa only [program,List.append_assoc] using h
lemma inc_code : BlockAt increment program 73 := by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma preBatch_length : (pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code).length=74 := by
 simp only [List.length_append,List.length_map,pushSetup,increment,List.length_cons,List.length_nil,UniformRecursiveReturnStackMachine.saveProgram_length]
lemma batch_code : CodeAt UniformBinaryBatchCMachine.program program 74 128 := by
 have h:=embed_code (pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code)
  UniformBinaryBatchCMachine.program (popSetup.map Op.code++Stack.loadProgram.map (relocate 133 202)++[.halt]) 128
 unfold embed at h;rw [preBatch_length] at h
 simpa only [program,List.append_assoc] using h
lemma pop_code : BlockAt popSetup program 128 := by
 intro i hi
 let pre:=pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code++UniformBinaryBatchCMachine.program.map (relocate 74 128)
 have len:pre.length=128:=by simp only [pre,List.length_append,List.length_map,pushSetup,increment,List.length_cons,List.length_nil,
  UniformRecursiveReturnStackMachine.saveProgram_length,UniformBinaryBatchCMachine.program_length]
 have eq:program=pre++(popSetup.map Op.code++(Stack.loadProgram.map (relocate 133 202)++[.halt])):=by simp only [program,pre,List.append_assoc]
 rw [eq,List.getElem?_append_right (by omega),len,Nat.add_sub_cancel_left,
  List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma preLoad_length : (pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code++
 UniformBinaryBatchCMachine.program.map (relocate 74 128)++popSetup.map Op.code).length=133 := by
 simp only [List.length_append,List.length_map,pushSetup,popSetup,increment,List.length_cons,List.length_nil,
 UniformRecursiveReturnStackMachine.saveProgram_length,UniformBinaryBatchCMachine.program_length]
lemma load_code : CodeAt Stack.loadProgram program 133 202 := by
 have h:=embed_code (pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code++UniformBinaryBatchCMachine.program.map (relocate 74 128)++popSetup.map Op.code)
  Stack.loadProgram [.halt] 202
 unfold embed at h;rw [preLoad_length] at h
 simpa only [program,List.append_assoc] using h
lemma prefix_length : (pushSetup.map Op.code++Stack.saveProgram.map (relocate 4 73)++increment.map Op.code++
 UniformBinaryBatchCMachine.program.map (relocate 74 128)++popSetup.map Op.code++Stack.loadProgram.map (relocate 133 202)).length=202 := by
 simp only [List.length_append,List.length_map,pushSetup,popSetup,increment,List.length_cons,List.length_nil,
 UniformRecursiveReturnStackMachine.saveProgram_length,UniformRecursiveReturnStackMachine.loadProgram_length,UniformBinaryBatchCMachine.program_length]
lemma halt_at : program[202]?=some .halt := by unfold program;rw [List.getElem?_append_right (by rw [prefix_length]),prefix_length];rfl
lemma save_halt : Stack.saveProgram[68]?=some .halt := by
 unfold Stack.saveProgram
 rw [List.getElem?_append_right (by rw [List.length_map,UniformRecursiveReturnStackMachine.saveFields_length,UniformRecursiveReturnStackMachine.fields_length])]
 simp [UniformRecursiveReturnStackMachine.saveFields_length,UniformRecursiveReturnStackMachine.fields_length]
lemma load_halt : Stack.loadProgram[68]?=some .halt := by
 unfold Stack.loadProgram
 rw [List.getElem?_append_right (by rw [List.length_map,UniformRecursiveReturnStackMachine.loadFields_length,UniformRecursiveReturnStackMachine.fields_length])]
 simp [UniformRecursiveReturnStackMachine.loadFields_length,UniformRecursiveReturnStackMachine.fields_length]

lemma frame_extent (base depth B:ℕ) (endptr:base+34*(depth+1)≤B) : base+34*depth+34≤B := by nlinarith
lemma depth_bound (base depth B:ℕ) (endptr:base+34*(depth+1)≤B) : depth+1≤B := by nlinarith
lemma product_bound (base depth B:ℕ) (endptr:base+34*(depth+1)≤B) : depth*34≤B := by nlinarith
lemma frame_base_bound (base depth B:ℕ) (endptr:base+34*(depth+1)≤B) : base+depth*34≤B := by nlinarith

/-- Actual complete-batch execution, physical return-frame restoration and
full native tensor action, with every header/store/load/jump charged. -/
theorem execution (n B k count A stack depth:ℕ) (x:Fin n→ℂ) (s:State)
 (v:Fin count→Fin (2^k)→Scalar) (pc:s.pc=0)
 (bits:s.natReg 4900=k) (arrays:s.natReg 4901=count) (base:s.natReg 4902=A) (size:s.natReg 4903=2^k)
 (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (data:∀w z,s.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k w.val+z.val)=some (v w z))
 (ha:3≤A) (con:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s) (code:203≤B) (extent:A+count*2^k≤B) (stackEnd:stack+34*(depth+1)≤B) :
 ∃u,BoundedExecution program n x B s (count*UniformBinaryBatchCMachine.arrayCost k+154) u ∧ u.pc=202 ∧
 (∀w z,u.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k w.val+z.val)=some (UniformBinaryBatchCMachine.transformed k (v w) z)) ∧
 (∀r∈Stack.fields,u.natReg r=s.natReg r) ∧ u.natReg 4151=depth ∧
 (∀z,z<stack+34*depth∨stack+34*(depth+1)≤z→u.natHeap z=s.natHeap z) ∧
 (∀z,z<A∨A+count*2^k≤z→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mulB:=product_bound stack depth B stackEnd
 have ptrB:=frame_base_bound stack depth B stackEnd
 have endB:=frame_extent stack depth B stackEnd
 have depthB:=depth_bound stack depth B stackEnd
 have psafe:readable pushSetup s ∧ peak pushSetup s≤B:=by
  simp [pushSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,sp,dp,mulB,ptrB]
  omega
 have pushRun:=block_runs pushSetup program 0 n B x s push_code pc bound (by change 4≤B;omega) psafe.1 psafe.2
 let pushed:=applyBlock pushSetup s
 let saveChild:State:={pushed with pc:=0}
 have pp:pushed.pc=4:=by simp [pushed,pushSetup,applyBlock,Op.apply,writeNat,next,pc]
 have sb:=changePC_bound B pushed 0 pushRun.final_bound (by omega)
 have savePtr:saveChild.natReg 4152=stack+34*depth:=by simp [saveChild,pushed,pushSetup,applyBlock,Op.apply,evalNat,writeNat,next,sp,dp,Nat.mul_comm]
 have saveOne:saveChild.natReg 4153=1:=by simp [saveChild,pushed,pushSetup,applyBlock,Op.apply,evalNat,writeNat,next]
 obtain ⟨saved,sr,savedPC,bank,savedPtr,sh,nr,ssh,ssr,so,sro⟩:=UniformRecursiveReturnStackMachine.save_execution
  n B (stack+34*depth) x saveChild rfl savePtr saveOne sb (by omega) endB
 have se:BoundedExecution Stack.saveProgram n x B saveChild 69 saved:=by
  convert sr.executes (.halt sr.final_bound (by simp [step,savedPC,save_halt])) using 1
 have saveRun:=UniformBoundedAssembly.boundedExecution_placed save_code (by change 73≤B;omega) (by omega) se
 have placedSave:placed 4 saveChild=pushed:=by change {pushed with pc:=4}=pushed;rw [←pp]
 rw [placedSave] at saveRun
 let atIncrement:State:={saved with pc:=73}
 have savedDepth:saved.natReg 4151=depth:=by
  have h:=nr 4151 (by omega)
  simpa [saveChild,pushed,pushSetup,applyBlock,Op.apply,evalNat,writeNat,next,dp] using h
 have savedOne:saved.natReg 4153=1:=(nr _ (by omega)).trans saveOne
 have isafe:readable increment atIncrement ∧ peak increment atIncrement≤B:=by
  simp [increment,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,atIncrement,savedDepth,savedOne,depthB]
 have incrementRun:=block_runs increment program 73 n B x atIncrement inc_code rfl saveRun.final_bound (by change 74≤B;omega) isafe.1 isafe.2
 let installed:=applyBlock increment atIncrement
 let child:State:={installed with pc:=0}
 have cb:=changePC_bound B installed 0 incrementRun.final_bound (by omega)
 have preserved (i:ℕ) (hi:i≠4151 ∧ i≠4152 ∧ i≠4153 ∧ i≠4154):child.natReg i=s.natReg i:=by
  have h:=nr i hi.2.1
  simpa [child,installed,increment,applyBlock,Op.apply,evalNat,writeNat,next,atIncrement,saveChild,pushed,pushSetup,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2] using h
 have allScalars:child.scalarHeap=s.scalarHeap:=ssh
 obtain ⟨acted,ar,av,_,af,_,_⟩:=UniformBinaryBatchCMachine.execution n B k count A x child v rfl
  ((preserved _ (by omega)).trans bits) ((preserved _ (by omega)).trans arrays)
  ((preserved _ (by omega)).trans base) ((preserved _ (by omega)).trans size)
  (by simpa only [allScalars] using data) ha (by simpa only [UniformBinaryCStageMachine.Constants,allScalars] using con)
  (by omega) extent cb
 have batchRun:=UniformBoundedAssembly.boundedExecution_placed batch_code (by change 128≤B;omega) (by omega) ar
 have childpc:installed.pc=74:=by simp [installed,increment,applyBlock,Op.apply,writeNat,next,atIncrement]
 have placedChild:placed 74 child=installed:=by change {installed with pc:=74}=installed;rw [←childpc]
 rw [placedChild] at batchRun
 let atPop:State:={acted with pc:=128}
 have childKeep(i:ℕ)(hi:¬UniformBinaryBatchCMachine.Changed i):acted.natReg i=child.natReg i:=af.natReg i hi
 have popDepth:atPop.natReg 4151=depth+1:=by
  have h:=childKeep 4151 (by simp [UniformBinaryBatchCMachine.Changed,UniformBinaryTensorCMachine.Changed])
  simpa [atPop,child,installed,increment,applyBlock,Op.apply,evalNat,writeNat,next,atIncrement,savedDepth,savedOne] using h
 have popStack:atPop.natReg 4150=stack:=by
  have h:=childKeep 4150 (by simp [UniformBinaryBatchCMachine.Changed,UniformBinaryTensorCMachine.Changed])
  exact h.trans ((preserved _ (by omega)).trans sp)
 have popSafe:readable popSetup atPop ∧ peak popSetup atPop≤B:=by
  simp [popSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,popDepth,popStack,mulB,ptrB]
  omega
 have popRun:=block_runs popSetup program 128 n B x atPop pop_code rfl batchRun.final_bound (by change 133≤B;omega) popSafe.1 popSafe.2
 let popped:=applyBlock popSetup atPop
 let loadChild:State:={popped with pc:=0}
 have lb:=changePC_bound B popped 0 popRun.final_bound (by omega)
 have loadPtr:loadChild.natReg 4152=stack+34*depth:=by simp [loadChild,popped,popSetup,applyBlock,Op.apply,evalNat,writeNat,next,popDepth,popStack,Nat.mul_comm]
 have loadOne:loadChild.natReg 4153=1:=by simp [loadChild,popped,popSetup,applyBlock,Op.apply,evalNat,writeNat,next]
 have bankNow:Stack.Bank Stack.fields (stack+34*depth) s.natReg loadChild:=by
  intro j hj
  have b:=bank j hj
  have nh:loadChild.natHeap=saved.natHeap:=af.natHeap
  rw [nh]
  have fi:Stack.fields[j]'hj≠4152 ∧ Stack.fields[j]'hj≠4153:=UniformRecursiveReturnStackMachine.fields_safe _ (List.getElem_mem hj)
  have all4:∀i∈Stack.fields,i≠4154:=by decide
  have f4:=all4 _ (List.getElem_mem hj)
  simpa [saveChild,pushed,pushSetup,applyBlock,Op.apply,evalNat,writeNat,next,fi.1,fi.2,f4] using b
 obtain ⟨restored,rr,rpc,rvalues,rptr,rnh,rnr,rsh,rsr,ro,rro⟩:=UniformRecursiveReturnStackMachine.load_execution
  n B (stack+34*depth) s.natReg x loadChild rfl loadPtr loadOne bankNow (fun i _=>bound.2.1 i) lb (by omega) endB
 have re:BoundedExecution Stack.loadProgram n x B loadChild 69 restored:=by
  convert rr.executes (.halt rr.final_bound (by simp [step,rpc,load_halt])) using 1
 have restoreRun:=UniformBoundedAssembly.boundedExecution_placed load_code (by change 202≤B;omega) (by omega) re
 have popPC:popped.pc=133:=by simp [popped,popSetup,applyBlock,Op.apply,writeNat,next,atPop]
 have placedLoad:placed 133 loadChild=popped:=by change {popped with pc:=133}=popped;rw [←popPC]
 rw [placedLoad] at restoreRun
 let u:State:={restored with pc:=202}
 have last:BoundedExecution program n x B u 1 u:=.halt restoreRun.final_bound (by simp [step,u,halt_at])
 refine ⟨u,?_,rfl,?_,rvalues,?_,?_,?_,?_,?_⟩
 · convert (pushRun.trans (saveRun.trans (incrementRun.trans (batchRun.trans (popRun.trans restoreRun))))).executes last using 1
   simp [pushSetup,increment,popSetup];omega
 · intro w z
   simpa only [u,rsh,loadChild,popped,popSetup,applyBlock,Op.apply,writeNat,next,atPop] using av w z
 · have h:=rnr 4151 (by omega) (by decide)
   have actedDepth:acted.natReg 4151=depth+1:=popDepth
   simpa [u,loadChild,popped,popSetup,applyBlock,Op.apply,evalNat,writeNat,next,atPop,actedDepth] using h
 · intro z hz
   have hz':z<stack+34*depth∨stack+34*depth+34≤z:=by
    rcases hz with h|h
    · exact Or.inl h
    · right
      simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h
   exact (congrFun rnh z).trans ((congrFun af.natHeap z).trans (sh z hz'))
 · intro z hz
   exact (congrFun rsh z).trans ((af.scalarHeap z hz).trans (congrFun allScalars z))
 · exact ro.trans (af.outputs.trans so)
 · exact rro.trans (af.roots.trans sro)

end
end ExactFourierCircuits.UniformRecursiveBaseCallMachine
