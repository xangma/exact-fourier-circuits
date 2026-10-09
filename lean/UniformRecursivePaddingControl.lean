import UniformRecursiveRecordControl
import UniformRecursiveNodeJoin
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingControl
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
open UniformFixedNetworkScheduleMachine (Record Printed)
namespace P
export UniformRecursiveSavingProgram (program address unitRecord)
end P
namespace R
export UniformRecursiveParentReturn (code_bound start_bound)
end R
noncomputable section

def initOps:List Op := [.literal 4179 6,.binary .sub 4178 4123 4179,
 .store 4178 4153,.binary .add 4178 4178 4153,.store 4178 2865,
 .binary .add 4178 4178 4153,.store 4178 2854,
 .binary .add 4178 4178 4153,.binary .add 4177 2854 2855,.store 4178 4177]
def testOps:List Op := [.literal 4179 4,.binary .sub 4178 4123 4179,
 .load 4175 4178,.binary .add 4178 4178 4153,.load 4176 4178]
def patchOps:List Op := [.literal 4179 2,.binary .sub 4178 4123 4179,.load 2850 4178,
 .literal 4177 3,.binary .add 4178 2850 4177,.store 4178 4175,
 .binary .add 4178 2850 4153,.store 4178 4060,.binary .mul 5300 4120 4153]
def nextOps:List Op := [.literal 4179 4,.binary .sub 4178 4123 4179,
 .load 4175 4178,.binary .add 4175 4175 4153,.store 4178 4175]
def finishOps:List Op := [.literal 4179 5,.binary .sub 4178 4123 4179,.load 2850 4178]
lemma init_length:initOps.length=10:=rfl
lemma test_length:testOps.length=5:=rfl
lemma patch_length:patchOps.length=9:=rfl
lemma next_length:nextOps.length=5:=rfl
lemma finish_length:finishOps.length=3:=rfl

def Changed (j:ℕ):Prop := (2850≤j∧j<2877)∨j=5300∨(4175≤j∧j<4180)
structure Frame (cells:List ℕ)(s u:State):Prop where
 natHeap:∀z,z∉cells→u.natHeap z=s.natHeap z
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
lemma Frame.pc {cells:List ℕ}{s u:State}(f:Frame cells s u)(pc:ℕ):Frame cells s (setPC u pc):=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma pure_fields (ops:List Op)(s:State):
 (applyBlock ops s).scalarHeap=s.scalarHeap ∧ (applyBlock ops s).scalarReg=s.scalarReg ∧
 (applyBlock ops s).outputs=s.outputs ∧ (applyBlock ops s).rootOrders=s.rootOrders:=by
 induction ops generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl⟩
 | cons o os ih=>cases o <;> exact ih _
lemma run_jump (main:Program)(start exit n B:ℕ)(ops:List Op)(x:Fin n→ℂ)(s:State)
 (link:BlockAt ops main start)(jump:main[start+ops.length]?=some (.jump exit))
 (pc:s.pc=start)(bound:WordBound B s)(extent:start+ops.length+1≤B)(ret:exit≤B)
 (safe:readable ops s∧peak ops s≤B):
 BoundedRuns main n x B s (ops.length+1) (setPC (applyBlock ops s) exit):=by
 have run:=block_runs ops main start n B x s link pc bound (by omega) safe.1 safe.2
 have atPC:(applyBlock ops s).pc=start+ops.length:=by rw [UniformRecursiveNodePreparation.block_pc,pc]
 have last:BoundedRuns main n x B (applyBlock ops s) 1 (setPC (applyBlock ops s) exit):=
  .next run.final_bound (by simp only [step,atPC,jump];rfl)
   (.refl (changePC_bound B _ _ run.final_bound ret))
 exact run.trans last
lemma coordinates (work:ℕ)(low:6≤work):
 work-6+1=work-5 ∧ work-6+1+1=work-4 ∧ work-6+1+1+1=work-3 ∧ work-4+1=work-3:=by omega

def initHeap (work saved dest count:ℕ)(s:State):ℕ→Option ℕ:=
 Function.update (Function.update (Function.update (Function.update s.natHeap
  (work-6) (some 1)) (work-5) (some saved)) (work-4) (some dest)) (work-3) (some (dest+count))
lemma init_heap (work saved dest count:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=dest)(c:s.natReg 2855=count)(low:6≤work):
 (applyBlock initOps s).natHeap=initHeap work saved dest count s:=by
 have cs:=coordinates work low
 have c1:work-5+1=work-4:=by omega
 have c2:work-4+1=work-3:=by omega
 simp [initOps,applyBlock,Op.apply,evalNat,writeNat,next,w,one,sp,d,c,cs.1,c1,c2,initHeap]
lemma init_frame (work saved dest count:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=dest)(c:s.natReg 2855=count)(low:6≤work):
 Frame [work-6,work-5,work-4,work-3] s (applyBlock initOps s):=by
 have fs:=pure_fields initOps s
 refine ⟨?_,fs.1,fs.2.1,fs.2.2.1,fs.2.2.2,?_⟩
 · intro z hz
   rw [init_heap work saved dest count s w one sp d c low]
   simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hz
   simp only [initHeap,Function.update_of_ne hz.2.2.2,Function.update_of_ne hz.2.2.1,Function.update_of_ne hz.2.1,Function.update_of_ne hz.1]
 · intro j hj;unfold Changed at hj
   simp (disch:=omega) [initOps,applyBlock,Op.apply,evalNat,writeNat,next]

theorem init_generic (main:Program)(start exit n B work saved dest count:ℕ)(x:Fin n→ℂ)(s:State)
 (link:BlockAt initOps main start)(jump:main[start+10]?=some (.jump exit))
 (pc:s.pc=start)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=dest)(c:s.natReg 2855=count)
 (low:6≤work)(bound:WordBound B s)(code:start+11≤B)(ret:exit≤B)(endBound:dest+count≤B):∃u,
 BoundedRuns main n x B s 11 u ∧ u.pc=exit ∧
 u.natHeap (work-6)=some 1 ∧ u.natHeap (work-5)=some saved ∧
 u.natHeap (work-4)=some dest ∧ u.natHeap (work-3)=some (dest+count) ∧
 Frame [work-6,work-5,work-4,work-3] s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa [w] at h
 have sb:saved≤B:=by have h:=bound.2.1 2865;rwa [sp] at h
 have db:dest≤B:=by omega
 have cs:=coordinates work low
 have safe:readable initOps s∧peak initOps s≤B:=by
  simp [initOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,sp,d,c,
   cs.1,sb,endBound]
  omega
 have run:=run_jump main start exit n B initOps x s link jump pc bound code ret safe
 let u:=setPC (applyBlock initOps s) exit
 have hp:u.natHeap=initHeap work saved dest count s:=init_heap work saved dest count s w one sp d c low
 have a:work-6≠work-5:=by omega
 have b:work-6≠work-4:=by omega
 have c0:work-6≠work-3:=by omega
 have e:work-5≠work-4:=by omega
 have f:work-5≠work-3:=by omega
 have g:work-4≠work-3:=by omega
 refine ⟨u,run,rfl,?_,?_,?_,?_,(init_frame work saved dest count s w one sp d c low).pc exit⟩
 all_goals rw [hp];simp only [initHeap,Function.update_self,Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c0,Function.update_of_ne e,Function.update_of_ne f,Function.update_of_ne g]

lemma test_frame (s:State):Frame [] s (applyBlock testOps s):=by
 have fs:=pure_fields testOps s
 refine ⟨fun _ _=>rfl,fs.1,fs.2.1,fs.2.2.1,fs.2.2.2,?_⟩
 intro j hj;unfold Changed at hj
 simp (disch:=omega) [testOps,applyBlock,Op.apply,evalNat,writeNat,next]
theorem test_generic (main:Program)(start yes no n B work role last:ℕ)(x:Fin n→ℂ)(s:State)
 (link:BlockAt testOps main start)(branch:main[start+5]?=some (.branchLT 4175 4176 yes no))
 (pc:s.pc=start)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(_low:6≤work)
 (current:s.natHeap (work-4)=some role)(endpoint:s.natHeap (work-3)=some last)
 (bound:WordBound B s)(code:start+6≤B)(yb:yes≤B)(nb:no≤B):∃u,
 BoundedRuns main n x B s 6 u ∧ u.pc=(if role<last then yes else no) ∧
 u.natReg 4175=role ∧ u.natReg 4176=last ∧ Frame [] s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa [w] at h
 have rb:role≤B:=(bound.2.2.1 _ _ current).2
 have lb:last≤B:=(bound.2.2.1 _ _ endpoint).2
 have cs:work-4+1=work-3:=by omega
 have safe:readable testOps s∧peak testOps s≤B:=by
  simp [testOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,current,endpoint,cs,rb,lb]
  omega
 have run:=block_runs testOps main start n B x s link pc bound (by rw[test_length];omega) safe.1 safe.2
 let t:=applyBlock testOps s
 have tp:t.pc=start+5:=by rw [UniformRecursiveNodePreparation.block_pc,pc,test_length]
 have tr:t.natReg 4175=role:=by simp [t,testOps,applyBlock,Op.apply,evalNat,writeNat,next,w,current]
 have te:t.natReg 4176=last:=by simp [t,testOps,applyBlock,Op.apply,evalNat,writeNat,next,w,one,endpoint,cs]
 have lastRun:=UniformRecursiveRecordControl.branch_control main (start+5) yes no n B 4175 4176 x t branch tp run.final_bound yb nb
 let u:=setPC t (if role<last then yes else no)
 have r:BoundedRuns main n x B t 1 u:=by simpa only [u,setPC,tr,te] using lastRun
 exact ⟨u,by simpa only[test_length] using run.trans r,rfl,tr,te,(test_frame s).pc _⟩

-- Only these two header fields change; all directions and other fields remain.
def patchRecord (r:Record)(q role:ℕ):Record:={r with columns:=q,dest:=role}
lemma patch_length_same (r:Record)(q role:ℕ):(patchRecord r q role).data.length=r.data.length:=by
 simp only [Record.data_length,patchRecord]
lemma patch_good (r:Record)(q role:ℕ)(h:UniformFixedNetworkOpcodeMachine.WellFormed r):
 UniformFixedNetworkOpcodeMachine.WellFormed (patchRecord r q role):=by
 change r.opcode<7 ∧ r.directions.length=UniformFixedNetworkOpcodeMachine.bodyLength (patchRecord r q role)
 have body:UniformFixedNetworkOpcodeMachine.bodyLength (patchRecord r q role)=UniformFixedNetworkOpcodeMachine.bodyLength r:=rfl
 rw [body];exact h
lemma patch_twice (r:Record)(q0 role0 q role:ℕ):patchRecord (patchRecord r q0 role0) q role=patchRecord r q role:=by cases r;rfl
lemma patched_get (r:Record)(q role j:ℕ)(hj:j<r.data.length)(a:j≠1)(b:j≠3):
 (patchRecord r q role).data[j]'(by rw[patch_length_same];exact hj)=r.data[j]'hj:=by
 by_cases h:j<8
 · interval_cases j <;> simp_all [patchRecord,Record.data,Record.header]
 · have h1:r.header.length≤j:=by rw [Record.header_length];omega
   have h2:(patchRecord r q role).header.length≤j:=by rw [Record.header_length];omega
   simp only [Record.data]
   rw [List.getElem_append_right h2,List.getElem_append_right h1]
   simp only [Record.header_length,patchRecord]
lemma printed_patch (U q role:ℕ)(r:Record)(s:State)(bank:Printed U r.data s):
 Printed U (patchRecord r q role).data
  {s with natHeap:=Function.update (Function.update s.natHeap (U+3) (some role)) (U+1) (some q)}:=by
 intro j hj
 have old:j<r.data.length:=by rwa[patch_length_same] at hj
 by_cases a:j=1
 · subst j;simp [patchRecord,Record.data,Record.header]
 · by_cases b:j=3
   · subst j;simp [patchRecord,Record.data,Record.header]
   · have a0:U+j≠U+1:=by omega
     have b0:U+j≠U+3:=by omega
     simp only [Function.update_of_ne a0,Function.update_of_ne b0,patched_get r q role j old a b]
     exact bank j old

lemma patch_heap (work U q role k:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k):
 (applyBlock patchOps s).natHeap=Function.update (Function.update s.natHeap (U+3) (some role)) (U+1) (some q):=by
 simp [patchOps,applyBlock,Op.apply,evalNat,writeNat,next,w,one,ptr,col,dst,bits]
lemma patch_frame (work U q role k:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k):
 Frame [U+1,U+3] s (applyBlock patchOps s):=by
 have fs:=pure_fields patchOps s
 refine ⟨?_,fs.1,fs.2.1,fs.2.2.1,fs.2.2.2,?_⟩
 · intro z hz
   rw [patch_heap work U q role k s w one ptr col dst bits]
   simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hz
   simp only [Function.update_of_ne hz.1,Function.update_of_ne hz.2]
 · intro j hj;unfold Changed at hj
   simp (disch:=omega) [patchOps,applyBlock,Op.apply,evalNat,writeNat,next]

theorem patch_generic (main:Program)(start exit n B work U q role k:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (link:BlockAt patchOps main start)(jump:main[start+9]?=some (.jump exit))
 (pc:s.pc=start)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(_low:6≤work)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k)
 (bank:Printed U r.data s)(bound:WordBound B s)(code:start+10≤B)(ret:exit≤B)(headerEnd:U+4≤B):∃u,
 BoundedRuns main n x B s 10 u ∧ u.pc=exit ∧ u.natReg 2850=U ∧ u.natReg 5300=k ∧
 Printed U (patchRecord r q role).data u ∧ Frame [U+1,U+3] s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have qb:q≤B:=by have h:=bound.2.1 4060;rwa[col] at h
 have rb:role≤B:=by have h:=bound.2.1 4175;rwa[dst] at h
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa[bits] at h
 have safe:readable patchOps s∧peak patchOps s≤B:=by
  simp [patchOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,ptr,col,dst,bits,qb,rb,kb]
  omega
 have run:=run_jump main start exit n B patchOps x s link jump pc bound code ret safe
 let u:=setPC (applyBlock patchOps s) exit
 have heap:u.natHeap=Function.update (Function.update s.natHeap (U+3) (some role)) (U+1) (some q):=patch_heap work U q role k s w one ptr col dst bits
 have bp:u.natReg 2850=U:=by simp[u,setPC,patchOps,applyBlock,Op.apply,evalNat,writeNat,next,w,ptr]
 have nk:u.natReg 5300=k:=by simp[u,setPC,patchOps,applyBlock,Op.apply,evalNat,writeNat,next,one,bits]
 have out:Printed U (patchRecord r q role).data u:=by
  intro j hj;rw[heap];exact printed_patch U q role r s bank j hj
 exact ⟨u,run,rfl,bp,nk,out,(patch_frame work U q role k s w one ptr col dst bits).pc exit⟩

lemma next_heap (work role:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(current:s.natHeap (work-4)=some role):
 (applyBlock nextOps s).natHeap=Function.update s.natHeap (work-4) (some (role+1)):=by
 simp[nextOps,applyBlock,Op.apply,evalNat,writeNat,next,w,one,current]
lemma next_frame (work role:ℕ)(s:State)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(current:s.natHeap (work-4)=some role):
 Frame [work-4] s (applyBlock nextOps s):=by
 have fs:=pure_fields nextOps s
 refine ⟨?_,fs.1,fs.2.1,fs.2.2.1,fs.2.2.2,?_⟩
 · intro z hz;rw[next_heap work role s w one current]
   have ne:z≠work-4:=by simpa only[List.mem_singleton] using hz
   exact Function.update_of_ne ne _ _
 · intro j hj;unfold Changed at hj
   simp (disch:=omega)[nextOps,applyBlock,Op.apply,evalNat,writeNat,next]
theorem next_generic (main:Program)(start exit n B work role:ℕ)(x:Fin n→ℂ)(s:State)
 (link:BlockAt nextOps main start)(jump:main[start+5]?=some (.jump exit))
 (pc:s.pc=start)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(_low:6≤work)
 (current:s.natHeap (work-4)=some role)(bound:WordBound B s)(code:start+6≤B)(ret:exit≤B)(increment:role+1≤B):∃u,
 BoundedRuns main n x B s 6 u ∧ u.pc=exit ∧ u.natHeap (work-4)=some (role+1) ∧ Frame [work-4] s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have safe:readable nextOps s∧peak nextOps s≤B:=by
  simp[nextOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,current]
  omega
 have run:=run_jump main start exit n B nextOps x s link jump pc bound code ret safe
 let u:=setPC (applyBlock nextOps s) exit
 have cell:u.natHeap (work-4)=some (role+1):=by
  change (applyBlock nextOps s).natHeap (work-4)=_
  rw[next_heap work role s w one current];exact Function.update_self _ _ _
 exact ⟨u,run,rfl,cell,(next_frame work role s w one current).pc exit⟩
lemma finish_frame (s:State):Frame [] s (applyBlock finishOps s):=by
 have fs:=pure_fields finishOps s
 refine ⟨fun _ _=>rfl,fs.1,fs.2.1,fs.2.2.1,fs.2.2.2,?_⟩
 intro j hj;unfold Changed at hj
 simp (disch:=omega)[finishOps,applyBlock,Op.apply,evalNat,writeNat,next]
theorem finish_generic (main:Program)(start exit n B work saved:ℕ)(x:Fin n→ℂ)(s:State)
 (link:BlockAt finishOps main start)(jump:main[start+3]?=some (.jump exit))
 (pc:s.pc=start)(w:s.natReg 4123=work)(low:6≤work)(stored:s.natHeap (work-5)=some saved)
 (bound:WordBound B s)(code:start+4≤B)(ret:exit≤B):∃u,
 BoundedRuns main n x B s 4 u ∧ u.pc=exit ∧ u.natReg 2850=saved ∧ Frame [] s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have sb:saved≤B:=(bound.2.2.1 _ _ stored).2
 have safe:readable finishOps s∧peak finishOps s≤B:=by
  simp[finishOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,stored,sb]
  omega
 have run:=run_jump main start exit n B finishOps x s link jump pc bound code ret safe
 let u:=setPC (applyBlock finishOps s) exit
 have ptr:u.natReg 2850=saved:=by simp[u,setPC,finishOps,applyBlock,Op.apply,evalNat,writeNat,next,w,stored]
 exact ⟨u,run,rfl,ptr,(finish_frame s).pc exit⟩


lemma init_code : BlockAt initOps P.program (P.address .paddingInit):=
 UniformRecursiveSavingExecution.part_block .paddingInit _ _ rfl
lemma init_jump:P.program[P.address .paddingInit+10]?=some (.jump (P.address .paddingTest)):=
 UniformRecursiveSavingExecution.part_at .paddingInit 10 (by decide)
lemma test_code : BlockAt testOps P.program (P.address .paddingTest):=
 UniformRecursiveSavingExecution.part_block .paddingTest _ _ rfl
lemma test_branch:P.program[P.address .paddingTest+5]?=some (.branchLT 4175 4176 (P.address .paddingPatch) (P.address .paddingFinish)):=
 UniformRecursiveSavingExecution.part_at .paddingTest 5 (by decide)
lemma patch_code : BlockAt patchOps P.program (P.address .paddingPatch):=
 UniformRecursiveSavingExecution.part_block .paddingPatch _ _ rfl
lemma patch_jump:P.program[P.address .paddingPatch+9]?=some (.jump (P.address .paddingReader)):=
 UniformRecursiveSavingExecution.part_at .paddingPatch 9 (by decide)
lemma next_code : BlockAt nextOps P.program (P.address .paddingNext):=
 UniformRecursiveSavingExecution.part_block .paddingNext _ _ rfl
lemma next_jump:P.program[P.address .paddingNext+5]?=some (.jump (P.address .paddingTest)):=
 UniformRecursiveSavingExecution.part_at .paddingNext 5 (by decide)
lemma finish_code : BlockAt finishOps P.program (P.address .paddingFinish):=
 UniformRecursiveSavingExecution.part_block .paddingFinish _ _ rfl
lemma finish_jump:P.program[P.address .paddingFinish+3]?=some (.jump (P.address .loop)):=
 UniformRecursiveSavingExecution.part_at .paddingFinish 3 (by decide)
lemma reader_code:CodeAt UniformFixedNetworkOpcodeMachine.headProgram P.program
 (P.address .paddingReader) (P.address .residualInit):=UniformRecursiveSavingProgram.part_child rfl

theorem init_execution (n B work saved dest count:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingInit)(w:s.natReg 4123=work)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=dest)(c:s.natReg 2855=count)
 (low:6≤work)(bound:WordBound B s)(code:P.program.length≤B)(endBound:dest+count≤B):∃u,
 BoundedRuns P.program n x B s 11 u ∧ u.pc=P.address .paddingTest ∧
 u.natHeap (work-6)=some 1 ∧ u.natHeap (work-5)=some saved ∧
 u.natHeap (work-4)=some dest ∧ u.natHeap (work-3)=some (dest+count) ∧
 Frame [work-6,work-5,work-4,work-3] s u:=
 init_generic P.program (P.address .paddingInit) (P.address .paddingTest) n B work saved dest count x s
 init_code init_jump pc w one sp d c low bound (R.code_bound .paddingInit 11 B rfl code)
 (R.start_bound .paddingTest B code) endBound

theorem test_execution (n B work role last:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingTest)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(low:6≤work)
 (current:s.natHeap (work-4)=some role)(endpoint:s.natHeap (work-3)=some last)
 (bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 6 u ∧
 u.pc=(if role<last then P.address .paddingPatch else P.address .paddingFinish) ∧
 u.natReg 4175=role ∧ u.natReg 4176=last ∧ Frame [] s u:=
 test_generic P.program (P.address .paddingTest) (P.address .paddingPatch) (P.address .paddingFinish) n B work role last x s
 test_code test_branch pc w one low current endpoint bound (R.code_bound .paddingTest 6 B rfl code)
 (R.start_bound .paddingPatch B code) (R.start_bound .paddingFinish B code)

theorem patch_execution (n B work U q role k:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingPatch)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(low:6≤work)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k)
 (bank:Printed U r.data s)(bound:WordBound B s)(code:P.program.length≤B)(headerEnd:U+4≤B):∃u,
 BoundedRuns P.program n x B s 10 u ∧ u.pc=P.address .paddingReader ∧ u.natReg 2850=U ∧ u.natReg 5300=k ∧
 Printed U (patchRecord r q role).data u ∧ Frame [U+1,U+3] s u:=
 patch_generic P.program (P.address .paddingPatch) (P.address .paddingReader) n B work U q role k r x s
 patch_code patch_jump pc w one low ptr col dst bits bank bound (R.code_bound .paddingPatch 10 B rfl code)
 (R.start_bound .paddingReader B code) headerEnd

theorem next_execution (n B work role:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingNext)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(low:6≤work)
 (current:s.natHeap (work-4)=some role)(bound:WordBound B s)(code:P.program.length≤B)(increment:role+1≤B):∃u,
 BoundedRuns P.program n x B s 6 u ∧ u.pc=P.address .paddingTest ∧
 u.natHeap (work-4)=some (role+1) ∧ Frame [work-4] s u:=
 next_generic P.program (P.address .paddingNext) (P.address .paddingTest) n B work role x s
 next_code next_jump pc w one low current bound (R.code_bound .paddingNext 6 B rfl code)
 (R.start_bound .paddingTest B code) increment

theorem finish_execution (n B work saved:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingFinish)(w:s.natReg 4123=work)(low:6≤work)(stored:s.natHeap (work-5)=some saved)
 (bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 4 u ∧ u.pc=P.address .loop ∧ u.natReg 2850=saved ∧ Frame [] s u:=
 finish_generic P.program (P.address .paddingFinish) (P.address .loop) n B work saved x s
 finish_code finish_jump pc w low stored bound (R.code_bound .paddingFinish 4 B rfl code) (R.start_bound .loop B code)

lemma Frame.then_reader {cells:List ℕ}{s t u:State}(f:Frame cells s t)
 (g:UniformFixedNetworkOpcodeMachine.Frame t u):Frame cells s u:=by
 refine ⟨fun z hz=>by rw[g.natHeap];exact f.natHeap z hz,
 g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,
 g.roots.trans f.roots,?_⟩
 intro j hj
 exact (g.natReg j (by unfold Changed at hj;omega)).trans (f.natReg j hj)
lemma Frame.parent {cells:List ℕ}{s u:State}(f:Frame cells s u):
 u.natReg 4120=s.natReg 4120 ∧ u.natReg 4121=s.natReg 4121 ∧
 u.natReg 4122=s.natReg 4122 ∧ u.natReg 4127=s.natReg 4127 ∧
 u.natReg 4150=s.natReg 4150 ∧ u.natReg 4151=s.natReg 4151 ∧
 u.natReg 4153=s.natReg 4153 ∧ u.natReg 4123=s.natReg 4123:=by
 exact ⟨f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega),
 f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega),f.natReg _ (by unfold Changed;omega)⟩

open UniformFixedNetworkOpcodeMachine (Fields WellFormed headCost)
theorem reader_execution (U B n:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingReader)(ptr:s.natReg 2850=U)(bound:WordBound B s)(bank:Printed U r.data s)
 (good:WellFormed r)(extent:U+r.data.length≤B)(width:r.width+1≤B)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s (headCost r) u ∧ u.pc=P.address .residualInit ∧ Fields U r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=U+r.data.length ∧ UniformFixedNetworkOpcodeMachine.Frame s u:=
 UniformRecursiveRecordControl.reader_generic P.program (P.address .paddingReader) (P.address .residualInit) U B n r x s
 reader_code pc ptr bound bank good extent width (R.code_bound .paddingReader _ B rfl code) (R.start_bound .residualInit B code)

/-- Body-only bridge stays generic, so specializing the fixed table never
normalizes its list or addresses. -/
lemma body_source (m U q role:ℕ) (r:Record) (v:Fin m→Fin m→ZMod 2) (s:State)
 (len:r.directions.length=m*m)
 (word:∀j i:Fin m,r.directions[j.val*m+i.val]'(by rw[len];have hj:=j.isLt;have hi:=i.isLt;nlinarith)=(v j i).val)
 (bank:Printed U (patchRecord r q role).data s) (j:Fin m):
 UniformRepeatedMaskMachine.Source (U+8+j.val*m) (v j) s:=by
 intro i
 have h:=bank.body (j.val*m+i.val) (by
  change j.val*m+i.val<r.directions.length
  rw[len];have hj:=j.isLt;have hi:=i.isLt;nlinarith)
 have idx:j.val*m+i.val<r.directions.length:=by rw[len];have hj:=j.isLt;have hi:=i.isLt;nlinarith
 change s.natHeap (U+8+(j.val*m+i.val))=some (r.directions[j.val*m+i.val]'idx) at h
 rw [word] at h
 simpa only[Nat.add_assoc] using h
lemma unit_body_length:P.unitRecord.directions.length=ExplicitSeedBudget.m*ExplicitSeedBudget.m:=by
 simp only[UniformRecursiveSavingProgram.unitRecord,List.length_ofFn]
/-- Same physical unit body after any previous column/destination patch. -/
lemma unit_source (U q role:ℕ) (j:Fin ExplicitSeedBudget.m) (s:State)
 (bank:Printed U (patchRecord P.unitRecord q role).data s):
 UniformRepeatedMaskMachine.Source (U+8+j.val*ExplicitSeedBudget.m) (BinaryFrames.unit j) s:=
 body_source ExplicitSeedBudget.m U q role P.unitRecord BinaryFrames.unit s unit_body_length
 UniformRecursiveNodePreparation.unit_word bank j
lemma binaryUnit_good (m:ℕ):WellFormed (UniformRecursiveNodePreparation.binaryUnitRecord m):=by
 constructor
 · exact Nat.zero_lt_succ 6
 · simp only[UniformRecursiveNodePreparation.binaryUnitRecord,List.length_ofFn,UniformFixedNetworkOpcodeMachine.bodyLength,ite_true]
lemma unit_good:WellFormed P.unitRecord:=by
 rw[UniformRecursiveNodePreparation.unitRecord_eq];exact binaryUnit_good _
lemma columns_patch (r:Record) (q role:ℕ):patchRecord (r.withColumns q) q role=patchRecord r q role:=by cases r;rfl
lemma patch_headCost (r:Record)(q role:ℕ):headCost (patchRecord r q role)=headCost r:=rfl

/-- Raw patch followed by the actual relocated header reader. No child handler
or child-output premise occurs; the result is ready at residualInit. -/
theorem patch_read_generic (main:Program)(start reader exit n B work U q role k:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (link:BlockAt patchOps main start)(jump:main[start+9]?=some (.jump reader))
 (head:CodeAt UniformFixedNetworkOpcodeMachine.headProgram main reader exit)
 (pc:s.pc=start)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(low:6≤work)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k)
 (bank:Printed U r.data s)(good:WellFormed r)(bound:WordBound B s)
 (extent:U+r.data.length≤B)(width:r.width+1≤B)(patchBound:start+10≤B)
 (headBound:reader+UniformFixedNetworkOpcodeMachine.headProgram.length≤B)(ret:exit≤B):∃u,
 BoundedRuns main n x B s (10+headCost r) u ∧ u.pc=exit ∧ Fields U (patchRecord r q role) u ∧
 u.natReg 5300=k ∧ Printed U (patchRecord r q role).data u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=U+r.data.length ∧ Frame [U+1,U+3] s u:=by
 have headerEnd:U+4≤B:=by have len:=Record.data_length r;omega
 obtain ⟨t,run,tp,tu,tk,tbank,tf⟩:=patch_generic main start reader n B work U q role k r x s
  link jump pc w one low ptr col dst bits bank bound patchBound (by omega) headerEnd
 have e:U+(patchRecord r q role).data.length≤B:=by rw[patch_length_same];exact extent
 obtain ⟨u,read,up,fields,body,nextval,uf⟩:=UniformRecursiveRecordControl.reader_generic main reader exit U B n
  (patchRecord r q role) x t head tp tu run.final_bound tbank (patch_good r q role good) e width headBound ret
 have bankU:Printed U (patchRecord r q role).data u:=by intro j hj;rw[uf.natHeap];exact tbank j hj
 refine ⟨u,?_,up,fields,(uf.natReg _ (by omega)).trans tk,bankU,body,?_,tf.then_reader uf⟩
 · simpa only[patch_headCost] using run.trans read
 · simpa only[patch_length_same] using nextval

theorem patch_reader_execution (n B work U q role k:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .paddingPatch)(w:s.natReg 4123=work)(one:s.natReg 4153=1)(low:6≤work)
 (ptr:s.natHeap (work-2)=some U)(col:s.natReg 4060=q)(dst:s.natReg 4175=role)(bits:s.natReg 4120=k)
 (bank:Printed U r.data s)(good:WellFormed r)(bound:WordBound B s)
 (extent:U+r.data.length≤B)(width:r.width+1≤B)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s (10+headCost r) u ∧ u.pc=P.address .residualInit ∧ Fields U (patchRecord r q role) u ∧
 u.natReg 5300=k ∧ Printed U (patchRecord r q role).data u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=U+r.data.length ∧ Frame [U+1,U+3] s u:=
 patch_read_generic P.program (P.address .paddingPatch) (P.address .paddingReader) (P.address .residualInit)
 n B work U q role k r x s patch_code patch_jump reader_code pc w one low ptr col dst bits bank good bound extent width
 (R.code_bound .paddingPatch 10 B rfl code) (R.code_bound .paddingReader _ B rfl code) (R.start_bound .residualInit B code)

end
end ExactFourierCircuits.UniformRecursivePaddingControl
