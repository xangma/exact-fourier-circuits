import UniformDirectLeafDescriptorMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeDescriptorMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformNewtonTableMachine (putWords putWords_append putWords_get putWords_before putWords_after)
open UniformFixedNetworkScheduleMachine (Printed)
structure Record where
 kind:ℕ
 dest:ℕ
 source:ℕ
 coefficient:ℕ
 deriving Inhabited,DecidableEq
def Record.words(r:Record):List ℕ:=[r.kind,r.dest,r.source,r.coefficient]
def Record.transpose(r:Record):Record:=⟨r.kind,r.source,r.dest,r.coefficient⟩
lemma Record.words_length(r:Record):r.words.length=4:=rfl
lemma Record.transpose_transpose(r:Record):r.transpose.transpose=r:=rfl
def reverseWords(f:ℕ→Record):ℕ→List ℕ
 | 0=>[]
 | i+1=>(f i).transpose.words++reverseWords f i
lemma reverseWords_length(f:ℕ→Record)(i:ℕ):(reverseWords f i).length=4*i:=by
 induction i with
 | zero=>rfl
 | succ i ih=>simp only [reverseWords,List.length_append,Record.words_length,ih];omega
lemma reverseWords_range(f:ℕ→Record)(i:ℕ):
 reverseWords f i=((List.range i).reverse.flatMap fun j=>(f j).transpose.words):=by
 induction i with
 | zero=>rfl
 | succ i ih=>simp [reverseWords,List.range_succ,List.reverse_append,ih]

/-- Reverse record traversal and physical endpoint exchange. Scale endpoints are
identical, so the same literal routine transposes both record kinds. -/
def boot:List Op:=[.literal 5510 0,.literal 5511 1,.literal 5512 4,
 .add 5513 5500 5510,.add 5514 5502 5510,.literal 5515 0]
def body:List Op:=[.sub 5513 5513 5511,.mul 5515 5513 5512,.add 5515 5501 5515,
 .getNat 5516 5515,.add 5515 5515 5511,.getNat 5517 5515,.add 5515 5515 5511,
 .getNat 5518 5515,.add 5515 5515 5511,.getNat 5519 5515,
 .putNat 5514 5516,.add 5514 5514 5511,.putNat 5514 5518,.add 5514 5514 5511,
 .putNat 5514 5517,.add 5514 5514 5511,.putNat 5514 5519,.add 5514 5514 5511]
def program:Program:=boot.map Op.code++[.branchLT 5510 5513 7 26]++body.map Op.code++[.jump 6,.halt]
lemma program_length:program.length=27:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<6 at hi;interval_cases i <;>rfl
lemma body_code:BlockAt body program 7:=by intro i hi;change i<18 at hi;interval_cases i <;>rfl
lemma outer_at:program[6]?=some (.branchLT 5510 5513 7 26):=rfl
lemma jump_at:program[25]?=some (.jump 6):=rfl
lemma halt_at:program[26]?=some .halt:=rfl
noncomputable section
structure Header(N T D:ℕ)(s:State):Prop where
 count:s.natReg 5500=N
 source:s.natReg 5501=T
 dest:s.natReg 5502=D
structure Cursor(N T D i A:ℕ)(s:State):Prop where
 header:Header N T D s
 zero:s.natReg 5510=0
 one:s.natReg 5511=1
 four:s.natReg 5512=4
 index:s.natReg 5513=i
 address:s.natReg 5514=A
def Bank(T N:ℕ)(f:ℕ→Record)(s:State):Prop:=
 ∀i,i < N→∀j:Fin 4,s.natHeap (T+4*i+j.val)=some ((f i).words[j.val]'j.isLt)
structure Frame(s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,r<5510∨5520≤r→u.natReg r=s.natReg r
lemma Frame.refl(s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans{s u v:State}(f:Frame s u)(g:Frame u v):Frame s v:=
 ⟨g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma Frame.pc{s u:State}(f:Frame s u)(p:ℕ):Frame s (setPC u p):=
 ⟨f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Cursor.pc{N T D i A:ℕ}{s:State}(h:Cursor N T D i A s)(p:ℕ):Cursor N T D i A (setPC s p):=
 ⟨⟨h.header.count,h.header.source,h.header.dest⟩,h.zero,h.one,h.four,h.index,h.address⟩
lemma Bank.pc{T N:ℕ}{f:ℕ→Record}{s:State}(h:Bank T N f s)(p:ℕ):Bank T N f (setPC s p):=h
lemma boot_frame(s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma body_frame(s:State):Frame s (applyBlock body s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr;simp (disch:=omega) [body,applyBlock,Op.apply,writeNat,next]
lemma initialized{N T D:ℕ}(s:State)(h:Header N T D s):Cursor N T D N D (applyBlock boot s):=by
 constructor
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,h.count,h.source,h.dest]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.count]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.dest]
lemma boot_safe{N T D B:ℕ}(s:State)(h:Header N T D s)(hs:WordBound B s)(code:27≤B):
 readable boot s∧peak boot s≤B:=by
 have nb:=hs.2.1 5500;rw [h.count] at nb
 have db:=hs.2.1 5502;rw [h.dest] at db
 simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.count,h.dest];omega

lemma body_semantics{N T D i A:ℕ}{f:ℕ→Record}(s:State)(h:Cursor N T D (i+1) A s)
 (bank:Bank T N f s)(hi:i < N):
 Cursor N T D i (A+4) (applyBlock body s)∧
 (applyBlock body s).natHeap=putWords A (f i).transpose.words s.natHeap:=by
 have a:=bank i hi ⟨0,by decide⟩
 have b:=bank i hi ⟨1,by decide⟩
 have c:=bank i hi ⟨2,by decide⟩
 have d:=bank i hi ⟨3,by decide⟩
 simp only [Record.words,List.getElem_cons_zero,List.getElem_cons_succ,Nat.mul_comm,Nat.add_assoc,Nat.add_zero] at a b c d
 constructor
 · constructor
   · constructor <;>simp [body,applyBlock,Op.apply,writeNat,next,h.header.count,h.header.source,h.header.dest]
   · simp [body,applyBlock,Op.apply,writeNat,next,h.zero]
   · simp [body,applyBlock,Op.apply,writeNat,next,h.one]
   · simp [body,applyBlock,Op.apply,writeNat,next,h.four]
   · simp [body,applyBlock,Op.apply,writeNat,next,h.index,h.one]
   · simp [body,applyBlock,Op.apply,writeNat,next,h.address,h.one]
 · simp [body,applyBlock,Op.apply,writeNat,next,h.index,h.address,h.header.source,h.one,h.four,
   a,b,c,d,Nat.add_assoc,Record.transpose,Record.words,putWords]

lemma body_safe{N T D i A B:ℕ}{f:ℕ→Record}(s:State)(h:Cursor N T D (i+1) A s)
 (bank:Bank T N f s)(hi:i < N)(values:∀i,i < N→∀v∈(f i).words,v≤B)
 (tb:T+4*N≤B)(ab:A+4≤B):readable body s∧peak body s≤B:=by
 have a:=bank i hi ⟨0,by decide⟩
 have b:=bank i hi ⟨1,by decide⟩
 have c:=bank i hi ⟨2,by decide⟩
 have d:=bank i hi ⟨3,by decide⟩
 have va:(f i).kind≤B:=values i hi _ (by simp [Record.words])
 have vb:(f i).dest≤B:=values i hi _ (by simp [Record.words])
 have vc:(f i).source≤B:=values i hi _ (by simp [Record.words])
 have vd:(f i).coefficient≤B:=values i hi _ (by simp [Record.words])
 simp only [Record.words,List.getElem_cons_zero,List.getElem_cons_succ,Nat.mul_comm,Nat.add_assoc,Nat.add_zero] at a b c d
 simp [body,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.index,h.address,h.header.source,h.one,h.four,a,b,c,d,Nat.add_assoc]
 omega

lemma body_bank{N T D i A:ℕ}{f:ℕ→Record}(s:State)(h:Cursor N T D (i+1) A s)
 (bank:Bank T N f s)(hi:i < N)(apart:T+4*N≤A):Bank T N f (applyBlock body s):=by
 intro j hj c
 rw [(body_semantics s h bank hi).2]
 rw [putWords_before A (f i).transpose.words s.natHeap (T+4*j+c.val) (by have cc:=c.isLt;omega)]
 exact bank j hj c

lemma loop(n N T D i A B:ℕ)(f:ℕ→Record)(x:Fin n→ℂ)(s:State)
 (h:Cursor N T D i A s)(pc:s.pc=6)(hs:WordBound B s)(bank:Bank T N f s)(hi:i≤N)
 (code:27≤B)(tb:T+4*N≤B)(ab:A+4*i≤B)(apart:T+4*N≤A)
 (values:∀i,i < N→∀v∈(f i).words,v≤B):
 ∃u,BoundedRuns program n x B s (20*i) u∧u.pc=6∧Cursor N T D 0 (A+4*i) u∧
 u.natHeap=putWords A (reverseWords f i) s.natHeap∧Bank T N f u∧Frame s u:=by
 induction i generalizing A s with
 | zero=>exact ⟨s,by simpa using BoundedRuns.refl hs,pc,by simpa using h,rfl,bank,Frame.refl s⟩
 | succ i ih=>
   have ib:i < N:=by omega
   have choose:step program n x s=.running (setPC s 7):=by simp [step,pc,outer_at,h.zero,h.index,setPC]
   have branch:=UniformPreparationRowTableMachine.control_run program n B 7 x s hs (by omega) choose
   let a:=setPC s 7
   have ha:=h.pc 7
   have ba:=bank.pc 7
   have safe:=body_safe a ha ba ib values tb (by omega)
   have blocks:=block_runs body program 7 n B x a body_code rfl branch.final_bound (by change 25≤B;omega) safe.1 safe.2
   let z:=applyBlock body a
   have zp:z.pc=25:=by rw [applyBlock_pc];rfl
   have backStep:step program n x z=.running (setPC z 6):=by simp [step,zp,jump_at,setPC]
   have back:=UniformPreparationRowTableMachine.control_run program n B 6 x z blocks.final_bound (by omega) backStep
   obtain ⟨u,tail,up,final,heap,bankFinal,frame⟩:=ih (A+4) (setPC z 6)
     ((body_semantics a ha ba ib).1.pc 6) rfl back.final_bound
     ((body_bank a ha ba ib apart).pc 6) (by omega) (by omega) (by omega)
   refine ⟨u,?_,up,?_,?_,bankFinal,(((Frame.refl s).pc 7).trans ((body_frame a).pc 6)).trans frame⟩
   · convert branch.trans (blocks.trans (back.trans tail)) using 1;change 20*(i+1)=1+(18+(1+20*i));omega
   · simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
   · rw [heap]
     change putWords (A+4) (reverseWords f i) z.natHeap=putWords A (reverseWords f (i+1)) s.natHeap
     rw [(body_semantics a ha ba ib).2,reverseWords,putWords_append,Record.words_length];rfl

/-- Physical transposition retains the source bank and every nonworking cell. -/
theorem execution(n N T D B:ℕ)(f:ℕ→Record)(x:Fin n→ℂ)(s:State)
 (h:Header N T D s)(pc:s.pc=0)(hs:WordBound B s)(bank:Bank T N f s)
 (code:27≤B)(tb:T+4*N≤B)(db:D+4*N≤B)(apart:T+4*N≤D):
 ∃u,BoundedExecution program n x B s (20*N+8) u∧u.pc=26∧
 Printed D (reverseWords f N) u∧Bank T N f u∧u.natReg 5514=D+4*N∧
 (∀z,z<D∨D+4*N≤z→u.natHeap z=s.natHeap z)∧Frame s u:=by
 have values:∀i,i < N→∀v∈(f i).words,v≤B:=by
   intro i hi v hv
   obtain ⟨j,hj,rfl⟩:=List.mem_iff_getElem.mp hv
   have jj:j<4:=by simpa only [Record.words_length] using hj
   exact (hs.2.2.1 (T+4*i+j) _ (bank i hi ⟨j,jj⟩)).2
 have safe:=boot_safe s h hs code
 have init:=block_runs boot program 0 n B x s boot_code pc hs (by change 6≤B;omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=6:=by rw [applyBlock_pc,pc];rfl
 have ba:Bank T N f a:=by simpa only [Bank,a,boot,applyBlock,Op.apply,writeNat,next] using bank
 obtain ⟨w,run,wp,final,heap,bankFinal,frame⟩:=loop n N T D N D B f x a (initialized s h) ap init.final_bound ba
   (by omega) code tb db apart values
 have choose:step program n x w=.running (setPC w 26):=by simp [step,wp,outer_at,final.zero,final.index,setPC]
 have stop:=UniformPreparationRowTableMachine.control_run program n B 26 x w run.final_bound (by omega) choose
 have halt:BoundedExecution program n x B (setPC w 26) 1 (setPC w 26):=
   .halt stop.final_bound (by simp [step,setPC,halt_at])
 refine ⟨setPC w 26,?_,rfl,?_,bankFinal.pc 26,final.address,?_,((boot_frame s).trans frame).pc 26⟩
 · convert init.executes (run.executes (stop.executes halt)) using 1;change 20*N+8=6+(20*N+(1+1));omega
 · intro j hj
   change w.natHeap (D+j)=some ((reverseWords f N)[j]'hj)
   rw [heap,putWords_get D (reverseWords f N) a.natHeap j hj,List.getElem?_eq_getElem hj]
 · intro z hz
   change w.natHeap z=s.natHeap z
   rw [heap]
   rcases hz with before|after
   · rw [putWords_before D (reverseWords f N) a.natHeap z before];rfl
   · rw [putWords_after D (reverseWords f N) a.natHeap z (by rw [reverseWords_length];exact after)];rfl

lemma flatWords_length(rs:List Record):(rs.flatMap Record.words).length=4*rs.length:=by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [List.flatMap_cons,List.length_append,Record.words_length,List.length_cons,ih];omega

def recordAt(rs:List Record)(i:ℕ):Record:=(rs[i]?).getD default
lemma recordAt_range(rs:List Record):(List.range rs.length).map (recordAt rs)=rs:=by
 apply List.ext_getElem
 · simp
 · intro j hj hl
   simp only [List.getElem_map,List.getElem_range,recordAt,List.getElem?_eq_getElem hl,Option.getD_some]

lemma bank_of_printed(T:ℕ)(rs:List Record)(s:State)(printed:Printed T (rs.flatMap Record.words) s):
 Bank T rs.length (recordAt rs) s:=by
 induction rs generalizing T with
 | nil=>intro i hi;simp at hi
 | cons r rs ih=>
   change Printed T (r.words++rs.flatMap Record.words) s at printed
   obtain ⟨first,rest⟩:=printed.split
   have tail:=ih (T+4) (by simpa only [Record.words_length] using rest)
   intro i hi j
   cases i with
   | zero=>
     simp only [recordAt,List.getElem?_cons_zero,Option.getD_some,Nat.mul_zero,Nat.add_zero]
     exact first j.val j.isLt
   | succ i=>
     have ii:i < rs.length:=by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
     simpa [recordAt,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail i ii j

lemma reverseWords_records(rs:List Record):
 reverseWords (recordAt rs) rs.length=(rs.reverse.map Record.transpose).flatMap Record.words:=by
 rw [reverseWords_range]
 conv_rhs=>rw [←recordAt_range rs]
 simp only [←List.map_reverse,List.flatMap_map,List.map_map,Function.comp_def]

/-- Numeric leaf records have the same four fields as the direct printer. -/
def ofOperation{v:ℕ}(o K:ℕ):UniformDirectToeplitz.Operation v→Record
 | .scale i=>⟨0,o+i.val,o+i.val,K⟩
 | .shear i j=>⟨1,o+i.val,o+j.val,K+(i.val-j.val)⟩
lemma ofOperation_words{v:ℕ}(o K:ℕ)(op:UniformDirectToeplitz.Operation v):
 (ofOperation o K op).words=UniformDirectLeafDescriptorMachine.operationWords o K op:=by cases op <;>rfl

def leafRecords(v o K:ℕ):List Record:=(UniformDirectToeplitz.topology v).map (ofOperation o K)
lemma leafRecords_words(v o K:ℕ):
 (leafRecords v o K).flatMap Record.words=UniformDirectLeafDescriptorMachine.rows o K v:=by
 rw [leafRecords,List.flatMap_map,List.flatMap_def]
 simp only [ofOperation_words]
 exact UniformDirectLeafDescriptorMachine.topology_words o K v
lemma leafRecords_length(v o K:ℕ):(leafRecords v o K).length=v+v*(v-1)/2:=by
 rw [leafRecords,List.length_map,UniformDirectToeplitz.topology_length]
lemma leaf_bank{n v o K D B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (_run:BoundedExecution UniformDirectLeafDescriptorMachine.program n x B s t u)
 (printed:Printed D (UniformDirectLeafDescriptorMachine.rows o K v) u):
 Bank D (leafRecords v o K).length (recordAt (leafRecords v o K)) u:=
 bank_of_printed D (leafRecords v o K) u (by rw [leafRecords_words];exact printed)
end
end ExactFourierCircuits.UniformTransposeDescriptorMachine
