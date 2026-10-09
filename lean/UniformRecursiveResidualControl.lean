import UniformRecursiveRecordControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualControl
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (Part program address size piece order offset)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
noncomputable section

lemma offset_append_unseen {α:Type*}[DecidableEq α](size:α→ℕ)(pre tail:List α)(a:α)
 (fresh:a∉pre):P.offset size (pre++tail) a=(pre.map size).sum+P.offset size tail a:=by
 induction pre with
 | nil=>simp
 | cons b bs ih=>
  have ne:b≠a:=by intro h;subst b;exact fresh (by simp)
  have f:a∉bs:=by intro h;exact fresh (by simp [h])
  simp only [List.cons_append,P.offset,ne,ite_false,List.map_cons,List.sum_cons,ih f,Nat.add_assoc]
lemma adjacent_offset {α:Type*}[DecidableEq α](size:α→ℕ)(whole pre tail:List α)(a b:α)
 (eq:whole=pre++a::b::tail)(fa:a∉pre)(fb:b∉pre)(ne:a≠b):
 P.offset size whole a+size a=P.offset size whole b:=by
 rw [eq,offset_append_unseen size pre _ a fa,offset_append_unseen size pre _ b fb]
 simp only [P.offset,ite_true,ne,ite_false,Nat.add_zero]

def markPrefix:List P.Part:=P.order.take 13
def markTail:List P.Part:=P.order.drop 15
lemma follow_addresses {α:Type*}[DecidableEq α](addr:α→ℕ)(size:α→ℕ)(whole pre tail:List α)(a b:α)
 (definition:addr=(fun v=>P.offset size whole v))(eq:whole=pre++a::b::tail)
 (fa:a∉pre)(fb:b∉pre)(ne:a≠b)(len:size a=4):addr a+4=addr b:=by
 rw [definition,←len]
 exact adjacent_offset size whole pre tail a b eq fa fb ne
lemma mark_follow:P.address .residualMark+4=P.address .residualInit:=
 follow_addresses P.address P.size P.order markPrefix markTail .residualMark .residualInit rfl rfl
  (by decide) (by decide) (by decide) rfl
lemma six_bound (loc B:ℕ)(h:loc+12≤B):6≤B:=by omega

lemma block_jump (main:Program)(ops:List Op)(loc ret n B:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt ops main loc)(atJump:main[loc+ops.length]?=some (.jump ret))
 (pc:s.pc=loc)(bound:WordBound B s)(codeEnd:loc+ops.length+1≤B)(returnBound:ret≤B)
 (reads:readable ops s)(values:peak ops s≤B):
 BoundedRuns main n x B s (ops.length+1) (setPC (applyBlock ops s) ret):=by
 have run:=block_runs ops main loc n B x s atCode pc bound (by omega) reads values
 have tp:(applyBlock ops s).pc=loc+ops.length:=by rw [UniformRecursiveNodePreparation.block_pc,pc]
 have ub:=changePC_bound B _ ret run.final_bound returnBound
 have jump:BoundedRuns main n x B (applyBlock ops s) 1 (setPC (applyBlock ops s) ret):=
  .next run.final_bound (by simp only [step,tp,atJump];rfl) (.refl ub)
 exact run.trans jump

def markOps:List Op:=[.literal 4179 6,.binary .sub 4178 4123 4179,.literal 4177 0,.store 4178 4177]
def initOps:List Op:=[.literal 4134 0,.binary .mul 4132 2857 4153,.binary .mul 4130 2865 4153,.binary .mul 4131 2856 4153]
def nextOps:List Op:=[.binary .add 4134 4134 4153]
def advanceOps:List Op:=[.binary .mul 2850 4130 4153]
def edgeOps:List Op:=[.literal 4179 6,.binary .sub 4178 4123 4179,.load 4177 4178]
def Changed (j:ℕ):Prop:=j=4177∨j=4178∨j=4179∨j=4134∨j=4132∨j=4130∨j=4131∨j=2850
structure Frame (work:ℕ)(s u:State):Prop where
 natHeap:∀a,a≠work-6→u.natHeap a=s.natHeap a
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
lemma Frame.trans {work:ℕ}{s t u:State}(a:Frame work s t)(b:Frame work t u):Frame work s u:=
 ⟨fun adr h=>(b.natHeap adr h).trans (a.natHeap adr h),b.scalarHeap.trans a.scalarHeap,
 b.scalarReg.trans a.scalarReg,b.outputs.trans a.outputs,b.roots.trans a.roots,
 fun j h=>(b.natReg j h).trans (a.natReg j h)⟩
lemma mark_frame (work:ℕ)(s:State)(header:s.natReg 4123=work):Frame work s (applyBlock markOps s):=by
 refine ⟨?_,rfl,rfl,rfl,rfl,?_⟩
 · intro a h;simp [markOps,applyBlock,Op.apply,evalNat,writeNat,next,header,h]
 · intro j hj;unfold Changed at hj;simp (disch:=omega) [markOps,applyBlock,Op.apply,evalNat,writeNat,next]
lemma init_frame (work:ℕ)(s:State)(ret:ℕ):Frame work s (setPC (applyBlock initOps s) ret):=by
 refine ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [setPC,initOps,applyBlock,Op.apply,evalNat,writeNat,next]
lemma next_frame (work:ℕ)(s:State)(ret:ℕ):Frame work s (setPC (applyBlock nextOps s) ret):=by
 refine ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [setPC,nextOps,applyBlock,Op.apply,evalNat,writeNat,next]
lemma advance_frame (work:ℕ)(s:State)(ret:ℕ):Frame work s (setPC (applyBlock advanceOps s) ret):=by
 refine ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [setPC,advanceOps,applyBlock,Op.apply,evalNat,writeNat,next]
lemma edge_frame (work:ℕ)(s:State)(ret:ℕ):Frame work s (setPC (applyBlock edgeOps s) ret):=by
 refine ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [setPC,edgeOps,applyBlock,Op.apply,evalNat,writeNat,next]

/-- The real opcode0 marks its own metadata mode before entering residual
initialization. Neither the mode cell nor the following PC is supplied. -/
theorem mark_generic (main:Program)(loc ret n B work:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt markOps main loc)(follows:loc+4=ret)(pc:s.pc=loc)(header:s.natReg 4123=work)
 (bound:WordBound B s)(codeEnd:loc+4≤B)(literals:6≤B):∃u,
 BoundedRuns main n x B s 4 u ∧ u.pc=ret ∧ u.natHeap (work-6)=some 0 ∧ Frame work s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa [header] at h
 have safe:readable markOps s∧peak markOps s≤B:=by
  simp [markOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,header];omega
 have run:=block_runs markOps main loc n B x s atCode pc bound codeEnd safe.1 safe.2
 have up:(applyBlock markOps s).pc=ret:=by rw [UniformRecursiveNodePreparation.block_pc,pc];exact follows
 refine ⟨applyBlock markOps s,run,up,?_,mark_frame work s header⟩
 simp [markOps,applyBlock,Op.apply,evalNat,writeNat,next,header]
lemma mark_code:BlockAt markOps P.program (P.address .residualMark):=
 UniformRecursiveSavingExecution.part_block .residualMark markOps [] rfl
theorem mark_execution (n B work:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .residualMark)(header:s.natReg 4123=work)(bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 4 u ∧ u.pc=P.address .residualInit ∧ u.natHeap (work-6)=some 0 ∧ Frame work s u:=
 mark_generic P.program (P.address .residualMark) (P.address .residualInit) n B work x s mark_code mark_follow pc header bound
 (R.code_bound .residualMark 4 B rfl code) (six_bound _ B (R.code_bound .unitSetup 12 B rfl code))

/-- Real decoded dimension, record end and inverse flag become the direction
controller's state through charged copies and an actual jump. -/
theorem init_generic (main:Program)(loc ret n B work dimension recordEnd inverse:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt initOps main loc)(atJump:main[loc+4]?=some (.jump ret))
 (pc:s.pc=loc)(one:s.natReg 4153=1)(dim:s.natReg 2857=dimension)
 (endHeader:s.natReg 2865=recordEnd)(iv:s.natReg 2856=inverse)(bound:WordBound B s)
 (codeEnd:loc+5≤B)(returnBound:ret≤B):∃u,
 BoundedRuns main n x B s 5 u ∧ u.pc=ret ∧ u.natReg 4134=0 ∧ u.natReg 4132=dimension ∧
 u.natReg 4130=recordEnd ∧ u.natReg 4131=inverse ∧ u.natHeap=s.natHeap ∧ Frame work s u:=by
 have db:dimension≤B:=by have h:=bound.2.1 2857;rwa [dim] at h
 have eb:recordEnd≤B:=by have h:=bound.2.1 2865;rwa [endHeader] at h
 have ib:inverse≤B:=by have h:=bound.2.1 2856;rwa [iv] at h
 have safe:readable initOps s∧peak initOps s≤B:=by
  simp [initOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,dim,endHeader,iv,db,eb,ib]
 have run:=block_jump main initOps loc ret n B x s atCode atJump pc bound codeEnd returnBound safe.1 safe.2
 refine ⟨setPC (applyBlock initOps s) ret,run,rfl,?_,?_,?_,?_,rfl,init_frame work s ret⟩
 all_goals simp [setPC,initOps,applyBlock,Op.apply,evalNat,writeNat,next,one,dim,endHeader,iv]
lemma init_code:BlockAt initOps P.program (P.address .residualInit):=
 UniformRecursiveSavingExecution.part_block .residualInit initOps _ rfl
lemma init_jump:P.program[P.address .residualInit+4]?=some (.jump (P.address .directionTest)):=
 UniformRecursiveSavingExecution.part_at .residualInit 4 (by decide)
theorem init_execution (n B work dimension recordEnd inverse:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .residualInit)(one:s.natReg 4153=1)(dim:s.natReg 2857=dimension)
 (endHeader:s.natReg 2865=recordEnd)(iv:s.natReg 2856=inverse)(bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 5 u ∧ u.pc=P.address .directionTest ∧ u.natReg 4134=0 ∧ u.natReg 4132=dimension ∧
 u.natReg 4130=recordEnd ∧ u.natReg 4131=inverse ∧ u.natHeap=s.natHeap ∧ Frame work s u:=
 init_generic P.program (P.address .residualInit) (P.address .directionTest) n B work dimension recordEnd inverse x s
 init_code init_jump pc one dim endHeader iv bound (R.code_bound .residualInit 5 B rfl code) (R.start_bound .directionTest B code)

lemma zero_cell (main:Program)(loc:ℕ)(op:Instruction)(h:main[loc+0]?=some op):main[loc]?=some op:=
 by simpa only [Nat.add_zero] using h
lemma test_code:P.program[P.address .directionTest]?=some (.branchLT 4134 4132 (P.address .gather) (P.address .edgeDone)):=
 zero_cell P.program (P.address .directionTest) _ (UniformRecursiveSavingExecution.part_at .directionTest 0 (by decide))
theorem direction_test (n B index dimension:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .directionTest)(i:s.natReg 4134=index)(dim:s.natReg 4132=dimension)
 (bound:WordBound B s)(code:P.program.length≤B):
 BoundedRuns P.program n x B s 1 (setPC s (if index<dimension then P.address .gather else P.address .edgeDone)):=by
 have h:=UniformRecursiveRecordControl.branch_control P.program (P.address .directionTest) (P.address .gather)
  (P.address .edgeDone) n B 4134 4132 x s test_code pc bound (R.start_bound .gather B code) (R.start_bound .edgeDone B code)
 simpa only [i,dim,setPC] using h

theorem next_generic (main:Program)(loc ret n B work index:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt nextOps main loc)(atJump:main[loc+1]?=some (.jump ret))
 (pc:s.pc=loc)(one:s.natReg 4153=1)(i:s.natReg 4134=index)(nextBound:index+1≤B)
 (bound:WordBound B s)(codeEnd:loc+2≤B)(returnBound:ret≤B):∃u,
 BoundedRuns main n x B s 2 u ∧ u.pc=ret ∧ u.natReg 4134=index+1 ∧ u.natHeap=s.natHeap ∧ Frame work s u:=by
 have safe:readable nextOps s∧peak nextOps s≤B:=by
  simp [nextOps,readable,peak,Op.readable,Op.peak,evalNat,i,one,nextBound]
 have run:=block_jump main nextOps loc ret n B x s atCode atJump pc bound codeEnd returnBound safe.1 safe.2
 refine ⟨setPC (applyBlock nextOps s) ret,run,rfl,?_,rfl,next_frame work s ret⟩
 simp [setPC,nextOps,applyBlock,Op.apply,evalNat,writeNat,next,i,one]
lemma next_code:BlockAt nextOps P.program (P.address .directionNext):=
 UniformRecursiveSavingExecution.part_block .directionNext nextOps _ rfl
lemma next_jump:P.program[P.address .directionNext+1]?=some (.jump (P.address .directionTest)):=
 UniformRecursiveSavingExecution.part_at .directionNext 1 (by decide)
theorem direction_next (n B work index:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .directionNext)(one:s.natReg 4153=1)(i:s.natReg 4134=index)(nextBound:index+1≤B)
 (bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 2 u ∧ u.pc=P.address .directionTest ∧ u.natReg 4134=index+1 ∧
 u.natHeap=s.natHeap ∧ Frame work s u:=
 next_generic P.program (P.address .directionNext) (P.address .directionTest) n B work index x s next_code next_jump
 pc one i nextBound bound (R.code_bound .directionNext 2 B rfl code) (R.start_bound .directionTest B code)

/-- The actual mode cell selects main-record advance or padded-role advance.
The flag is loaded physically after all directions; no branch result is supplied. -/
theorem edge_generic (main:Program)(loc mainNext paddedNext n B work flag:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt edgeOps main loc)(atBranch:main[loc+3]?=some (.branchLT 4177 4153 mainNext paddedNext))
 (pc:s.pc=loc)(one:s.natReg 4153=1)(header:s.natReg 4123=work)(mode:s.natHeap (work-6)=some flag)
 (bound:WordBound B s)(codeEnd:loc+4≤B)(literals:6≤B)(mb:mainNext≤B)(pb:paddedNext≤B):∃u,
 BoundedRuns main n x B s 4 u ∧ u.pc=(if flag<1 then mainNext else paddedNext) ∧
 u.natHeap=s.natHeap ∧ Frame work s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa [header] at h
 have fb:flag≤B:=(bound.2.2.1 (work-6) flag mode).2
 have safe:readable edgeOps s∧peak edgeOps s≤B:=by
  simp [edgeOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,header,mode];omega
 have run:=block_runs edgeOps main loc n B x s atCode pc bound (by change loc+3≤B;omega) safe.1 safe.2
 let t:=applyBlock edgeOps s
 have tp:t.pc=loc+3:=by rw [UniformRecursiveNodePreparation.block_pc,pc];rfl
 have fm:t.natReg 4177=flag:=by simp [t,edgeOps,applyBlock,Op.apply,evalNat,writeNat,next,header,mode]
 have unit:t.natReg 4153=1:=by simp [t,edgeOps,applyBlock,Op.apply,evalNat,writeNat,next,one]
 have br:=UniformRecursiveRecordControl.branch_control main (loc+3) mainNext paddedNext n B 4177 4153 x t
  atBranch tp run.final_bound mb pb
 have last:BoundedRuns main n x B t 1 (setPC t (if flag<1 then mainNext else paddedNext)):=by simpa only [fm,unit,setPC] using br
 exact ⟨setPC t (if flag<1 then mainNext else paddedNext),run.trans last,rfl,rfl,edge_frame work s _⟩
lemma edge_code:BlockAt edgeOps P.program (P.address .edgeDone):=
 UniformRecursiveSavingExecution.part_block .edgeDone edgeOps _ rfl
lemma edge_branch:P.program[P.address .edgeDone+3]?=some (.branchLT 4177 4153 (P.address .recordAdvance) (P.address .paddingNext)):=
 UniformRecursiveSavingExecution.part_at .edgeDone 3 (by decide)
theorem edge_done (n B work flag:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .edgeDone)(one:s.natReg 4153=1)(header:s.natReg 4123=work)(mode:s.natHeap (work-6)=some flag)
 (bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 4 u ∧ u.pc=(if flag<1 then P.address .recordAdvance else P.address .paddingNext) ∧
 u.natHeap=s.natHeap ∧ Frame work s u:=
 edge_generic P.program (P.address .edgeDone) (P.address .recordAdvance) (P.address .paddingNext) n B work flag x s
 edge_code edge_branch pc one header mode bound (R.code_bound .edgeDone 4 B rfl code)
 (six_bound _ B (R.code_bound .unitSetup 12 B rfl code)) (R.start_bound .recordAdvance B code) (R.start_bound .paddingNext B code)

theorem advance_generic (main:Program)(loc ret n B work recordEnd:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt advanceOps main loc)(atJump:main[loc+1]?=some (.jump ret))
 (pc:s.pc=loc)(one:s.natReg 4153=1)(endHeader:s.natReg 4130=recordEnd)
 (bound:WordBound B s)(codeEnd:loc+2≤B)(returnBound:ret≤B):∃u,
 BoundedRuns main n x B s 2 u ∧ u.pc=ret ∧ u.natReg 2850=recordEnd ∧ u.natHeap=s.natHeap ∧ Frame work s u:=by
 have eb:recordEnd≤B:=by have h:=bound.2.1 4130;rwa [endHeader] at h
 have safe:readable advanceOps s∧peak advanceOps s≤B:=by
  simp [advanceOps,readable,peak,Op.readable,Op.peak,evalNat,endHeader,one,eb]
 have run:=block_jump main advanceOps loc ret n B x s atCode atJump pc bound codeEnd returnBound safe.1 safe.2
 refine ⟨setPC (applyBlock advanceOps s) ret,run,rfl,?_,rfl,advance_frame work s ret⟩
 simp [setPC,advanceOps,applyBlock,Op.apply,evalNat,writeNat,next,endHeader,one]
lemma advance_code:BlockAt advanceOps P.program (P.address .recordAdvance):=
 UniformRecursiveSavingExecution.part_block .recordAdvance advanceOps _ rfl
lemma advance_jump:P.program[P.address .recordAdvance+1]?=some (.jump (P.address .loop)):=
 UniformRecursiveSavingExecution.part_at .recordAdvance 1 (by decide)
theorem record_advance (n B work recordEnd:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .recordAdvance)(one:s.natReg 4153=1)(endHeader:s.natReg 4130=recordEnd)
 (bound:WordBound B s)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 2 u ∧ u.pc=P.address .loop ∧ u.natReg 2850=recordEnd ∧ u.natHeap=s.natHeap ∧ Frame work s u:=
 advance_generic P.program (P.address .recordAdvance) (P.address .loop) n B work recordEnd x s advance_code advance_jump
 pc one endHeader bound (R.code_bound .recordAdvance 2 B rfl code) (R.start_bound .loop B code)

lemma vector_zero (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 0):pc=a:=h
lemma residual_pc (pc:ℕ)(h:pc=UniformRecursiveRecordControl.targets 0):pc=P.address .residualMark:=
 vector_zero pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma raw_entry_charge (r:UniformFixedNetworkScheduleMachine.Record)(opcode:r.opcode=0):
 4+UniformFixedNetworkOpcodeMachine.headCost r+UniformRecursiveRecordControl.dispatchCost r.opcode+4+5=46:=by
 simp [UniformFixedNetworkOpcodeMachine.headCost,UniformRecursiveRecordControl.dispatchCost,opcode]

/-- Physical main-loop opcode0 enters the real direction controller. The
header, record end and mode marker are produced by the charged path. -/
theorem raw_residual_entry (work T tapeEnd n B:ℕ)(r:UniformFixedNetworkScheduleMachine.Record)
 (x:Fin n→ℂ)(s:State)(pc:s.pc=P.address .loop)(workHeader:s.natReg 4123=work)
 (ptr:s.natReg 2850=T)(one:s.natReg 4153=1)(metadata:s.natHeap (work-1)=some tapeEnd)(live:T<tapeEnd)
 (bank:UniformFixedNetworkScheduleMachine.Printed T r.data s)(good:UniformFixedNetworkOpcodeMachine.WellFormed r)
 (opcode:r.opcode=0)(bound:WordBound B s)(code:P.program.length≤B)
 (recordEnd:T+r.data.length≤B)(width:r.width+1≤B)(workLower:6≤work):∃u t,
 BoundedRuns P.program n x B s 46 u ∧ u.pc=P.address .directionTest ∧
 u.natReg 4134=0 ∧ u.natReg 4132=r.dimension ∧ u.natReg 4130=T+r.data.length ∧ u.natReg 4131=r.inverse ∧
 u.natHeap (work-6)=some 0 ∧ u.natHeap (work-1)=some tapeEnd ∧
 u.natHeap (work-2)=s.natHeap (work-2) ∧
 UniformRecursiveRecordControl.ControlFrame s t ∧ Frame work t u:=by
 obtain ⟨t,readRun,tp,fields,_,endField,cf⟩:=UniformRecursiveRecordControl.read_dispatch_execution
  work T tapeEnd B n r x s pc workHeader ptr one metadata live bank good bound recordEnd width code
 have op:(⟨r.opcode,good.1⟩:Fin 7)=0:=Fin.ext opcode
 have atMark:t.pc=P.address .residualMark:=residual_pc t.pc (tp.trans (congrArg UniformRecursiveRecordControl.targets op))
 have tWork:t.natReg 4123=work:=(cf.natReg _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans workHeader
 have tOne:t.natReg 4153=1:=(cf.natReg _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans one
 obtain ⟨a,markRun,ap,mode,mf⟩:=mark_execution n B work x t atMark tWork readRun.final_bound code
 have aOne:a.natReg 4153=1:=(mf.natReg _ (by unfold Changed;omega)).trans tOne
 have aDim:a.natReg 2857=r.dimension:=(mf.natReg _ (by unfold Changed;omega)).trans fields.dimension
 have aEnd:a.natReg 2865=T+r.data.length:=(mf.natReg _ (by unfold Changed;omega)).trans endField
 have aInverse:a.natReg 2856=r.inverse:=(mf.natReg _ (by unfold Changed;omega)).trans fields.inverse
 obtain ⟨u,initRun,up,index,dim,ep,iv,heap,inf⟩:=init_execution n B work r.dimension (T+r.data.length) r.inverse x a
  ap aOne aDim aEnd aInverse markRun.final_bound code
 have fr:=mf.trans inf
 have me:u.natHeap (work-6)=some 0:=by rw [heap];exact mode
 have main:u.natHeap (work-1)=some tapeEnd:=by
  rw [fr.natHeap _ (by omega),cf.natHeap];exact metadata
 have unit:u.natHeap (work-2)=s.natHeap (work-2):=by rw [fr.natHeap _ (by omega),cf.natHeap]
 refine ⟨u,t,?_,up,index,dim,ep,iv,me,main,unit,cf,fr⟩
 have total:BoundedRuns P.program n x B s
  (4+UniformFixedNetworkOpcodeMachine.headCost r+UniformRecursiveRecordControl.dispatchCost r.opcode+4+5) u:=
  (readRun.trans markRun).trans initRun
 rw [raw_entry_charge r opcode] at total
 exact total

end
end ExactFourierCircuits.UniformRecursiveResidualControl
