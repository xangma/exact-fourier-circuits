import UniformRecursiveResidualControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualControlJoin
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
open UniformFixedNetworkScheduleMachine (Printed Record)
namespace C
export UniformRecursiveResidualControl (Frame Changed markOps initOps edgeOps block_jump)
end C
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section

/-- Precise cursor and end projections supplement the deliberately broad
common control frame. This lemma is proved at symbolic code addresses. -/
theorem mark_init_generic (main:Program)(start init ret n B work T dimension recordEnd inverse:ℕ)
 (x:Fin n→ℂ)(s:State)(pc:s.pc=start)(header:s.natReg 4123=work)(one:s.natReg 4153=1)
 (cursor:s.natReg 2850=T)(dim:s.natReg 2857=dimension)(endHeader:s.natReg 2865=recordEnd)
 (iv:s.natReg 2856=inverse)(bound:WordBound B s)(six:6 ≤ B)
 (markCode:BlockAt C.markOps main start)(follow:start+4=init)
 (initCode:BlockAt C.initOps main init)(jump:main[init+4]?=some (.jump ret))
 (markEnd:start+4 ≤ B)(initEnd:init+5 ≤ B)(returnBound:ret ≤ B):∃u,
 BoundedRuns main n x B s 9 u ∧ u.pc=ret ∧ u.natReg 2850=T ∧
 u.natReg 4134=0 ∧ u.natReg 4132=dimension ∧ u.natReg 4130=recordEnd ∧ u.natReg 4131=inverse ∧
 u.natHeap (work-6)=some 0 ∧ C.Frame work s u:=by
 have workBound:work ≤ B:=by have z:=bound.2.1 4123;rwa[header] at z
 have safe:readable C.markOps s∧peak C.markOps s ≤ B:=by
  simp [C.markOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,header];omega
 have marked:=block_runs C.markOps main start n B x s markCode pc bound markEnd safe.1 safe.2
 let a:=applyBlock C.markOps s
 have ap:a.pc=init:=by rw[UniformRecursiveNodePreparation.block_pc,pc];exact follow
 have mf:=UniformRecursiveResidualControl.mark_frame work s header
 have aOne:a.natReg 4153=1:=(mf.natReg _ (by unfold C.Changed;omega)).trans one
 have aDim:a.natReg 2857=dimension:=(mf.natReg _ (by unfold C.Changed;omega)).trans dim
 have aEnd:a.natReg 2865=recordEnd:=(mf.natReg _ (by unfold C.Changed;omega)).trans endHeader
 have aInv:a.natReg 2856=inverse:=(mf.natReg _ (by unfold C.Changed;omega)).trans iv
 have db:=marked.final_bound.2.1 2857;rw[aDim] at db
 have eb:=marked.final_bound.2.1 2865;rw[aEnd] at eb
 have ib:=marked.final_bound.2.1 2856;rw[aInv] at ib
 have initSafe:readable C.initOps a∧peak C.initOps a ≤ B:=by
  simp [C.initOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,aOne,aDim,aEnd,aInv];omega
 have initialized:=C.block_jump main C.initOps init ret n B x a initCode jump ap marked.final_bound
  initEnd returnBound initSafe.1 initSafe.2
 let u:=setPC (applyBlock C.initOps a) ret
 have run:BoundedRuns main n x B s 9 u:=by
  simpa only [u,C.markOps,C.initOps,List.length_cons,List.length_nil] using marked.trans initialized
 refine ⟨u,run,rfl,?_,?_,?_,?_,?_,?_,mf.trans (UniformRecursiveResidualControl.init_frame work a ret)⟩
 · simp [u,a,setPC,C.markOps,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next,cursor]
 · simp [u,setPC,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next]
 · simp [u,setPC,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next,aDim,aOne]
 · simp [u,setPC,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next,aEnd,aOne]
 · simp [u,setPC,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next,aInv,aOne]
 · simp [u,a,setPC,C.markOps,C.initOps,applyBlock,Op.apply,evalNat,writeNat,next,header]

theorem raw_entry_cursor (work T tapeEnd n B:ℕ)(r:Record)
 (x:Fin n→ℂ)(s:State)(pc:s.pc=P.address .loop)(workHeader:s.natReg 4123=work)
 (ptr:s.natReg 2850=T)(one:s.natReg 4153=1)(metadata:s.natHeap (work-1)=some tapeEnd)(live:T<tapeEnd)
 (bank:Printed T r.data s)(good:UniformFixedNetworkOpcodeMachine.WellFormed r)
 (opcode:r.opcode=0)(bound:WordBound B s)(code:P.program.length ≤ B)
 (recordEnd:T+r.data.length ≤ B)(width:r.width+1 ≤ B)(workLower:6 ≤ work):∃u t,
 BoundedRuns P.program n x B s 46 u ∧ u.pc=P.address .directionTest ∧ u.natReg 2850=T ∧
 u.natReg 4134=0 ∧ u.natReg 4132=r.dimension ∧ u.natReg 4130=T+r.data.length ∧ u.natReg 4131=r.inverse ∧
 u.natHeap (work-6)=some 0 ∧ u.natHeap (work-1)=some tapeEnd ∧
 u.natHeap (work-2)=s.natHeap (work-2) ∧
 UniformRecursiveRecordControl.ControlFrame s t ∧ C.Frame work t u:=by
 obtain ⟨t,readRun,tp,fields,_,endField,cf⟩:=UniformRecursiveRecordControl.read_dispatch_execution
  work T tapeEnd B n r x s pc workHeader ptr one metadata live bank good bound recordEnd width code
 have op:(⟨r.opcode,good.1⟩:Fin 7)=0:=Fin.ext opcode
 have atMark:t.pc=P.address .residualMark:=UniformRecursiveResidualControl.residual_pc t.pc
  (tp.trans (congrArg UniformRecursiveRecordControl.targets op))
 have tWork:t.natReg 4123=work:=(cf.natReg _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans workHeader
 have tOne:t.natReg 4153=1:=(cf.natReg _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans one
 have six:6 ≤ B:=by have z:=readRun.final_bound.2.1 4123;rw[tWork] at z;omega
 obtain ⟨u,run,up,uc,idx,dim,fin,iv,mode,fr⟩:=mark_init_generic P.program
  (P.address .residualMark) (P.address .residualInit) (P.address .directionTest) n B work T
  r.dimension (T+r.data.length) r.inverse x t atMark tWork tOne fields.cursor fields.dimension endField fields.inverse
  readRun.final_bound six UniformRecursiveResidualControl.mark_code UniformRecursiveResidualControl.mark_follow
  UniformRecursiveResidualControl.init_code UniformRecursiveResidualControl.init_jump
  (UniformRecursiveParentReturn.code_bound .residualMark 4 B rfl code)
  (UniformRecursiveParentReturn.code_bound .residualInit 5 B rfl code)
  (UniformRecursiveParentReturn.start_bound .directionTest B code)
 refine ⟨u,t,?_,up,uc,idx,dim,fin,iv,mode,?_,?_,cf,fr⟩
 · have total:=readRun.trans run
   have charge:4+UniformFixedNetworkOpcodeMachine.headCost r+UniformRecursiveRecordControl.dispatchCost r.opcode+9=46:=by
    have z:=UniformRecursiveResidualControl.raw_entry_charge r opcode;omega
   simpa only [charge] using total
 · rw[fr.natHeap _ (by omega),cf.natHeap];exact metadata
 · rw[fr.natHeap _ (by omega),cf.natHeap]

theorem edge_generic_finish (main:Program)(start mainNext padNext n B work flag:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=start)(one:s.natReg 4153=1)(header:s.natReg 4123=work)(mode:s.natHeap (work-6)=some flag)
 (bound:WordBound B s)(atCode:BlockAt C.edgeOps main start)
 (branch:main[start+3]?=some (.branchLT 4177 4153 mainNext padNext))
 (codeEnd:start+4 ≤ B)(six:6 ≤ B)(mainBound:mainNext ≤ B)(padBound:padNext ≤ B):∃u,
 BoundedRuns main n x B s 4 u ∧ u.pc=(if flag<1 then mainNext else padNext) ∧
 u.natReg 4130=s.natReg 4130 ∧ u.natHeap=s.natHeap ∧ C.Frame work s u:=by
 have wb:work ≤ B:=by have h:=bound.2.1 4123;rwa[header] at h
 have fb:flag ≤ B:=(bound.2.2.1 (work-6) flag mode).2
 have safe:readable C.edgeOps s∧peak C.edgeOps s ≤ B:=by
  simp [C.edgeOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,header,mode];omega
 have run:=block_runs C.edgeOps main start n B x s atCode pc bound (by change start+3 ≤ B;omega) safe.1 safe.2
 let t:=applyBlock C.edgeOps s
 have tp:t.pc=start+3:=by rw[UniformRecursiveNodePreparation.block_pc,pc];rfl
 have flagT:t.natReg 4177=flag:=by simp [t,C.edgeOps,applyBlock,Op.apply,evalNat,writeNat,next,header,mode]
 have oneT:t.natReg 4153=1:=by simp [t,C.edgeOps,applyBlock,Op.apply,evalNat,writeNat,next,one]
 have last:=UniformRecursiveRecordControl.branch_control main (start+3) mainNext padNext n B 4177 4153 x t
  branch tp run.final_bound mainBound padBound
 let u:=setPC t (if flag<1 then mainNext else padNext)
 have last':BoundedRuns main n x B t 1 u:=by simpa only[u,setPC,flagT,oneT] using last
 refine ⟨u,?_,rfl,?_,rfl,UniformRecursiveResidualControl.edge_frame work s _⟩
 · simpa only[u,C.edgeOps,List.length_cons,List.length_nil] using run.trans last'
 · simp [u,t,setPC,C.edgeOps,applyBlock,Op.apply,evalNat,writeNat,next]
theorem edge_done_finish (n B work flag:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .edgeDone)(one:s.natReg 4153=1)(header:s.natReg 4123=work)
 (mode:s.natHeap (work-6)=some flag)(bound:WordBound B s)(code:P.program.length ≤ B):∃u,
 BoundedRuns P.program n x B s 4 u ∧
 u.pc=(if flag<1 then P.address .recordAdvance else P.address .paddingNext) ∧
 u.natReg 4130=s.natReg 4130 ∧ u.natHeap=s.natHeap ∧ C.Frame work s u:=
 edge_generic_finish P.program (P.address .edgeDone) (P.address .recordAdvance) (P.address .paddingNext)
  n B work flag x s pc one header mode bound UniformRecursiveResidualControl.edge_code
  UniformRecursiveResidualControl.edge_branch (UniformRecursiveParentReturn.code_bound .edgeDone 4 B rfl code)
  (UniformRecursiveResidualControl.six_bound _ B (UniformRecursiveParentReturn.code_bound .unitSetup 12 B rfl code))
  (UniformRecursiveParentReturn.start_bound .recordAdvance B code) (UniformRecursiveParentReturn.start_bound .paddingNext B code)
end
end ExactFourierCircuits.UniformRecursiveResidualControlJoin
