import UniformPermutationMachine
import UniformNatBlockMachine
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalCRTConsumerMachine
open UniformMachine UniformAssembly UniformBoundedAssembly UniformNatBlockMachine

def firstSetup:List Op:=[.literal 7390 0,.binary .add 70 103 7390,
 .binary .add 71 6026 7390,.binary .add 72 6025 7390,.binary .add 73 7311 7390]
def secondSetup:List Op:=[.binary .add 70 103 7390,.binary .add 71 6025 7390,
 .binary .add 72 6026 7390,.binary .add 73 7310 7390]
def alphaSetup:List Op:=[.literal 7390 0,.binary .add 70 103 7390,
 .binary .add 71 7312 7390,.binary .add 72 6026 7390,.binary .add 73 7310 7390]
def program:Program:=firstSetup.map Op.code++UniformPermutationMachine.program.map (relocate 5 17)++
 secondSetup.map Op.code++UniformPermutationMachine.program.map (relocate 21 33)++[.halt]
def alphaProgram:Program:=alphaSetup.map Op.code++UniformPermutationMachine.program.map (relocate 5 17)++[.halt]
lemma program_length:program.length=34:=rfl
lemma alphaProgram_length:alphaProgram.length=18:=rfl
lemma first_setup_code:BlockAt firstSetup program 0:=by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma first_code:CodeAt UniformPermutationMachine.program program 5 17:=by
 intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma second_setup_code:BlockAt secondSetup program 17:=by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma second_code:CodeAt UniformPermutationMachine.program program 21 33:=by
 intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma halt_at:program[33]?=some .halt:=rfl
lemma alpha_setup_code:BlockAt alphaSetup alphaProgram 0:=by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma alpha_code:CodeAt UniformPermutationMachine.program alphaProgram 5 17:=by
 intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma alpha_halt_at:alphaProgram[17]?=some .halt:=rfl
noncomputable section

def Protected (j:ℕ):Prop:=(j<70∨81≤j)∧j≠7390
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,Protected j→u.natReg j=s.natReg j
 scalarReg:∀j,j≠20→u.scalarReg j=s.scalarReg j
lemma Frame.trans{s t u:State}(a:Frame s t)(b:Frame t u):Frame s u:=
 ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,
  fun j h=>(b.natReg j h).trans (a.natReg j h),fun j h=>(b.scalarReg j h).trans (a.scalarReg j h)⟩
lemma Frame.withPC{s u:State}(h:Frame s u)(pc:ℕ):Frame s {u with pc:=pc}:=by
 cases h;constructor <;> assumption
lemma Frame.beforePC{s u:State}(h:Frame s u)(pc:ℕ):Frame {s with pc:=pc} u:=by
 cases h;constructor <;> assumption
lemma Frame.permutation{s u:State}(h:UniformPermutationMachine.Frame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,fun j hj=>h.2.2.2.2 j (by rcases hj.1 with lo|hi <;> omega),h.2.2.2.1⟩
lemma block_pc (b:List Op)(s:State):(applyBlock b s).pc=s.pc+b.length:=by
 induction b generalizing s with
 | nil=>rfl
 | cons o b ih=>rw[applyBlock,ih,Op.apply_pc,List.length_cons];omega

lemma first_regs (s:State):
 (applyBlock firstSetup s).natReg 70=s.natReg 103∧
 (applyBlock firstSetup s).natReg 71=s.natReg 6026∧
 (applyBlock firstSetup s).natReg 72=s.natReg 6025∧
 (applyBlock firstSetup s).natReg 73=s.natReg 7311∧
 (applyBlock firstSetup s).natReg 7390=0:=by
 simp[firstSetup,applyBlock,Op.apply,writeNat,next,evalNat]
lemma second_regs (s:State)(zero:s.natReg 7390=0):
 (applyBlock secondSetup s).natReg 70=s.natReg 103∧
 (applyBlock secondSetup s).natReg 71=s.natReg 6025∧
 (applyBlock secondSetup s).natReg 72=s.natReg 6026∧
 (applyBlock secondSetup s).natReg 73=s.natReg 7310:=by
 simp[secondSetup,applyBlock,Op.apply,writeNat,next,evalNat,zero]
lemma alpha_regs (s:State):
 (applyBlock alphaSetup s).natReg 70=s.natReg 103∧
 (applyBlock alphaSetup s).natReg 71=s.natReg 7312∧
 (applyBlock alphaSetup s).natReg 72=s.natReg 6026∧
 (applyBlock alphaSetup s).natReg 73=s.natReg 7310:=by
 simp[alphaSetup,applyBlock,Op.apply,writeNat,next,evalNat]
lemma first_frame (s:State):Frame s (applyBlock firstSetup s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   simp[firstSetup,applyBlock,Op.apply,writeNat,next,hj.2,show j≠70 by rcases hj.1 with lo|hi <;> omega,
    show j≠71 by rcases hj.1 with lo|hi <;> omega,show j≠72 by rcases hj.1 with lo|hi <;> omega,
    show j≠73 by rcases hj.1 with lo|hi <;> omega]
 · intro j _;rfl
lemma second_frame (s:State):Frame s (applyBlock secondSetup s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   simp[secondSetup,applyBlock,Op.apply,writeNat,next,show j≠70 by rcases hj.1 with lo|hi <;> omega,
    show j≠71 by rcases hj.1 with lo|hi <;> omega,show j≠72 by rcases hj.1 with lo|hi <;> omega,
    show j≠73 by rcases hj.1 with lo|hi <;> omega]
 · intro j _;rfl
lemma alpha_frame (s:State):Frame s (applyBlock alphaSetup s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   simp[alphaSetup,applyBlock,Op.apply,writeNat,next,hj.2,show j≠70 by rcases hj.1 with lo|hi <;> omega,
    show j≠71 by rcases hj.1 with lo|hi <;> omega,show j≠72 by rcases hj.1 with lo|hi <;> omega,
    show j≠73 by rcases hj.1 with lo|hi <;> omega]
 · intro j _;rfl
lemma first_peak (B:ℕ)(s:State)(bound:WordBound B s):peak firstSetup s≤B:=by
 simp[peak,firstSetup,Op.peak,Op.apply,writeNat,next,evalNat]
 exact ⟨bound.2.1 103,bound.2.1 6026,bound.2.1 6025,bound.2.1 7311⟩
lemma second_peak (B:ℕ)(s:State)(zero:s.natReg 7390=0)(bound:WordBound B s):peak secondSetup s≤B:=by
 simp[peak,secondSetup,Op.peak,Op.apply,writeNat,next,evalNat,zero]
 exact ⟨bound.2.1 103,bound.2.1 6025,bound.2.1 6026,bound.2.1 7310⟩
lemma alpha_peak (B:ℕ)(s:State)(bound:WordBound B s):peak alphaSetup s≤B:=by
 simp[peak,alphaSetup,Op.peak,Op.apply,writeNat,next,evalNat]
 exact ⟨bound.2.1 103,bound.2.1 7312,bound.2.1 6026,bound.2.1 7310⟩

/-- The actual BI gather followed by the actual AP gather, retaining exact flags. -/
theorem execution (n B V S T AP BI:ℕ)(x:Fin n→ℂ)(f:Fin V→Scalar)
 (alpha betaInverse:Fin V≃Fin V)(s:State)(pc:s.pc=0)
 (hV:s.natReg 103=V)(hS:s.natReg 6026=S)(hT:s.natReg 6025=T)
 (hAP:s.natReg 7310=AP)(hBI:s.natReg 7311=BI)
 (source:∀j,s.scalarHeap (S+j.val)=some (f j))
 (alphaTable:UniformGlobalNatPreparation.PermutationBank V AP s.natHeap alpha)
 (betaTable:UniformGlobalNatPreparation.PermutationBank V BI s.natHeap betaInverse)
 (disjoint:UniformPermutationMachine.Disjoint S T V)
 (sourceFit:S+V≤B)(targetFit:T+V≤B)(alphaFit:AP+V≤B)(betaFit:BI+V≤B)
 (code:34≤B)(bound:WordBound B s):∃u,
 BoundedExecution program n x B s (18*V+18) u∧u.pc=33∧
 (∀j:Fin V,u.scalarHeap (S+j.val)=some (f (betaInverse (alpha j))))∧
 (∀j:Fin V,u.scalarHeap (T+j.val)=some (f (betaInverse j)))∧
 (∀a,(a<S∨S+V≤a)→(a<T∨T+V≤a)→u.scalarHeap a=s.scalarHeap a)∧Frame s u:=by
 have first:=block_runs firstSetup program 0 n B x s first_setup_code pc bound
  (by change 0+5≤B;omega) (by simp[readable,firstSetup,Op.readable,evalNat]) (first_peak B s bound)
 let a:=applyBlock firstSetup s
 have pa:a.pc=5:=by rw[block_pc,pc];rfl
 let ae:State:={a with pc:=0}
 obtain ⟨v,gather1,values1,_source1,out1,frame1,_pv,_index1⟩:=UniformPermutationMachine.execution
  n x V S T BI B betaInverse ae (by exact betaTable) (by intro j;exact ⟨f j,source j⟩)
  disjoint sourceFit targetFit betaFit (by omega) rfl
  ((first_regs s).1.trans hV) ((first_regs s).2.1.trans hS)
  ((first_regs s).2.2.1.trans hT) ((first_regs s).2.2.2.1.trans hBI)
  (changePC_bound _ a 0 first.final_bound (by omega))
 have placed1:=boundedExecution_placed first_code (by change 5+12≤B;omega) (by omega:17≤B) gather1
 have place1:placed 5 ae=a:=by change {a with pc:=5}=a;rw[←pa]
 rw[place1] at placed1
 let b:State:={v with pc:=17}
 have fm1:Frame a v:=by
  have h:Frame (placed 5 ae) v:=(Frame.permutation frame1).beforePC 5
  rw[place1] at h;exact h
 have fb:Frame s b:=((first_frame s).trans fm1).withPC 17
 have zero:b.natReg 7390=0:=(frame1.2.2.2.2 _ (Or.inr (by omega))).trans (first_regs s).2.2.2.2
 have original (j:ℕ)(h:Protected j):b.natReg j=s.natReg j:=fb.natReg j h
 have regs:(applyBlock secondSetup b).natReg 70=V∧(applyBlock secondSetup b).natReg 71=T∧
  (applyBlock secondSetup b).natReg 72=S∧(applyBlock secondSetup b).natReg 73=AP:=by
  obtain ⟨l,i,d,t⟩:=second_regs b zero
  exact ⟨l.trans ((original 103 (by unfold Protected;omega)).trans hV),
   i.trans ((original 6025 (by unfold Protected;omega)).trans hT),
   d.trans ((original 6026 (by unfold Protected;omega)).trans hS),
   t.trans ((original 7310 (by unfold Protected;omega)).trans hAP)⟩
 have next:=block_runs secondSetup program 17 n B x b second_setup_code rfl placed1.final_bound
  (by change 17+4≤B;omega) (by simp[readable,secondSetup,Op.readable,evalNat])
  (second_peak B b zero placed1.final_bound)
 let c:=applyBlock secondSetup b
 have pc':c.pc=21:=by rw[block_pc];rfl
 let ce:State:={c with pc:=0}
 have fc:Frame s c:=fb.trans (second_frame b)
 have src2:UniformPermutationMachine.Source V T ce.scalarHeap:=by intro j;exact ⟨f (betaInverse j),(values1 j).trans (source (betaInverse j))⟩
 have table2:UniformGlobalNatPreparation.PermutationBank V AP ce.natHeap alpha:=by rw[fc.natHeap];exact alphaTable
 have disjoint2:UniformPermutationMachine.Disjoint T S V:=by
  unfold UniformPermutationMachine.Disjoint at disjoint ⊢;exact disjoint.symm
 obtain ⟨u,gather2,values2,kept2,out2,frame2,_pu,_index2⟩:=UniformPermutationMachine.execution
  n x V T S AP B alpha ce table2 src2 disjoint2 targetFit sourceFit alphaFit (by omega) rfl
  regs.1 regs.2.1 regs.2.2.1 regs.2.2.2 (changePC_bound _ c 0 next.final_bound (by omega))
 have placed2:=boundedExecution_placed second_code (by change 21+12≤B;omega) (by omega:33≤B) gather2
 have place2:placed 21 ce=c:=by change {c with pc:=21}=c;rw[←pc']
 rw[place2] at placed2
 have fm2:Frame c u:=by
  have h:Frame (placed 21 ce) u:=(Frame.permutation frame2).beforePC 21
  rw[place2] at h;exact h
 let z:State:={u with pc:=33}
 have halt:BoundedExecution program n x B z 1 z:=.halt placed2.final_bound (by simp[step,z,halt_at])
 refine ⟨z,?_,rfl,?_,?_,?_,(fc.trans fm2).withPC 33⟩
 · convert ((first.trans placed1).trans next).executes (placed2.executes halt) using 1
   simp only[firstSetup,secondSetup,List.length_cons,List.length_nil]
   omega
 · intro j
   exact (values2 j).trans ((values1 (alpha j)).trans (source (betaInverse (alpha j))))
 · intro j
   exact (kept2 j).trans ((values1 j).trans (source (betaInverse j)))
 · intro address hs ht
   exact (out2 address hs).trans (out1 address ht)

/-- A single physical AP gather from the caller's original source bank. -/
theorem alpha_execution (n B V K S AP:ℕ)(x:Fin n→ℂ)(f:Fin V→Scalar)
 (alpha:Fin V≃Fin V)(s:State)(pc:s.pc=0)
 (hV:s.natReg 103=V)(hK:s.natReg 7312=K)(hS:s.natReg 6026=S)(hAP:s.natReg 7310=AP)
 (source:∀j,s.scalarHeap (K+j.val)=some (f j))
 (table:UniformGlobalNatPreparation.PermutationBank V AP s.natHeap alpha)
 (disjoint:UniformPermutationMachine.Disjoint K S V)(sourceFit:K+V≤B)(targetFit:S+V≤B)
 (tableFit:AP+V≤B)(code:18≤B)(bound:WordBound B s):∃u,
 BoundedExecution alphaProgram n x B s (9*V+10) u∧u.pc=17∧
 (∀j:Fin V,u.scalarHeap (S+j.val)=some (f (alpha j)))∧
 (∀j:Fin V,u.scalarHeap (K+j.val)=some (f j))∧
 UniformPermutationMachine.Outside S V s.scalarHeap u∧Frame s u:=by
 have boot:=block_runs alphaSetup alphaProgram 0 n B x s alpha_setup_code pc bound
  (by change 0+5≤B;omega) (by simp[readable,alphaSetup,Op.readable,evalNat]) (alpha_peak B s bound)
 let a:=applyBlock alphaSetup s
 have pa:a.pc=5:=by rw[block_pc,pc];rfl
 let ae:State:={a with pc:=0}
 obtain ⟨u,run,values,kept,outside,frame,_pu,_index⟩:=UniformPermutationMachine.execution
  n x V K S AP B alpha ae table (by intro j;exact ⟨f j,source j⟩) disjoint
  sourceFit targetFit tableFit (by omega) rfl
  ((alpha_regs s).1.trans hV) ((alpha_regs s).2.1.trans hK)
  ((alpha_regs s).2.2.1.trans hS) ((alpha_regs s).2.2.2.trans hAP)
  (changePC_bound _ a 0 boot.final_bound (by omega))
 have placedRun:=boundedExecution_placed alpha_code (by change 5+12≤B;omega) (by omega:17≤B) run
 have place:placed 5 ae=a:=by change {a with pc:=5}=a;rw[←pa]
 rw[place] at placedRun
 have fm:Frame a u:=by
  have h:Frame (placed 5 ae) u:=(Frame.permutation frame).beforePC 5
  rw[place] at h;exact h
 let z:State:={u with pc:=17}
 have halt:BoundedExecution alphaProgram n x B z 1 z:=.halt placedRun.final_bound (by simp[step,z,alpha_halt_at])
 refine ⟨z,?_,rfl,fun j=>(values j).trans (source (alpha j)),fun j=>(kept j).trans (source j),outside,
  ((alpha_frame s).trans fm).withPC 17⟩
 convert boot.executes (placedRun.executes halt) using 1
 simp only[alphaSetup,List.length_cons,List.length_nil]
 omega
end
end ExactFourierCircuits.UniformPhysicalCRTConsumerMachine
