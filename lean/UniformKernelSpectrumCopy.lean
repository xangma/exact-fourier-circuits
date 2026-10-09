import UniformScalarCopyDisjoint
import UniformNatBlockMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelSpectrumCopy
open UniformMachine UniformAssembly UniformNatBlockMachine
noncomputable section

/-- Save role1 of the prepared-only transform before loading data. Both
scalar values and the real dependency tags are copied by actual10. -/
def setup:List Op:=[.literal 7390 0,.binary .add 147 103 7390,
 .binary .add 148 6026 103,.binary .add 149 7300 7390]
def program:Program:=setup.map Op.code++UniformScalarCopyMachine.program.map (relocate 4 14)++[.halt]
lemma setup_length:setup.length=4:=rfl
lemma program_length:program.length=15:=rfl
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma copy_code:CodeAt UniformScalarCopyMachine.program program 4 14:=by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma halt_at:program[14]?=some .halt:=rfl
def Changed(q:ℕ):Prop:=q=147∨q=148∨q=149∨q=7390∨(150≤q∧q≤153)
structure Frame(Q L:ℕ)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalar:∀q,q<Q∨Q+L≤q→u.scalarHeap q=s.scalarHeap q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,¬Changed q→u.natReg q=s.natReg q

lemma values{L S Q:ℕ}(s:State)(width:s.natReg 103=L)(base:s.natReg 6026=S)(storage:s.natReg 7300=Q):
 (applyBlock setup s).natReg 147=L∧(applyBlock setup s).natReg 148=S+L∧
 (applyBlock setup s).natReg 149=Q:=by
 simp [setup,applyBlock,Op.apply,writeNat,next,evalNat,width,base,storage]
lemma safe{L S Q B:ℕ}(s:State)(width:s.natReg 103=L)(base:s.natReg 6026=S)
 (storage:s.natReg 7300=Q)(sourceFit:S+L≤B)(storageFit:Q≤B):
 readable setup s∧peak setup s≤B:=by
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,evalNat,width,base,storage]
 omega
lemma setup_kept(s:State)(q:ℕ)(keep:¬Changed q):(applyBlock setup s).natReg q=s.natReg q:=by
 unfold Changed at keep
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]

theorem execution{n L S Q B:ℕ}(x:Fin n→ℂ)(v:Fin L→Scalar)(s:State)
 (input:∀j:Fin L,s.scalarHeap (S+L+j.val)=some (v j))
 (width:s.natReg 103=L)(base:s.natReg 6026=S)(storage:s.natReg 7300=Q)
 (separate:Q+L≤S+L)(sourceFit:S+L+L≤B)(storageFit:Q+L≤B)
 (code:15≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution program n x B s (7*L+9) u∧
 (∀j:Fin L,u.scalarHeap (Q+j.val)=some (v j))∧Frame Q L s u∧u.pc=14:=by
 have proof:=safe (B:=B) s width base storage (by omega) (by omega)
 have start:=block_runs setup program 0 n B x s setup_code pc wb
  (by rw[setup_length];omega) proof.1 proof.2
 let a:=applyBlock setup s
 have ap:a.pc=4:=by simp [a,setup,applyBlock,Op.apply,writeNat,next,pc]
 let e:State:={a with pc:=0}
 have source:UniformScalarCopyMachine.Source L (S+L) e.scalarHeap:=by
  intro j hj
  exact ⟨v ⟨j,hj⟩,input ⟨j,hj⟩⟩
 have args:=values s width base storage
 obtain ⟨u,run,copied,_,outside,frame,natFrame⟩:=UniformScalarCopyMachine.execution_disjoint
  n x L (S+L) Q B e source sourceFit (Or.inr separate) storageFit (by omega)
  rfl args.1 args.2.1 args.2.2 (changePC_bound _ a 0 start.final_bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed copy_code
  (by rw[UniformScalarCopyMachine.program_length];omega) (by omega) run
 have entry:placed 4 e=a:=by change {a with pc:=4}=a;rw[←ap]
 rw[entry] at placedRun
 let final:State:={u with pc:=14}
 have finish:BoundedExecution program n x B final 1 final:=
  .halt placedRun.final_bound (by simp [step,final,halt_at])
 refine ⟨final,?_,?_,?_,rfl⟩
 · convert start.executes (placedRun.executes finish) using 1
   simp only[setup_length]
   omega
 · intro j;exact (copied j.val j.isLt).trans (input j)
 · refine ⟨frame.1,outside,frame.2.1,frame.2.2.1,?_⟩
   intro q hq
   exact (natFrame q (by unfold Changed at hq;omega)).trans (setup_kept s q hq)
end
end ExactFourierCircuits.UniformKernelSpectrumCopy
