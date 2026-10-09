import UniformChirpPointwiseMachine
import UniformNatBlockMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRolePointwiseMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
namespace P
export UniformChirpPointwiseMachine (productScalar)
end P
noncomputable section

/-- Multiply the actual data role by the prepared kernel role. Saved103 is
the working volume and charged allocation6026 is the common source bank. -/
def setup:List Op:=[.literal 7200 0,.binary .add 17 103 7200,
 .binary .add 26 6026 7200,.binary .add 28 7300 7200]
def program:Program:=setup.map Op.code++
 UniformChirpPointwiseMachine.program.map (relocate 4 16)++[.halt]
lemma setup_length:setup.length=4:=rfl
lemma program_length:program.length=17:=rfl
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma pointwise_code:CodeAt UniformChirpPointwiseMachine.program program 4 16:=by
 intro i hi;change i<12 at hi;interval_cases i <;>rfl
lemma halt_at:program[16]?=some .halt:=rfl

def Source(W L S:ℕ)(v:ℕ→Fin L→Scalar)(s:State):Prop:=
 ∀r,r<W→∀j,s.scalarHeap (S+r*L+j.val)=some (v r j)
def multiplied{L:ℕ}(v:ℕ→Fin L→Scalar)(y:Fin L→ℂ)(r:ℕ)(j:Fin L):Scalar:=
 if r=0 then P.productScalar (v 0 j) (y j) else v r j
def Changed(q:ℕ):Prop:=q=17∨q=26∨q=28∨q=7200∨(61≤q∧q≤64)
structure Frame(S L:ℕ)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalar:∀q,q<S∨S+L≤q→u.scalarHeap q=s.scalarHeap q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,¬Changed q→u.natReg q=s.natReg q

lemma setup_values{L S Q:ℕ}(s:State)(width:s.natReg 103=L)(base:s.natReg 6026=S)
 (kernel:s.natReg 7300=Q):
 (applyBlock setup s).natReg 17=L∧(applyBlock setup s).natReg 26=S∧
 (applyBlock setup s).natReg 28=Q:=by
 simp [setup,applyBlock,Op.apply,writeNat,next,evalNat,width,base,kernel]
lemma setup_safe{L S Q B:ℕ}(s:State)(width:s.natReg 103=L)(base:s.natReg 6026=S)
 (kernel:s.natReg 7300=Q)(extent:S+L≤B)(kernelFit:Q≤B):readable setup s∧peak setup s≤B:=by
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,evalNat,width,base,kernel]
 omega
lemma setup_frame(S L:ℕ)(s:State):Frame S L s (applyBlock setup s):=by
 refine ⟨rfl,fun _ _=>rfl,rfl,rfl,?_⟩
 intro q h;unfold Changed at h
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]

/-- The input-independent kernel tags are required explicitly. The real
partial multiplication instruction, including its guard, is executed below. -/
theorem execution{n W L S Q B:ℕ}(x:Fin n→ℂ)(v:ℕ→Fin L→Scalar)(y:Fin L→ℂ)(s:State)
 (roles:0<W)(input:Source W L S v s)
 (prepared:∀j:Fin L,s.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j)))
 (width:s.natReg 103=L)(base:s.natReg 6026=S)(kernelBase:s.natReg 7300=Q)
 (separate:S+L≤Q∨Q+L≤S)(kernelFit:Q+L≤B)
 (extent:S+W*L≤B)(code:64≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution program n x B s (9*L+9) u∧
 Source W L S (multiplied v y) u∧Frame S L s u∧u.pc=16:=by
 have one:L≤W*L:=by simpa only[Nat.one_mul] using Nat.mul_le_mul_right L (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt roles))
 have bounds:S+L≤B:=by omega
 have safe:=setup_safe s width base kernelBase bounds (by omega)
 have start:=block_runs setup program 0 n B x s setup_code pc wb
  (by rw[setup_length];omega) safe.1 safe.2
 let a:=applyBlock setup s
 have ap:a.pc=4:=by
  simp [a,setup,applyBlock,Op.apply,writeNat,next,pc]
 let e:State:={a with pc:=0}
 let data:ℕ→Scalar:=fun j=>if h:j<L then v 0 ⟨j,h⟩ else Scalar.zero
 let kernel:ℕ→ℂ:=fun j=>if h:j<L then y ⟨j,h⟩ else 0
 have bank:UniformChirpPointwiseMachine.Bank S L 0 data kernel e:=by
  intro j hj
  change s.scalarHeap (S+j)=some (UniformChirpPointwiseMachine.adjusted 0 data kernel j)
  simpa [UniformChirpPointwiseMachine.adjusted,data,hj] using input 0 roles ⟨j,hj⟩
 have kernels:UniformChirpPointwiseMachine.Kernels Q L kernel e:=by
  intro j hj
  change s.scalarHeap (Q+j)=some (UniformPairMachine.prepared (kernel j))
  simpa [kernel,hj] using prepared ⟨j,hj⟩
 have args:=setup_values s width base kernelBase
 obtain ⟨u,run,values,_,frame,upc⟩:=UniformChirpPointwiseMachine.pointwise_execution
  x S Q L B data kernel e rfl args.1 args.2.1 args.2.2 bank kernels
  separate code bounds kernelFit
  (changePC_bound _ a 0 start.final_bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed pointwise_code
  (by rw[UniformChirpPointwiseMachine.program_length];omega) (by omega) run
 have entry:placed 4 e=a:=by change {a with pc:=4}=a;rw[←ap]
 rw[entry] at placedRun
 let final:State:={u with pc:=16}
 have finish:BoundedExecution program n x B final 1 final:=
  .halt placedRun.final_bound (by simp [step,final,halt_at])
 have sf:=setup_frame S L s
 refine ⟨final,?_,?_,?_,rfl⟩
 · convert start.executes (placedRun.executes finish) using 1
   simp only [setup_length]
   omega
 · intro r hr j
   by_cases zero:r=0
   · subst r
     simpa [final,multiplied,data,kernel,j.isLt] using values j.val j.isLt
   · have lower:L≤r*L:=by simpa only[Nat.one_mul] using Nat.mul_le_mul_right L (show 1≤r by omega)
     change u.scalarHeap (S+r*L+j.val)=some (multiplied v y r j)
     rw [frame.2.2.2.1 _ (Or.inr (by omega))]
     change s.scalarHeap (S+r*L+j.val)=some (multiplied v y r j)
     simpa [multiplied,zero] using input r hr j
 · refine ⟨frame.1,?_,frame.2.1,frame.2.2.1,?_⟩
   · intro q hq;exact frame.2.2.2.1 q hq
   · intro q hq
     exact (frame.2.2.2.2.1 q (by unfold Changed at hq;omega)).trans (sf.natReg q hq)
end
end ExactFourierCircuits.UniformRolePointwiseMachine
