import UniformTensorMonomialMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalScalePoolMachine
open UniformMachine UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section

/-- Internally prepare every cell of all nine diagonal banks, including
unmatched coordinates. Nat4330 is pool,4331 is radix. -/
def boot : List Op := [.literal 4356 0,.literal 4357 1,.literal 4358 9,
 .mul 4358 4331 4358,.literalScalar 125 1]
def body : List Op := [.add 4359 4330 4356,.putScalar 4359 125,.add 4356 4356 4357]
def program : Program := boot.map Op.code++[.branchLT 4356 4358 6 10]++
 body.map Op.code++[.jump 5,.halt]
lemma program_length : program.length=11 := rfl
lemma boot_code : BlockAt boot program 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma body_code : BlockAt body program 6 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma branch_at : program[5]?=some (.branchLT 4356 4358 6 10) := rfl
lemma jump_at : program[9]?=some (.jump 5) := rfl
lemma halt_at : program[10]?=some .halt := rfl

structure Cursor (pool count i : ℕ) (s : State) : Prop where
 pc:s.pc=5
 pool:s.natReg 4330=pool
 count:s.natReg 4358=count
 index:s.natReg 4356=i
 one:s.natReg 4357=1
 value:s.scalarReg 125=prepared 1

def Prefix (pool i : ℕ) (s : State) : Prop :=
 ∀j,j < i → s.scalarHeap (pool+j)=some (prepared 1)
def nextState (s : State) : State := {applyBlock body {s with pc:=6} with pc:=5}
lemma body_heap (pool i : ℕ) (s : State) (hp:s.natReg 4330=pool) (hi:s.natReg 4356=i)
 (hv:s.scalarReg 125=prepared 1) :
 (nextState s).scalarHeap=Function.update s.scalarHeap (pool+i) (some (prepared 1)) := by
 simp [nextState,body,applyBlock,Op.apply,writeNat,next,hp,hi,hv]
lemma body_cursor (pool count i : ℕ) (s : State) (h:Cursor pool count i s) :
 Cursor pool count (i+1) (nextState s) := by
 constructor <;> simp [nextState,body,applyBlock,Op.apply,writeNat,next,
  h.pool,h.count,h.index,h.one,h.value]
lemma body_prefix (pool count i : ℕ) (s : State) (h:Cursor pool count i s)
 (pre:Prefix pool i s) : Prefix pool (i+1) (nextState s) := by
 intro j hj
 rw [body_heap pool i s h.pool h.index h.value]
 by_cases eq:j=i
 · subst j;simp
 · rw [Function.update_of_ne (by omega)];exact pre j (by omega)
lemma body_safe (pool count i B : ℕ) (s : State) (h:Cursor pool count i s)
 (hi:i<count) (bound:pool+count≤B) : readable body s ∧ peak body s≤B := by
 constructor
 · simp [body,readable,Op.readable]
 · simp [body,peak,Op.peak,Op.apply,writeNat,next,h.pool,h.index,h.one];omega
lemma body_frame (pool count i : ℕ) (s : State) (h:Cursor pool count i s) (q : ℕ)
 (hq:q<pool ∨ pool+count≤q) (hi:i<count) :
 (nextState s).scalarHeap q=s.scalarHeap q := by
 rw [body_heap pool i s h.pool h.index h.value]
 exact Function.update_of_ne (by omega) _ _
structure Frame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 scalarReg:∀q,q≠125 → u.scalarReg q=s.scalarReg q
 natReg:∀q,q≠4356 → q≠4357 → q≠4358 → q≠4359 → u.natReg q=s.natReg q
lemma Frame.trans {s t u : State} (h:Frame s t) (g:Frame t u) : Frame s u :=
 ⟨g.natHeap.trans h.natHeap,g.outputs.trans h.outputs,g.roots.trans h.roots,
 fun q hn=>(g.scalarReg q hn).trans (h.scalarReg q hn),
 fun q h6 h7 h8 h9=>(g.natReg q h6 h7 h8 h9).trans (h.natReg q h6 h7 h8 h9)⟩
lemma body_frames (s : State) : Frame s (nextState s) := by
 constructor
 · rfl
 · rfl
 · rfl
 · intro q hq;rfl
 · intro q h6 h7 h8 h9
   simp [nextState,body,applyBlock,Op.apply,writeNat,next,h6,h9]
lemma boot_frames (s : State) : Frame s (applyBlock boot s) := by
 constructor
 · rfl
 · rfl
 · rfl
 · intro q hq;simp [boot,applyBlock,Op.apply,writeNat,writeScalar,next,hq]
 · intro q h6 h7 h8 h9
   simp [boot,applyBlock,Op.apply,writeNat,writeScalar,next,h6,h7,h8]
lemma body_bounded (pool count i n B : ℕ) (x : Fin n → ℂ) (s : State)
 (h:Cursor pool count i s) (hi:i<count) (bound:pool+count≤B) (code:11≤B)
 (hs:WordBound B s) : BoundedRuns program n x B s 5 (nextState s) := by
 let entry:State:={s with pc:=6}
 have hb:WordBound B entry:=changePC_bound B s 6 hs (by omega)
 have branch:step program n x s=.running entry:=by
  simp [step,h.pc,branch_at,h.index,h.count,hi,entry]
 have safe:=body_safe pool count i B s h hi bound
 have run:=block_runs body program 6 n B x entry body_code rfl hb
  (by change 6+3≤B;omega) safe.1 safe.2
 have last:(applyBlock body entry).pc=9:=by rw [applyBlock_pc];rfl
 have outb:WordBound B (nextState s):=changePC_bound B _ 5 run.final_bound (by omega)
 have jump:step program n x (applyBlock body entry)=.running (nextState s):=by
  simp only [step,last,jump_at];rfl
 have first:BoundedRuns program n x B s 4 (applyBlock body entry):=.next hs branch run
 exact first.trans (.next run.final_bound jump (.refl outb))

lemma loop (remaining pool count i n B : ℕ) (x : Fin n → ℂ) (s : State)
 (h:Cursor pool count i s) (pre:Prefix pool i s) (sum:i+remaining=count)
 (bound:pool+count≤B) (code:11≤B) (hs:WordBound B s) : ∃out,
 BoundedExecution program n x B s (5*remaining+2) out ∧ out.pc=10 ∧
 Prefix pool count out ∧
 (∀q,(q<pool ∨ pool+count≤q) → out.scalarHeap q=s.scalarHeap q) ∧ Frame s out := by
 induction remaining generalizing i s with
 | zero =>
  have eq:i=count:=by omega
  let out:State:={s with pc:=10}
  have hb:WordBound B out:=changePC_bound B s 10 hs (by omega)
  have branch:step program n x s=.running out:=by
   simp [step,h.pc,branch_at,h.index,h.count,eq,out]
  have halt:step program n x out=.halted out:=by simp only [step,out,halt_at]
  exact ⟨out,.next hs branch (.halt hb halt),rfl,by simpa only [Prefix,out,eq] using pre,fun _ _=>rfl,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _ _=>rfl⟩⟩
 | succ remaining ih =>
  have hi:i<count:=by omega
  have run:=body_bounded pool count i n B x s h hi bound code hs
  obtain ⟨out,tail,last,done,frame,fields⟩:=ih (i+1) (nextState s)
   (body_cursor pool count i s h) (body_prefix pool count i s h pre)
   (by omega) run.final_bound
  refine ⟨out,?_,last,done,?_,(body_frames s).trans fields⟩
  · convert run.executes tail using 1;omega
  · intro q hq;exact (frame q hq).trans (body_frame pool count i s h q hq hi)

/-- All9*r physical factor cells are prepared1 from the original dirty heap.
There is no supplied initialized pool. -/
theorem execution (pool r n B : ℕ) (x : Fin n → ℂ) (s : State)
 (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (bound:pool+9*r≤B) (code:11≤B) (pc:s.pc=0) (hs:WordBound B s) : ∃out,
 BoundedExecution program n x B s (45*r+7) out ∧ out.pc=10 ∧
 Prefix pool (9*r) out ∧
 (∀q,(q<pool ∨ pool+9*r≤q) → out.scalarHeap q=s.scalarHeap q) ∧ Frame s out := by
 let z:=applyBlock boot s
 have reads:readable boot s:=by simp [boot,readable,Op.readable]
 have peaks:peak boot s≤B:=by
  simp [boot,peak,Op.peak,Op.apply,writeNat,next,hr,Nat.mul_comm r 9];omega
 have run:=block_runs boot program 0 n B x s boot_code pc hs
  (by change 0+5≤B;omega) reads peaks
 have cursor:Cursor pool (9*r) 0 z:=by
  constructor <;> simp [z,boot,applyBlock,Op.apply,writeNat,writeScalar,next,pc,hp,hr,Nat.mul_comm r 9,prepared]
 obtain ⟨out,tail,last,table,frame,fields⟩:=loop (9*r) pool (9*r) 0 n B x z cursor
  (by intro j hj;omega) (by omega) bound code run.final_bound
 refine ⟨out,?_,last,table,frame,(boot_frames s).trans fields⟩
 convert run.executes tail using 1
 change 45*r+7=5+(5*(9*r)+2);omega
end
end ExactFourierCircuits.UniformGlobalScalePoolMachine
