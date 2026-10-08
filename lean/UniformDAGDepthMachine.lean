import UniformDAGLayers
import UniformToeplitzCrossTopologyMachine
import UniformTensorMonomialMachine
import UniformRadixInstructionMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDAGDepthMachine
open UniformMachine UniformTensorMonomialMachine

/-- Nat650=input count,651=gate count,652=actual five-field tape,
653=fresh depth bank. Scratch654..665. Every tape/depth access is charged. -/
def program : Program := [
 .natLiteral 654 0,.natLiteral 655 1,.natLiteral 656 5,.natLiteral 657 2,
 .natBinary .add 658 650 655,.natLiteral 659 0,.branchLT 659 658 7 11,
 .natBinary .add 660 653 659,.storeNat 660 654,.natBinary .add 659 659 655,.jump 6,
 .natLiteral 659 0,.branchLT 659 651 13 34,
 .natBinary .mul 660 659 656,.natBinary .add 660 652 660,.loadNat 661 660,
 .natBinary .add 660 660 655,.loadNat 662 660,.natBinary .add 660 660 655,.loadNat 663 660,
 .natBinary .add 660 653 662,.loadNat 664 660,.branchLT 661 657 23 28,
 .natBinary .add 660 653 663,.loadNat 665 660,.branchLT 664 665 26 28,
 .natBinary .add 664 665 654,.jump 28,.natBinary .add 664 664 655,
 .natBinary .add 660 653 658,.natBinary .add 660 660 659,.storeNat 660 664,
 .natBinary .add 659 659 655,.jump 12,.halt]
theorem program_length : program.length=35 := rfl

/-- Coefficient payloads do not contribute data edges. -/
inductive Row where
 | add (left right : ℕ)
 | sub (left right : ℕ)
 | scale (left : ℕ)
 deriving DecidableEq
def Row.opcode : Row→ℕ | .add _ _=>0 | .sub _ _=>1 | .scale _=>2
def Row.left : Row→ℕ | .add a _ | .sub a _ | .scale a=>a
def Row.right : Row→ℕ | .add _ b | .sub _ b=>b | .scale _=>0
def Row.refs : Row→List ℕ | .add a b | .sub a b=>[a,b] | .scale a=>[a]
def erase {r : ℕ} : UniformConvolutionDAG.Expr r ℕ→Row
 | .add a b=>.add a b | .sub a b=>.sub a b | .scale _ a=>.scale a
def rows {r n t : ℕ} (p:UniformReplayPrint.Program r n t) : List Row :=
 (UniformToeplitzCrossDAG.programRecords p).map erase
theorem rows_length {r n t : ℕ} (p:UniformReplayPrint.Program r n t) : (rows p).length=t := by
 simp [rows,UniformToeplitzCrossDAG.programRecords_length]

def Row.depth (row:Row) (d:ℕ→ℕ) : ℕ := match row with
 | .add a b | .sub a b=>max (d a) (d b)+1 | .scale a=>d a+1
def evaluate (start:ℕ) : List Row→(ℕ→ℕ)→(ℕ→ℕ)
 | [],d=>d
 | row::rest,d=>evaluate (start+1) rest (Function.update d start (row.depth d))
theorem evaluate_append (start:ℕ) (a b:List Row) (d:ℕ→ℕ) :
 evaluate start (a++b) d=evaluate (start+a.length) b (evaluate start a d) := by
 induction a generalizing start d with
 | nil=>rfl
 | cons row rest ih=>simp only [List.cons_append,evaluate,ih,List.length_cons];congr 1;omega

theorem erase_gate_depth {r w : ℕ} (g:UniformReplayPrint.Gate r w) (d:ℕ→ℕ) :
 (erase (UniformToeplitzCrossDAG.gateRecord g)).depth d=
 UniformToeplitzCrossDAG.gateDepth (fun i=>d i.val) g := by cases g <;> rfl

/-- The integer recurrence computes the actual constructor-longest-path
labels of the typed program, including its literal-zero port. -/
theorem evaluate_typed {r n t : ℕ} (p : UniformReplayPrint.Program r n t) :
    ∀ a : Fin (n+1+t), evaluate (n+1) (rows p) (fun _ => 0) a.val =
      UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a := by
  induction p with
  | nil =>
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a <;>
      simp [rows,UniformToeplitzCrossDAG.programRecords,evaluate,UniformToeplitzCrossDAG.runDepth]
  | @step t p g ih =>
    intro a
    have he : (fun i : Fin (n+1+t) => evaluate (n+1) (rows p) (fun _ => 0) i.val) =
        UniformToeplitzCrossDAG.runDepth p (fun _ => 0) := funext ih
    have hr : rows (p.step g) = rows p ++ [erase (UniformToeplitzCrossDAG.gateRecord g)] := by
      simp [rows,UniformToeplitzCrossDAG.programRecords]
    rw [hr,evaluate_append,rows_length]
    change Function.update (evaluate (n+1) (rows p) (fun _ => 0)) (n+1+t)
      ((erase (UniformToeplitzCrossDAG.gateRecord g)).depth
        (evaluate (n+1) (rows p) (fun _ => 0))) a.val =
      (Fin.snoc (UniformToeplitzCrossDAG.runDepth p (fun _ => 0))
        (UniformToeplitzCrossDAG.gateDepth
          (UniformToeplitzCrossDAG.runDepth p (fun _ => 0)) g) : Fin (n+1+t+1) → ℕ) a
    refine Fin.lastCases (n:=n+1+t) ?_ (fun i => ?_) a
    · simp only [Fin.val_last,Fin.snoc_last]
      simp [Function.update]
      rw [erase_gate_depth,he]
    · rw [Fin.snoc_castSucc]
      have hi : i.val ≠ n+1+t := by have := i.isLt;omega
      simp [Function.update,hi]
      exact ih i

theorem erase_gate_refs {r w : ℕ} (g : UniformReplayPrint.Gate r w) :
    ∀ a ∈ (erase (UniformToeplitzCrossDAG.gateRecord g)).refs, a < w := by
  cases g with
  | add a b => simp [erase,UniformToeplitzCrossDAG.gateRecord,Row.refs,a.isLt,b.isLt]
  | sub a b => simp [erase,UniformToeplitzCrossDAG.gateRecord,Row.refs,a.isLt,b.isLt]
  | scale c a => simp [erase,UniformToeplitzCrossDAG.gateRecord,Row.refs,a.isLt]

noncomputable section
structure Header (N G d P : ℕ) (s:State) : Prop where
 inputs:s.natReg 650=N
 gates:s.natReg 651=G
 tape:s.natReg 652=d
 bank:s.natReg 653=P
def Tape (d:ℕ) (rs:List Row) (s:State) : Prop :=
 ∀j:Fin rs.length,s.natHeap (d+5*j.val)=some (rs[j].opcode) ∧
 s.natHeap (d+5*j.val+1)=some (rs[j].left) ∧
 s.natHeap (d+5*j.val+2)=some (rs[j].right)
def Topological (N:ℕ) (rs:List Row) : Prop :=
 ∀j:Fin rs.length,∀a∈rs[j].refs,a<N+1+j.val
def DepthBank (P size:ℕ) (d:ℕ→ℕ) (s:State) : Prop :=
 ∀i,i<size→s.natHeap (P+i)=some (d i)
def Frame (s u:State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 ∀r,(r<654 ∨ 666 ≤ r)→u.natReg r=s.natReg r
theorem frame_refl (s:State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v:State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
 h'.2.2.2.1.trans h.2.2.2.1,fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
def Outside (P size:ℕ) (s u:State) : Prop :=
 ∀ i, (i < P ∨ P + size ≤ i) → u.natHeap i = s.natHeap i
def runtimeBudget (N G:ℕ) : ℕ := 5*(N+1)+22*G+10

def boot : List Op := [.literal 654 0,.literal 655 1,.literal 656 5,
 .literal 657 2,.add 658 650 655,.literal 659 0]
def zeroBody : List Op := [.add 660 653 659,.putNat 660 654,.add 659 659 655]
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem zeroBody_code : BlockAt zeroBody program 7 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem zero_branch : program[6]?=some (.branchLT 659 658 7 11) := rfl
theorem zero_jump : program[10]?=some (.jump 6) := rfl

structure Fixed (N G d P : ℕ) (s : State) : Prop where
 header : Header N G d P s
 zero : s.natReg 654=0
 one : s.natReg 655=1
 five : s.natReg 656=5
 two : s.natReg 657=2
 span : s.natReg 658=N+1
structure ZeroCursor (N G d P i : ℕ) (s : State) : Prop where
 fixed : Fixed N G d P s
 pc : s.pc=6
 index : s.natReg 659=i
theorem Fixed.withPC {N G d P pc : ℕ} {s : State} (h : Fixed N G d P s) :
 Fixed N G d P (setPC s pc) := by
 refine ⟨?_,h.zero,h.one,h.five,h.two,h.span⟩
 rcases h.header with ⟨a,b,c,d⟩
 exact ⟨a,b,c,d⟩
theorem Frame.withPC {s u : State} {pc : ℕ} (h : Frame s u) : Frame s (setPC u pc) := h
def zeroIteration (s : State) : State := setPC (applyBlock zeroBody (setPC s 7)) 6

theorem zeroIteration_heap {N G d P i : ℕ} {s : State} (h : ZeroCursor N G d P i s) :
 (zeroIteration s).natHeap=Function.update s.natHeap (P+i) (some 0) := by
 simp [zeroIteration,zeroBody,applyBlock,Op.apply,setPC,writeNat,next,
  h.fixed.header.bank,h.index,h.fixed.zero]
theorem zeroIteration_cursor {N G d P i : ℕ} {s : State} (h : ZeroCursor N G d P i s) :
 ZeroCursor N G d P (i+1) (zeroIteration s) := by
 refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩,rfl,?_⟩
 all_goals simp [zeroIteration,zeroBody,applyBlock,Op.apply,setPC,writeNat,next,
  h.fixed.header.inputs,h.fixed.header.gates,h.fixed.header.tape,h.fixed.header.bank,
  h.fixed.zero,h.fixed.one,h.fixed.five,h.fixed.two,h.fixed.span,h.index]
theorem zeroIteration_frame (s : State) : Frame s (zeroIteration s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r hr
 simp (disch:=omega) [zeroIteration,zeroBody,applyBlock,Op.apply,setPC,writeNat,next]

theorem zeroIteration_bounded {N G d P i : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
 (h : ZeroCursor N G d P i s) (hi : i<N+1) (hc : 35 ≤ B) (ha : P+N+1 ≤ B)
 (hs : WordBound B s) : BoundedRuns program n x B s 5 (zeroIteration s) := by
 have enter:=UniformRadixInstructionMachine.branch_runs program n B 659 658 7 11 x s hs
   (by omega) (by omega) (by rw [h.pc];exact zero_branch)
 have lt:s.natReg 659<s.natReg 658:=by rw [h.index,h.fixed.span];exact hi
 simp only [lt,ite_true] at enter
 let v:=setPC s 7
 have vb:WordBound B v:=by simpa [v,setPC] using enter.final_bound
 have readable:readable zeroBody v:=by simp [readable,zeroBody,Op.readable]
 have peak:peak zeroBody v ≤ B:=by
   simp [peak,zeroBody,Op.peak,Op.apply,writeNat,next,v,setPC,
     h.fixed.header.bank,h.index,h.fixed.zero,h.fixed.one]
   omega
 have run:=block_runs zeroBody program 7 n B x v zeroBody_code rfl vb
   (by change 7+3 ≤ B;omega) readable peak
 have pc:(applyBlock zeroBody v).pc=10:=by rw [applyBlock_pc];rfl
 have jump:=UniformRadixInstructionMachine.jump_runs program n B 6 x (applyBlock zeroBody v)
   run.final_bound (by omega) (by rw [pc];exact zero_jump)
 simpa [zeroIteration,show zeroBody.length=3 from rfl,v,setPC] using enter.trans (run.trans jump)

theorem zero_loop {N G d P i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ) (s : State)
 (h : ZeroCursor N G d P i s) (hi : i+remaining=N+1)
 (hc : 35 ≤ B) (ha : P+N+1 ≤ B) (hs : WordBound B s) : ∃u,
 BoundedRuns program n x B s (5*remaining+1) u ∧ Fixed N G d P u ∧
 u.pc=11 ∧ (∀j,i ≤ j→j<N+1→u.natHeap (P+j)=some 0) ∧
 Outside (P+i) remaining s u ∧ Frame s u := by
 induction remaining generalizing i s with
 | zero =>
   have he:i=N+1:=by omega
   have run:=UniformRadixInstructionMachine.branch_runs program n B 659 658 7 11 x s hs
     (by omega) (by omega) (by rw [h.pc];exact zero_branch)
   have stop:¬s.natReg 659<s.natReg 658:=by rw [h.index,h.fixed.span,he];omega
   simp only [stop,ite_false] at run
   refine ⟨setPC s 11,by simpa [setPC] using run,h.fixed.withPC,rfl,?_,?_,(frame_refl s).withPC⟩
   · intro j hj ht;omega
   · intro j hj;rfl
 | succ remaining ih =>
   have lt:i<N+1:=by omega
   have run:=zeroIteration_bounded B n x s h lt hc ha hs
   obtain ⟨u,hu,fixed,pc,zeros,outside,frame⟩:=ih (i:=i+1) (zeroIteration s)
     (zeroIteration_cursor h) (by omega) run.final_bound
   refine ⟨u,?_,fixed,pc,?_,?_,(zeroIteration_frame s).trans frame⟩
   · convert run.trans hu using 1;omega
   · intro j hj ht
     by_cases eq:j=i
     · subst j
       rw [outside (P+i) (Or.inl (by omega)),zeroIteration_heap h]
       simp [Function.update]
     · exact zeros j (by omega) ht
   · intro j hj
     rw [outside j (by unfold Outside at outside;omega),zeroIteration_heap h]
     rw [Function.update_of_ne (by omega)]

theorem boot_fixed {N G d P : ℕ} {s : State} (h : Header N G d P s) :
 Fixed N G d P (applyBlock boot s) := by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,
   h.inputs,h.gates,h.tape,h.bank]
theorem boot_frame (s : State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r hr;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]

/-- All input and zero-port labels are physically generated. -/
theorem initialize_depth (N G d P B n : ℕ) (x : Fin n→ℂ) (s : State)
 (h : Header N G d P s) (pc : s.pc=0) (hc : 35 ≤ B) (ha : P+N+1 ≤ B)
 (hs : WordBound B s) : ∃u,
 BoundedRuns program n x B s (5*(N+1)+8) u ∧ Fixed N G d P u ∧
 u.pc=12 ∧ u.natReg 659=0 ∧ DepthBank P (N+1) (fun _=>0) u ∧
 Outside P (N+1) s u ∧ Frame s u := by
 have hr:readable boot s:=by simp [readable,boot,Op.readable]
 have hp:peak boot s ≤ B:=by
   simp [peak,boot,Op.peak,Op.apply,writeNat,next,h.inputs]
   omega
 have start:=block_runs boot program 0 n B x s boot_code pc hs (by change 0+6 ≤ B;omega) hr hp
 have cur:ZeroCursor N G d P 0 (applyBlock boot s):=by
   refine ⟨boot_fixed h,?_,?_⟩
   · rw [applyBlock_pc,pc];rfl
   · simp [boot,applyBlock,Op.apply,writeNat,next]
 obtain ⟨v,run,fixed,vpc,zeros,outside,frame⟩:=zero_loop (N+1) B n x (applyBlock boot s)
   cur (by omega) hc ha start.final_bound
 let u:=writeNat v 659 0
 have ub:WordBound B u:=writeNat_bound B v 659 0 run.final_bound (by omega) (by omega)
 have last:BoundedRuns program n x B v 1 u:=.next run.final_bound
   (by rw [step,vpc];rfl) (.refl ub)
 refine ⟨u,?_,?_,?_,?_,?_,?_,?_⟩
 · convert start.trans (run.trans last) using 1
   simp only [show boot.length=6 from rfl];omega
 · refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
   all_goals simp [u,writeNat,next,fixed.header.inputs,fixed.header.gates,
     fixed.header.tape,fixed.header.bank,fixed.zero,fixed.one,fixed.five,fixed.two,fixed.span]
 · simp [u,writeNat,next,vpc]
 · simp [u,writeNat]
 · intro i hi;exact zeros i (by omega) hi
 · intro i hi
   exact (outside i (by simpa only [Nat.add_zero] using hi)).trans rfl
 · apply (boot_frame s).trans (frame.trans ?_)
   refine ⟨rfl,rfl,rfl,rfl,?_⟩
   intro r hr;simp [u,writeNat,next,show r≠659 by omega]

def readBlock : List Op := [.mul 660 659 656,.add 660 652 660,.getNat 661 660,
 .add 660 660 655,.getNat 662 660,.add 660 660 655,.getNat 663 660,
 .add 660 653 662,.getNat 664 660]
def rightBlock : List Op := [.add 660 653 663,.getNat 665 660]
def selectBlock : List Op := [.add 664 665 654]
def writeBlock : List Op := [.add 664 664 655,.add 660 653 658,
 .add 660 660 659,.putNat 660 664,.add 659 659 655]
theorem read_code : BlockAt readBlock program 13 := by
 intro i hi;change i<9 at hi;interval_cases i <;> rfl
theorem right_code : BlockAt rightBlock program 23 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem select_code : BlockAt selectBlock program 26 := by
 intro i hi;change i<1 at hi;interval_cases i;rfl
theorem write_code : BlockAt writeBlock program 28 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem gate_branch : program[12]?=some (.branchLT 659 651 13 34) := rfl
theorem kind_branch : program[22]?=some (.branchLT 661 657 23 28) := rfl
theorem max_branch : program[25]?=some (.branchLT 664 665 26 28) := rfl
theorem max_jump : program[27]?=some (.jump 28) := rfl
theorem gate_jump : program[33]?=some (.jump 12) := rfl
theorem halt_at : program[34]?=some .halt := rfl

structure GateCursor (N G d P i : ℕ) (s : State) : Prop where
 fixed : Fixed N G d P s
 pc : s.pc=12
 index : s.natReg 659=i
def PhysicalRow (d i : ℕ) (row : Row) (s : State) : Prop :=
 s.natHeap (d+5*i)=some row.opcode ∧ s.natHeap (d+5*i+1)=some row.left ∧
 s.natHeap (d+5*i+2)=some row.right
structure ReadCursor (N G d P i : ℕ) (row : Row) (value : ℕ) (s : State) : Prop where
 fixed : Fixed N G d P s
 pc : s.pc=22
 index : s.natReg 659=i
 opcode : s.natReg 661=row.opcode
 left : s.natReg 662=row.left
 right : s.natReg 663=row.right
 depth : s.natReg 664=value

theorem read_spec {N G d P i value : ℕ} {row : Row} {s : State}
 (h : GateCursor N G d P i s) (hr : PhysicalRow d i row s)
 (hv : s.natHeap (P+row.left)=some value) :
 ReadCursor N G d P i row value (applyBlock readBlock (setPC s 13)) := by
 have h0:s.natHeap (d+i*5)=some row.opcode:=by simpa [Nat.mul_comm] using hr.1
 have h1:s.natHeap (d+(i*5+1))=some row.left:=by simpa [Nat.mul_comm,Nat.add_assoc] using hr.2.1
 have h2:s.natHeap (d+(i*5+2))=some row.right:=by simpa [Nat.mul_comm,Nat.add_assoc] using hr.2.2
 refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [readBlock,applyBlock,Op.apply,setPC,writeNat,next,
  h.fixed.header.inputs,h.fixed.header.gates,h.fixed.header.tape,h.fixed.header.bank,
  h.fixed.zero,h.fixed.one,h.fixed.five,h.fixed.two,h.fixed.span,h.index,
  Nat.add_assoc,h0,h1,h2,hv]

theorem read_heap (s : State) :
 (applyBlock readBlock s).natHeap=s.natHeap := rfl
theorem read_frame (s : State) : Frame s (applyBlock readBlock s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r hr;simp (disch:=omega) [readBlock,applyBlock,Op.apply,writeNat,next]

theorem read_bounded {N G d P i value : ℕ} {row : Row} (B n : ℕ)
 (x : Fin n→ℂ) (s : State) (h : GateCursor N G d P i s)
 (hr : PhysicalRow d i row s) (hv : s.natHeap (P+row.left)=some value)
 (hi : i<G) (hl : row.left<N+1+i) (hh : row.right < N + 1 + i) (hvalue : value ≤ i)
 (hsource : d + 5*G ≤ P) (hbank : P + N + 1 + G ≤ B) (hc : 35 ≤ B) (hs : WordBound B s) :
 BoundedRuns program n x B s 10 (applyBlock readBlock (setPC s 13)) := by
 have enter:=UniformRadixInstructionMachine.branch_runs program n B 659 651 13 34 x s hs
   (by omega) (by omega) (by rw [h.pc];exact gate_branch)
 have lt:s.natReg 659<s.natReg 651:=by rw [h.index,h.fixed.header.gates];exact hi
 simp only [lt,ite_true] at enter
 let v:=setPC s 13
 have vb:WordBound B v:=by simpa [v,setPC] using enter.final_bound
 have h0:s.natHeap (d+i*5)=some row.opcode:=by simpa [Nat.mul_comm] using hr.1
 have h1:s.natHeap (d+(i*5+1))=some row.left:=by simpa [Nat.mul_comm,Nat.add_assoc] using hr.2.1
 have h2:s.natHeap (d+(i*5+2))=some row.right:=by simpa [Nat.mul_comm,Nat.add_assoc] using hr.2.2
 have readable:readable readBlock v:=by
   simp [readable,readBlock,Op.readable,Op.apply,writeNat,next,v,setPC,
     h.fixed.header.tape,h.fixed.header.bank,h.fixed.five,h.fixed.one,h.index,
     Nat.add_assoc,h0,h1,h2,hv]
 have op:row.opcode ≤ 2:=by cases row <;> simp [Row.opcode]
 have peak:peak readBlock v ≤ B:=by
   simp [peak,readBlock,Op.peak,Op.apply,writeNat,next,v,setPC,
     h.fixed.header.tape,h.fixed.header.bank,h.fixed.five,h.fixed.one,h.index,
     Nat.add_assoc,h0,h1,h2,hv]
   omega
 have run:=block_runs readBlock program 13 n B x v read_code rfl vb
   (by change 13+9 ≤ B;omega) readable peak
 simpa [show readBlock.length=9 from rfl,v,setPC] using enter.trans run

def Row.baseDepth (row : Row) (d : ℕ → ℕ) : ℕ := match row with
  | .add a b | .sub a b => max (d a) (d b)
  | .scale a => d a

theorem Row.depth_eq (row : Row) (d : ℕ → ℕ) : row.depth d = row.baseDepth d + 1 := by
  cases row <;> rfl

theorem Row.baseDepth_le (row : Row) (d : ℕ → ℕ) (i : ℕ)
    (h : ∀ a, d a ≤ i) : row.baseDepth d ≤ i := by
  cases row <;> simp [Row.baseDepth, h]

structure WriteCursor (N G d P i value : ℕ) (s : State) : Prop where
  fixed : Fixed N G d P s
  pc : s.pc = 28
  index : s.natReg 659 = i
  depth : s.natReg 664 = value

theorem right_spec {N G d P i left right : ℕ} {row : Row} {s : State}
    (h : ReadCursor N G d P i row left s)
    (hr : s.natHeap (P + row.right) = some right) :
    Fixed N G d P (applyBlock rightBlock (setPC s 23)) ∧
    (applyBlock rightBlock (setPC s 23)).pc = 25 ∧
    (applyBlock rightBlock (setPC s 23)).natReg 659 = i ∧
    (applyBlock rightBlock (setPC s 23)).natReg 664 = left ∧
    (applyBlock rightBlock (setPC s 23)).natReg 665 = right := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals simp [rightBlock, applyBlock, Op.apply, setPC, writeNat, next,
    h.fixed.header.inputs, h.fixed.header.gates, h.fixed.header.tape,
    h.fixed.header.bank, h.fixed.zero, h.fixed.one, h.fixed.five, h.fixed.two,
    h.fixed.span, h.index, h.depth, h.right, hr]

theorem right_frame (s : State) : Frame s (applyBlock rightBlock (setPC s 23)) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [rightBlock, applyBlock, Op.apply, setPC, writeNat, next]

theorem select_frame (s : State) : Frame s (applyBlock selectBlock (setPC s 26)) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [selectBlock, applyBlock, Op.apply, setPC, writeNat, next]

/-- Both binary branches compare the two physically loaded labels. -/
theorem binary_dispatch {N G d P i left right : ℕ} {row : Row}
    (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : ReadCursor N G d P i row left s) (hop : row.opcode < 2)
    (hr : s.natHeap (P + row.right) = some right)
    (href : row.right < N + 1 + i) (hi : i < G)
    (hrv : right ≤ i) (hbank : P + N + 1 + G ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedRuns program n x B s t u ∧ t ≤ 6 ∧
      WriteCursor N G d P i (max left right) u ∧
      u.natHeap = s.natHeap ∧ Frame s u := by
  have enter := UniformRadixInstructionMachine.branch_runs program n B 661 657 23 28 x s hs
    (by omega) (by omega) (by rw [h.pc]; exact kind_branch)
  have lt : s.natReg 661 < s.natReg 657 := by rw [h.opcode,h.fixed.two]; exact hop
  simp only [lt,ite_true] at enter
  let v := setPC s 23
  have vb : WordBound B v := enter.final_bound
  have rightReadable : readable rightBlock v := by
    simp [readable,rightBlock,Op.readable,Op.apply,writeNat,next,v,setPC,
      h.fixed.header.bank,h.right,hr]
  have rightPeak : peak rightBlock v ≤ B := by
    simp [peak,rightBlock,Op.peak,Op.apply,writeNat,next,v,setPC,
      h.fixed.header.bank,h.right,hr]
    omega
  have run := block_runs rightBlock program 23 n B x v right_code rfl vb
    (by change 23+2 ≤ B; omega) rightReadable rightPeak
  let w := applyBlock rightBlock v
  have hw := right_spec h hr
  change Fixed N G d P w ∧ w.pc = 25 ∧ w.natReg 659 = i ∧
    w.natReg 664 = left ∧ w.natReg 665 = right at hw
  have choose := UniformRadixInstructionMachine.branch_runs program n B 664 665 26 28 x w
    run.final_bound (by omega) (by omega) (by rw [hw.2.1]; exact max_branch)
  by_cases cmp : left < right
  · have cmp' : w.natReg 664 < w.natReg 665 := by rw [hw.2.2.2.1,hw.2.2.2.2]; exact cmp
    simp only [cmp',ite_true] at choose
    let z := setPC w 26
    have zf : Fixed N G d P z := hw.1.withPC
    have zp : peak selectBlock z ≤ B := by
      simp [peak,selectBlock,Op.peak,z,setPC,hw.2.2.2.2,hw.1.zero]
      omega
    have select := block_runs selectBlock program 26 n B x z select_code rfl choose.final_bound
      (by change 26+1 ≤ B; omega) (by simp [readable,selectBlock,Op.readable]) zp
    have pc : (applyBlock selectBlock z).pc = 27 := by rw [applyBlock_pc]; rfl
    have jump := UniformRadixInstructionMachine.jump_runs program n B 28 x (applyBlock selectBlock z)
      select.final_bound (by omega) (by rw [pc]; exact max_jump)
    let u := setPC (applyBlock selectBlock z) 28
    refine ⟨u,6,?_,by omega,?_,rfl,?_⟩
    · simpa [v,w,z,u,setPC,show rightBlock.length=2 from rfl,
        show selectBlock.length=1 from rfl] using enter.trans (run.trans (choose.trans (select.trans jump)))
    · refine ⟨?_,rfl,?_,?_⟩
      · refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
        all_goals simp [u,selectBlock,applyBlock,Op.apply,setPC,writeNat,next,
          zf.header.inputs,zf.header.gates,zf.header.tape,zf.header.bank,
          zf.zero,zf.one,zf.five,zf.two,zf.span]
      · simp [u,selectBlock,applyBlock,Op.apply,setPC,writeNat,next,z,hw.2.2.1]
      · simp [u,selectBlock,applyBlock,Op.apply,setPC,writeNat,next,z,hw.2.2.2.2,
          hw.1.zero,max_eq_right (Nat.le_of_lt cmp)]
    · exact (right_frame s).trans ((select_frame w).withPC)
  · have cmp' : ¬ w.natReg 664 < w.natReg 665 := by rw [hw.2.2.2.1,hw.2.2.2.2]; exact cmp
    simp only [cmp',ite_false] at choose
    refine ⟨setPC w 28,4,?_,by omega,⟨hw.1.withPC,rfl,hw.2.2.1,?_⟩,rfl,(right_frame s).withPC⟩
    · simpa [v,w,setPC,show rightBlock.length=2 from rfl] using enter.trans (run.trans choose)
    · change w.natReg 664 = max left right
      rw [hw.2.2.2.1,max_eq_left (Nat.le_of_not_gt cmp)]

/-- A scaling has one data operand; no coefficient becomes a data edge. -/
theorem scale_dispatch {N G d P i a left : ℕ} (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : ReadCursor N G d P i (.scale a) left s) (hc : 35 ≤ B)
    (hs : WordBound B s) :
    BoundedRuns program n x B s 1 (setPC s 28) ∧
      WriteCursor N G d P i left (setPC s 28) := by
  have run := UniformRadixInstructionMachine.branch_runs program n B 661 657 23 28 x s hs
    (by omega) (by omega) (by rw [h.pc]; exact kind_branch)
  have cmp : ¬ s.natReg 661 < s.natReg 657 := by rw [h.opcode,h.fixed.two]; simp [Row.opcode]
  simp only [cmp,ite_false] at run
  exact ⟨run,⟨h.fixed.withPC,rfl,h.index,h.depth⟩⟩

/-- The only heap write for a gate appends its newly computed depth. -/
def writeIteration (s : State) : State := setPC (applyBlock writeBlock s) 12

theorem writeIteration_heap {N G d P i value : ℕ} {s : State}
    (h : WriteCursor N G d P i value s) :
    (writeIteration s).natHeap = Function.update s.natHeap (P + N + 1 + i) (some (value + 1)) := by
  simp [writeIteration,writeBlock,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.bank,h.fixed.span,h.index,h.depth,h.fixed.one,Nat.add_assoc]

theorem writeIteration_cursor {N G d P i value : ℕ} {s : State}
    (h : WriteCursor N G d P i value s) :
    GateCursor N G d P (i+1) (writeIteration s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩,rfl,?_⟩
  all_goals simp [writeIteration,writeBlock,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.inputs,h.fixed.header.gates,h.fixed.header.tape,h.fixed.header.bank,
    h.fixed.zero,h.fixed.one,h.fixed.five,h.fixed.two,h.fixed.span,h.index]

theorem writeIteration_frame (s : State) : Frame s (writeIteration s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [writeIteration,writeBlock,applyBlock,Op.apply,setPC,writeNat,next]

theorem writeIteration_bounded {N G d P i value : ℕ} (B n : ℕ)
    (x : Fin n → ℂ) (s : State) (h : WriteCursor N G d P i value s)
    (hi : i < G) (hv : value ≤ i) (hbank : P + N + 1 + G ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    BoundedRuns program n x B s 6 (writeIteration s) := by
  have hr : readable writeBlock s := by simp [readable,writeBlock,Op.readable]
  have hp : peak writeBlock s ≤ B := by
    simp [peak,writeBlock,Op.peak,Op.apply,writeNat,next,
      h.fixed.header.bank,h.fixed.span,h.fixed.one,h.index,h.depth]
    omega
  have run := block_runs writeBlock program 28 n B x s write_code h.pc hs
    (by change 28+5 ≤ B; omega) hr hp
  have pc : (applyBlock writeBlock s).pc = 33 := by rw [applyBlock_pc,h.pc]; rfl
  have jump := UniformRadixInstructionMachine.jump_runs program n B 12 x (applyBlock writeBlock s)
    run.final_bound (by omega) (by rw [pc]; exact gate_jump)
  simpa [writeIteration,setPC,show writeBlock.length=5 from rfl] using run.trans jump

/-- One actual row, with all reads, comparisons and the depth write charged. -/
theorem row_execution {N G d P i : ℕ} (row : Row) (labels : ℕ → ℕ)
    (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : GateCursor N G d P i s) (hr : PhysicalRow d i row s)
    (hb : DepthBank P (N+1+i) labels s)
    (ht : ∀ a ∈ row.refs, a < N+1+i) (hi : i < G)
    (hv : ∀ a, labels a ≤ i) (hsource : d+5*G ≤ P)
    (hbank : P+N+1+G ≤ B) (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedRuns program n x B s t u ∧ t ≤ 22 ∧
      GateCursor N G d P (i+1) u ∧
      u.natHeap = Function.update s.natHeap (P+N+1+i) (some (row.depth labels)) ∧
      Frame s u := by
  have hl : row.left < N+1+i := by cases row <;> apply ht <;> simp [Row.refs,Row.left]
  have hh : row.right < N+1+i := by
    cases row with
    | add a b => exact ht b (by simp [Row.refs])
    | sub a b => exact ht b (by simp [Row.refs])
    | scale a => simp [Row.right]
  have left := hb row.left hl
  have read := read_bounded B n x s h hr left hi hl hh (hv _) hsource hbank hc hs
  let v := applyBlock readBlock (setPC s 13)
  have vr : ReadCursor N G d P i row (labels row.left) v := read_spec h hr left
  have dispatch : ∃ w t, BoundedRuns program n x B v t w ∧ t ≤ 6 ∧
      WriteCursor N G d P i (row.baseDepth labels) w ∧
      w.natHeap = v.natHeap ∧ Frame v w := by
    cases row with
    | add a b =>
      exact binary_dispatch B n x v vr (by simp [Row.opcode])
        (hb b hh) hh hi (hv _) hbank hc read.final_bound
    | sub a b =>
      exact binary_dispatch B n x v vr (by simp [Row.opcode])
        (hb b hh) hh hi (hv _) hbank hc read.final_bound
    | scale a =>
      have run := scale_dispatch B n x v vr hc read.final_bound
      exact ⟨setPC v 28,1,run.1,by omega,run.2,rfl,(frame_refl v).withPC⟩
  obtain ⟨w,t,run,tc,wc,wh,wf⟩ := dispatch
  have write := writeIteration_bounded B n x w wc hi (row.baseDepth_le labels i hv)
    hbank hc run.final_bound
  refine ⟨writeIteration w,10+t+6,read.trans (run.trans write),by omega,
    writeIteration_cursor wc,?_,?_⟩
  · rw [writeIteration_heap wc,wh,Row.depth_eq]
    rfl
  · exact (read_frame (setPC s 13)).trans (wf.trans (writeIteration_frame w))

/-- Uniform label magnitudes grow by at most one per printed gate. -/
theorem evaluate_bound (start i : ℕ) (rs : List Row) (labels : ℕ → ℕ)
    (h : ∀ a, labels a ≤ i) : ∀ a, evaluate start rs labels a ≤ i + rs.length := by
  induction rs generalizing start i labels with
  | nil => simpa [evaluate] using h
  | cons row rs ih =>
    have hd : row.depth labels ≤ i+1 := by rw [Row.depth_eq]; exact Nat.add_le_add_right (row.baseDepth_le labels i h) 1
    have hu : ∀ a, Function.update labels start (row.depth labels) a ≤ i+1 := by
      intro a
      by_cases he : a = start
      · simp [he,Function.update,hd]
      · rw [Function.update_of_ne he]; exact (h a).trans (by omega)
    have hi := ih (start+1) (i+1) (Function.update labels start (row.depth labels)) hu
    simpa [evaluate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

/-- Appending one heap cell extends the existing exact prefix. -/
theorem depthBank_update {P size value : ℕ} {labels : ℕ → ℕ} {s u : State}
    (hb : DepthBank P size labels s)
    (hh : u.natHeap = Function.update s.natHeap (P+size) (some value)) :
    DepthBank P (size+1) (Function.update labels size value) u := by
  intro a ha
  rw [hh]
  by_cases he : a = size
  · simp [he,Function.update]
  · have hn : P+a ≠ P+size := by omega
    rw [Function.update_of_ne hn,Function.update_of_ne he]
    exact hb a (by omega)

/-- A suffix retains its original physical tape offset. -/
def OffsetTape (d i : ℕ) (rs : List Row) (s : State) : Prop :=
  ∀ j : Fin rs.length, PhysicalRow d (i+j.val) rs[j] s

def OffsetTopological (N i : ℕ) (rs : List Row) : Prop :=
  ∀ j : Fin rs.length, ∀ a ∈ rs[j].refs, a < N+1+i+j.val

theorem OffsetTape.ofTape {d : ℕ} {rs : List Row} {s : State}
    (h : Tape d rs s) : OffsetTape d 0 rs s := by
  intro j
  simpa only [PhysicalRow,Nat.zero_add] using h j

theorem OffsetTopological.ofTopological {N : ℕ} {rs : List Row}
    (h : Topological N rs) : OffsetTopological N 0 rs := by
  intro j a ha
  simpa only [Nat.add_zero] using h j a ha

theorem OffsetTape.tail {d i : ℕ} {row : Row} {rs : List Row} {s : State}
    (h : OffsetTape d i (row::rs) s) : OffsetTape d (i+1) rs s := by
  intro j
  have hj := h ⟨j.val+1,by simpa only [List.length_cons] using Nat.add_lt_add_right j.isLt 1⟩
  change PhysicalRow d (i+1+j.val) rs[j.val] s
  change PhysicalRow d (i+(j.val+1)) (row::rs)[j.val+1] s at hj
  simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj

theorem OffsetTopological.tail {N i : ℕ} {row : Row} {rs : List Row}
    (h : OffsetTopological N i (row::rs)) : OffsetTopological N (i+1) rs := by
  intro j a ha
  have hj := h ⟨j.val+1,by simpa only [List.length_cons] using Nat.add_lt_add_right j.isLt 1⟩ a
  simpa only [List.get_eq_getElem,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj ha

theorem OffsetTape.update_after {d i G P address value : ℕ} {rs : List Row} {s u : State}
    (h : OffsetTape d i rs s) (hi : i+rs.length=G) (hsource : d+5*G ≤ P)
    (ha : P ≤ address) (hh : u.natHeap = Function.update s.natHeap address (some value)) :
    OffsetTape d i rs u := by
  intro j
  have hb : d+5*(i+j.val)+2 < P := by have := j.isLt; omega
  have h0 : d+5*(i+j.val) ≠ address := by omega
  have h1 : d+5*(i+j.val)+1 ≠ address := by omega
  have h2 : d+5*(i+j.val)+2 ≠ address := by omega
  simpa only [PhysicalRow,hh,Function.update_of_ne h0,Function.update_of_ne h1,
    Function.update_of_ne h2] using h j

theorem Tape.outside {N G d P : ℕ} {rs : List Row} {s u : State}
    (h : Tape d rs s) (hlen : rs.length=G) (hsource : d+5*G ≤ P)
    (ho : Outside P N s u) : Tape d rs u := by
  intro j
  have hb : d+5*j.val+2 < P := by have := j.isLt; omega
  rcases h j with ⟨h0,h1,h2⟩
  exact ⟨(ho _ (Or.inl (by omega))).trans h0,
    (ho _ (Or.inl (by omega))).trans h1,(ho _ (Or.inl (by omega))).trans h2⟩

/-- The suffix induction derives every label and its magnitude from earlier
    physical writes. The entry theorem below starts with internally written zeros. -/
theorem gate_loop (rs : List Row) {N G d P i : ℕ} (labels : ℕ → ℕ)
    (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : GateCursor N G d P i s) (hi : i+rs.length=G)
    (ht : OffsetTape d i rs s) (htop : OffsetTopological N i rs)
    (hb : DepthBank P (N+1+i) labels s) (hv : ∀ a, labels a ≤ i)
    (hsource : d+5*G ≤ P) (hbank : P+N+1+G ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedRuns program n x B s t u ∧ t ≤ 22*rs.length ∧
      GateCursor N G d P G u ∧
      DepthBank P (N+1+G) (evaluate (N+1+i) rs labels) u ∧
      Outside P (N+1+G) s u ∧ Frame s u := by
  induction rs generalizing i labels s with
  | nil =>
    have he : i=G := by simpa using hi
    subst i
    exact ⟨s,0,.refl hs,by simp,h,hb,fun _ _ => rfl,frame_refl s⟩
  | cons row rs ih =>
    simp only [List.length_cons] at hi
    have hrow : PhysicalRow d i row s := by
      have h0 := ht ⟨0,by simp⟩
      change PhysicalRow d (i+0) (row::rs)[0] s at h0
      simpa only [Nat.add_zero,List.getElem_cons_zero] using h0
    have hrt : ∀ a ∈ row.refs, a < N+1+i := by
      have h0 := htop ⟨0,by simp⟩
      change ∀ a ∈ (row::rs)[0].refs, a < N+1+i+0 at h0
      simpa only [Nat.add_zero,List.getElem_cons_zero] using h0
    obtain ⟨v,t,run,tc,vc,vh,vf⟩ := row_execution row labels B n x s h hrow hb hrt
      (by omega) hv hsource hbank hc hs
    let updated := Function.update labels (N+1+i) (row.depth labels)
    have ub : DepthBank P (N+1+(i+1)) updated v := by
      have out := depthBank_update hb (by simpa only [Nat.add_assoc] using vh)
      simpa only [updated,Nat.add_assoc] using out
    have uv : ∀ a, updated a ≤ i+1 := by
      intro a
      by_cases he : a=N+1+i
      · simpa [updated,Function.update,he,Row.depth_eq] using
          Nat.add_le_add_right (row.baseDepth_le labels i hv) 1
      · simp only [updated,Function.update_of_ne he]
        exact (hv a).trans (by omega)
    have vt := (OffsetTape.update_after ht hi hsource (by omega) vh).tail
    obtain ⟨u,t',run',tc',uc,uh,uo,uf⟩ := ih updated v vc
      (by omega) vt htop.tail ub uv run.final_bound
    refine ⟨u,t+t',run.trans run',?_,uc,?_,?_,vf.trans uf⟩
    · simp only [List.length_cons]; omega
    · simpa only [evaluate,updated,Nat.add_assoc] using uh
    · intro a ha
      rw [uo a ha,vh,Function.update_of_ne (by omega)]

/-- Universal initialized execution of the fixed 35-instruction depth producer.
    Its only readiness premise is the actual topological five-field tape. -/
theorem execution (N d P B n : ℕ) (rs : List Row) (x : Fin n → ℂ) (s : State)
    (h : Header N rs.length d P s) (hpc : s.pc=0)
    (ht : Tape d rs s) (htop : Topological N rs)
    (hsource : d+5*rs.length ≤ P) (hbank : P+N+1+rs.length ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedExecution program n x B s t u ∧
      t ≤ runtimeBudget N rs.length ∧ u.pc=34 ∧
      Header N rs.length d P u ∧
      DepthBank P (N+1+rs.length) (evaluate (N+1) rs (fun _ => 0)) u ∧
      Tape d rs u ∧ Outside P (N+1+rs.length) s u ∧ Frame s u := by
  obtain ⟨v,start,fixed,pc,index,bank,outside,frame⟩ := initialize_depth N rs.length d P B n x s h hpc hc (by omega) hs
  have tape : Tape d rs v := Tape.outside ht rfl hsource outside
  obtain ⟨w,t,run,tc,wc,wb,wo,wf⟩ := gate_loop rs (fun _ => 0) B n x v
    ⟨fixed,pc,index⟩ (by simp) (OffsetTape.ofTape tape) (OffsetTopological.ofTopological htop) bank (by simp)
    hsource hbank hc start.final_bound
  have stop := UniformRadixInstructionMachine.branch_runs program n B 659 651 13 34 x w
    run.final_bound (by omega) (by omega) (by rw [wc.pc]; exact gate_branch)
  have cmp : ¬ w.natReg 659 < w.natReg 651 := by rw [wc.index,wc.fixed.header.gates]; omega
  simp only [cmp,ite_false] at stop
  let u := setPC w 34
  have halt : BoundedExecution program n x B u 1 u := .halt stop.final_bound (by
    simp only [UniformMachine.step,show program[u.pc]?=some .halt from halt_at])
  refine ⟨u,5*(N+1)+8+t+1+1,?_,by unfold runtimeBudget; omega,rfl,wc.fixed.withPC.header,?_,?_,?_,?_⟩
  · exact (start.trans (run.trans stop)).executes halt
  · intro a ha
    change w.natHeap (P+a) = _
    simpa only [Nat.add_zero] using wb a ha
  · apply Tape.outside tape rfl hsource wo
  · intro a ha
    exact (wo a ha).trans (outside a (by unfold Outside at outside; omega))
  · exact frame.trans wf

theorem erase_refs {r : ℕ} (g : UniformConvolutionDAG.Expr r ℕ) :
    (erase g).refs = g.refs := by cases g <;> rfl

/-- Topological depth dependencies are derived from the actual typed constructors. -/
theorem rows_topological {r N t : ℕ} (p : UniformReplayPrint.Program r N t) :
    Topological N (rows p) := by
  intro j a ha
  have hj : j.val < (UniformToeplitzCrossDAG.programRecords p).length := by
    simpa only [rows,List.length_map] using j.isLt
  let g := (UniformToeplitzCrossDAG.programRecords p)[j.val]'hj
  have he : (rows p)[j] = erase g := by
    change ((UniformToeplitzCrossDAG.programRecords p).map erase)[j.val] = _
    rw [List.getElem_map]
  rw [he,erase_refs] at ha
  exact UniformToeplitzCrossTopologyMachine.programRecords_before p j.val g
    (List.getElem?_eq_getElem hj) a ha

theorem erase_encoded_fields {r : ℕ} (g : UniformConvolutionDAG.Expr r ℕ) :
    (UniformConvolutionTopologyMachine.encode g).opcode = (erase g).opcode ∧
    (UniformConvolutionTopologyMachine.encode g).left = (erase g).left ∧
    (UniformConvolutionTopologyMachine.encode g).right = (erase g).right := by
  cases g with
  | add a b | sub a b => exact ⟨rfl,rfl,rfl⟩
  | scale c a => cases c <;> exact ⟨rfl,rfl,rfl⟩

/-- These first three fields are read from the same five-field physical tape
    actually produced by the convolution/cross topology machines. -/
def EncodedTape {r N t : ℕ} (p : UniformReplayPrint.Program r N t) (d : ℕ) (s : State) : Prop :=
  UniformToeplitzCrossTopologyMachine.RowTable
    ((UniformToeplitzCrossDAG.programRecords p).map UniformConvolutionTopologyMachine.encode) d s

theorem tape_of_encoded {r N t d : ℕ} {p : UniformReplayPrint.Program r N t} {s : State}
    (h : EncodedTape p d s) : Tape d (rows p) s := by
  intro j
  have hj : j.val < (UniformToeplitzCrossDAG.programRecords p).length := by
    simpa only [rows,List.length_map] using j.isLt
  let g := (UniformToeplitzCrossDAG.programRecords p)[j.val]'hj
  have he : (rows p)[j] = erase g := by
    change ((UniformToeplitzCrossDAG.programRecords p).map erase)[j.val] = _
    rw [List.getElem_map]
  have hp := h j.val (UniformConvolutionTopologyMachine.encode g) (by
    rw [List.getElem?_map,List.getElem?_eq_getElem hj]; rfl)
  change s.natHeap (d+5*j.val) = some (rows p)[j].opcode ∧
    s.natHeap (d+5*j.val+1) = some (rows p)[j].left ∧
    s.natHeap (d+5*j.val+2) = some (rows p)[j].right
  rw [he]
  have fields := And.intro hp.1 (And.intro hp.2.1 hp.2.2.1)
  have shape := erase_encoded_fields g
  simpa only [shape.1,shape.2.1,shape.2.2] using fields

/-- Physical labels for the real typed DAG; no caller-provided label function
    or topological certificate occurs in this interface. -/
theorem typed_execution {r N t : ℕ} (p : UniformReplayPrint.Program r N t)
    (d P B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Header N t d P s) (hpc : s.pc=0) (ht : EncodedTape p d s)
    (hsource : d+5*t ≤ P) (hbank : P+N+1+t ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u time, BoundedExecution program n x B s time u ∧
      time ≤ runtimeBudget N t ∧ u.pc=34 ∧ Header N t d P u ∧
      (∀ a : Fin (N+1+t), u.natHeap (P+a.val) =
        some (UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a)) ∧
      (∀ a : Fin (N+1+t), UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a ≤ t) ∧
      Tape d (rows p) u ∧ Outside P (N+1+t) s u ∧ Frame s u := by
  obtain ⟨u,time,run,cost,pc,header,bank,tape,outside,frame⟩ := execution N d P B n (rows p) x s
    (by simpa only [rows_length] using h) hpc (tape_of_encoded ht) (rows_topological p)
    (by simpa only [rows_length] using hsource) (by simpa only [rows_length] using hbank) hc hs
  refine ⟨u,time,run,by simpa only [rows_length] using cost,pc,
    by simpa only [rows_length] using header,?_,?_,tape,
    by simpa only [rows_length] using outside,frame⟩
  · intro a
    have ha : a.val < N+1+(rows p).length := by simpa only [rows_length] using a.isLt
    simpa only [evaluate_typed] using bank a.val ha
  · intro a
    have hb := evaluate_bound (N+1) 0 (rows p) (fun _ => 0) (by simp) a.val
    simpa only [Nat.zero_add,rows_length,evaluate_typed] using hb

/-- All five physical fields survive; the depth bank is disjoint from the tape. -/
theorem EncodedTape.outside {r N t d P size : ℕ} {p : UniformReplayPrint.Program r N t}
    {s u : State} (h : EncodedTape p d s) (hsource : d+5*t ≤ P)
    (ho : Outside P size s u) : EncodedTape p d u := by
  intro j row hj
  have hlt : j < t := by
    obtain ⟨hv,_⟩ := List.getElem?_eq_some_iff.mp hj
    simpa only [List.length_map,UniformToeplitzCrossDAG.programRecords_length] using hv
  have hb : d+5*j+4 < P := by omega
  have fields := h j row hj
  exact ⟨(ho _ (Or.inl (by omega))).trans fields.1,
    (ho _ (Or.inl (by omega))).trans fields.2.1,
    (ho _ (Or.inl (by omega))).trans fields.2.2.1,
    (ho _ (Or.inl (by omega))).trans fields.2.2.2.1,
    (ho _ (Or.inl (by omega))).trans fields.2.2.2.2⟩

/-- The retained coefficient fields remain available to subsequent replay printers. -/
theorem typed_execution_full {r N t : ℕ} (p : UniformReplayPrint.Program r N t)
    (d P B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Header N t d P s) (hpc : s.pc=0) (ht : EncodedTape p d s)
    (hsource : d+5*t ≤ P) (hbank : P+N+1+t ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u time, BoundedExecution program n x B s time u ∧
      time ≤ runtimeBudget N t ∧ u.pc=34 ∧ Header N t d P u ∧
      (∀ a : Fin (N+1+t), u.natHeap (P+a.val) =
        some (UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a)) ∧
      (∀ a : Fin (N+1+t), UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a ≤ t) ∧
      EncodedTape p d u ∧ Outside P (N+1+t) s u ∧ Frame s u := by
  obtain ⟨u,time,run,cost,pc,header,bank,bound,_,outside,frame⟩ :=
    typed_execution p d P B n x s h hpc ht hsource hbank hc hs
  exact ⟨u,time,run,cost,pc,header,bank,bound,
    EncodedTape.outside ht hsource outside,outside,frame⟩

/-- The actual rank-three cross graph supplies its stronger height bound. -/
theorem cross_execution (K a e : ℕ)
    (ha : a ≤ UniformRadixTwoDAG.width K) (he : e ≤ UniformRadixTwoDAG.width K)
    (d P B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Header e (UniformToeplitzCrossDAG.crossDAG K a e ha he).size d P s)
    (hpc : s.pc=0)
    (ht : EncodedTape (UniformToeplitzCrossDAG.crossDAG K a e ha he).program d s)
    (hsource : d+5*(UniformToeplitzCrossDAG.crossDAG K a e ha he).size ≤ P)
    (hbank : P+e+1+(UniformToeplitzCrossDAG.crossDAG K a e ha he).size ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u time, BoundedExecution program n x B s time u ∧
      time ≤ runtimeBudget e (UniformToeplitzCrossDAG.crossDAG K a e ha he).size ∧
      u.pc=34 ∧ Header e (UniformToeplitzCrossDAG.crossDAG K a e ha he).size d P u ∧
      (∀ i : Fin (e+1+(UniformToeplitzCrossDAG.crossDAG K a e ha he).size),
        u.natHeap (P+i.val) = some (UniformToeplitzCrossDAG.runDepth
          (UniformToeplitzCrossDAG.crossDAG K a e ha he).program (fun _ => 0) i)) ∧
      (∀ i : Fin (e+1+(UniformToeplitzCrossDAG.crossDAG K a e ha he).size),
        UniformToeplitzCrossDAG.runDepth (UniformToeplitzCrossDAG.crossDAG K a e ha he).program
          (fun _ => 0) i ≤ 8*K+6) ∧
      EncodedTape (UniformToeplitzCrossDAG.crossDAG K a e ha he).program d u ∧
      Outside P (e+1+(UniformToeplitzCrossDAG.crossDAG K a e ha he).size) s u ∧ Frame s u := by
  obtain ⟨u,time,run,cost,pc,header,bank,_,tape,outside,frame⟩ :=
    typed_execution_full (UniformToeplitzCrossDAG.crossDAG K a e ha he).program d P B n x s
      h hpc ht hsource hbank hc hs
  exact ⟨u,time,run,cost,pc,header,bank,UniformToeplitzCrossDAG.crossDAG_depth K a e ha he,
    tape,outside,frame⟩

/-- Saved headers used by the global preparation driver lie outside scratch. -/
theorem Frame.saved {s u : State} (h : Frame s u) :
    ∀ r,100 ≤ r → r ≤ 106 → u.natReg r = s.natReg r := by
  intro r _ hr
  exact h.2.2.2.2 r (Or.inl (by omega))

/-- Empty typed programs, including zero inputs, use the same literal program. -/
theorem empty_execution (N d P B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Header N 0 d P s) (hpc : s.pc=0) (hbank : P+N+1 ≤ B)
    (hc : 35 ≤ B) (hs : WordBound B s) :
    ∃ u time, BoundedExecution program n x B s time u ∧
      time = 5*(N+1)+10 ∧ u.pc=34 ∧ DepthBank P (N+1) (fun _ => 0) u ∧
      Outside P (N+1) s u ∧ Frame s u := by
  obtain ⟨v,start,fixed,pc,index,bank,outside,frame⟩ := initialize_depth N 0 d P B n x s h hpc hc hbank hs
  have stop := UniformRadixInstructionMachine.branch_runs program n B 659 651 13 34 x v
    start.final_bound (by omega) (by omega) (by rw [pc]; exact gate_branch)
  have cmp : ¬ v.natReg 659 < v.natReg 651 := by rw [index,fixed.header.gates]; omega
  simp only [cmp,ite_false] at stop
  let u := setPC v 34
  have halt : BoundedExecution program n x B u 1 u := .halt stop.final_bound (by
    simp only [UniformMachine.step,show program[u.pc]?=some .halt from halt_at])
  refine ⟨u,5*(N+1)+8+1+1,(start.trans stop).executes halt,by omega,rfl,bank,outside,frame⟩


/-- Literal zero-port and repeated operand occurrences are retained. -/
theorem repeated_operand_fixture :
    evaluate 1 [.add 0 0,.sub 1 1,.scale 2] (fun _ => 0) 3 = 3 := by decide

theorem right_deeper_fixture :
    evaluate 1 [.scale 0,.add 0 1,.sub 0 2] (fun _ => 0) 3 = 3 := by decide

theorem left_deeper_fixture :
    evaluate 1 [.scale 0,.sub 1 0,.add 2 0] (fun _ => 0) 3 = 3 := by decide

theorem rational_coefficient_fixture :
    erase (.scale (.rational (-3/4)) 0 : UniformConvolutionDAG.Expr 1 ℕ) = .scale 0 := rfl

theorem prepared_coefficient_fixture :
    erase (.scale (.prepared 0 true) 0 : UniformConvolutionDAG.Expr 1 ℕ) = .scale 0 := rfl

end
end ExactFourierCircuits.UniformDAGDepthMachine
