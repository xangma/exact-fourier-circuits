import UniformCacheTimingControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingForwardRows
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)

def Values (T o : ℕ) (L : List ℕ) (s : State) : Prop :=
 ∀ j (hj : j < L.length), s.natHeap (T+o+j)=some (L[j]'hj)
def writeStarts (T o start : ℕ) : List ℕ → (ℕ→Option ℕ) → (ℕ→Option ℕ)
 | [],heap => heap
 | v::vs,heap => writeStarts T (o+1) start vs (Function.update heap (T+o) (some (start+v)))
structure Cursor (D R U V T N K k count o j start : ℕ) (s : State) : Prop
 extends Init D R U V T N K k s where
 count : s.natReg 6523=count
 ordinal : s.natReg 6529=o
 rowIndex : s.natReg 6530=j
 start : s.natReg 6534=start
noncomputable section
lemma Cursor.pc {D R U V T N K k count o j start : ℕ} {s : State}
 (h : Cursor D R U V T N K k count o j start s) (p : ℕ) :
 Cursor D R U V T N K k count o j start (setPC s p) :=
 ⟨h.toInit.pc p,h.count,h.ordinal,h.rowIndex,h.start⟩
lemma Values.pc {T o : ℕ} {L : List ℕ} {s : State} (h : Values T o L s) (p : ℕ) :
 Values T o L (setPC s p) := h
lemma Values.head {T o v : ℕ} {vs : List ℕ} {s : State} (h : Values T o (v::vs) s) :
 s.natHeap (T+o)=some v := by
 have hh:=h 0 (by simp)
 change s.natHeap (T+o+0)=some ((v::vs)[0]'(by simp)) at hh
 simpa only [List.getElem_cons_zero,Nat.add_zero] using hh
lemma row_cursor {D R U V T N K k count o j start : ℕ} (s : State)
 (h : Cursor D R U V T N K k count o j start s) :
 Cursor D R U V T N K k count (o+1) (j+1) start (applyBlock startRow s) := by
 constructor
 · constructor
   · constructor <;>simp [startRow,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [startRow,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [startRow,applyBlock,Op.apply,writeNat,next,h.count,h.ordinal,h.rowIndex,h.start,h.one]
lemma row_heap {D R U V T N K k count o j start v : ℕ} (s : State)
 (h : Cursor D R U V T N K k count o j start s) (hv : s.natHeap (T+o)=some v) :
 (applyBlock startRow s).natHeap=Function.update s.natHeap (T+o) (some (start+v)) := by
 simp [startRow,applyBlock,Op.apply,writeNat,next,h.requestStarts,h.ordinal,h.start,h.one,hv]
lemma row_regs (s : State) (r : ℕ) (hr : r<6529∨r=6533∨6535<r) :
 (applyBlock startRow s).natReg r=s.natReg r := by
 simp (disch:=omega) [startRow,applyBlock,Op.apply,writeNat,next]
lemma row_tail {D R U V T N K k count o j start v : ℕ} {vs : List ℕ} (s : State)
 (h : Cursor D R U V T N K k count o j start s) (hv : Values T o (v::vs) s) :
 Values T (o+1) vs (applyBlock startRow s) := by
 intro i hi
 rw [row_heap s h hv.head]
 have ne : T+(o+1)+i≠T+o := by omega
 rw [Function.update_of_ne ne]
 have hh:=hv (i+1) (by simpa using Nat.succ_lt_succ hi)
 change s.natHeap (T+o+(i+1))=some ((v::vs)[i+1]'(by simpa using Nat.succ_lt_succ hi)) at hh
 simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Each prefix word is physically read, shifted, and stored; eight instructions
per row include both loop controls. No supplied output bank is used. -/
theorem loop (n D R U V T N K k count o j start B : ℕ) (L : List ℕ)
 (x : Fin n→ℂ) (s : State) (h : Cursor D R U V T N K k count o j start s)
 (values : Values T o L s) (endIndex : j+L.length=count) (hp : s.pc=110)
 (hs : WordBound B s) (code : 122≤B) (destination : T+o+L.length≤B)
 (total : ∀v∈L,start+v≤B) : ∃u,
 BoundedRuns program n x B s (8*L.length+1) u ∧ u.pc=118 ∧
 Cursor D R U V T N K k count (o+L.length) count start u ∧
 u.natHeap=writeStarts T o start L s.natHeap ∧
 (∀r,r<6529∨r=6533∨6535<r→u.natReg r=s.natReg r) := by
 induction L generalizing o j s with
 | nil =>
  have eq : j=count := by simpa using endIndex
  have step : UniformMachine.step program n x s=.running (setPC s 118) := by
   simp [UniformMachine.step,hp,code_110,h.rowIndex,h.count,eq,setPC]
  refine ⟨setPC s 118,control_run program n B 118 x s hs (by omega) step,rfl,?_,rfl,fun _ _=>rfl⟩
  simpa [eq] using h.pc 118
 | cons v vs ih =>
  have hj : j<count := by simp only [List.length_cons] at endIndex;omega
  have step : UniformMachine.step program n x s=.running (setPC s 111) := by
   simp [UniformMachine.step,hp,code_110,h.rowIndex,h.count,hj,setPC]
  have enter:=control_run program n B 111 x s hs (by omega) step
  let a:=setPC s 111
  have av : s.natHeap (T+o)=some v := values.head
  have vb:=total v (by simp)
  have read:=block_runs startRow program 111 n B x a startRow_code rfl enter.final_bound
   (by change 117≤B;omega) (by
    simp [startRow,readable,Op.readable,Op.apply,writeNat,next,a,setPC,h.requestStarts,h.ordinal,av]) (by
    simp [startRow,peak,Op.peak,Op.apply,writeNat,next,a,setPC,h.requestStarts,h.ordinal,h.rowIndex,h.start,h.one,av]
    have jb : j≤B := by simpa [h.rowIndex] using hs.2.1 6530
    have cb : count≤B := by simpa [h.count] using hs.2.1 6523
    simp only [List.length_cons] at destination
    omega)
  have pc : (applyBlock startRow a).pc=117 := by rw [applyBlock_pc];rfl
  have backStep : UniformMachine.step program n x (applyBlock startRow a)=
   .running (setPC (applyBlock startRow a) 110) := by
   simp [UniformMachine.step,pc,code_117,setPC]
  have back:=control_run program n B 110 x (applyBlock startRow a) read.final_bound (by omega) backStep
  obtain ⟨u,tail,up,uh,heap,regs⟩:=ih (o+1) (j+1) (setPC (applyBlock startRow a) 110)
   ((row_cursor a (h.pc 111)).pc 110) ((row_tail a (h.pc 111) (values.pc 111)).pc 110)
   (by simp only [List.length_cons] at endIndex;omega) rfl back.final_bound
   (by simp only [List.length_cons] at destination;omega) (by intro w hw;exact total w (by simp [hw]))
  refine ⟨u,?_,up,?_,?_,?_⟩
  · convert ((enter.trans read).trans back).trans tail using 1
    change 8*(vs.length+1)+1=1+6+1+(8*vs.length+1)
    omega
  · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using uh
  · change u.natHeap=writeStarts T (o+1) start vs (applyBlock startRow a).natHeap at heap
    rw [row_heap a (h.pc 111) av] at heap
    simpa only [writeStarts,a,setPC] using heap
  · intro r hr
    exact (regs r hr).trans (row_regs a r hr)

lemma writeStarts_outside (T o start : ℕ) (L : List ℕ) (heap : ℕ→Option ℕ)
 (a : ℕ) (ha : a<T+o∨T+o+L.length≤a) : writeStarts T o start L heap a=heap a := by
 induction L generalizing o heap with
 | nil => rfl
 | cons v vs ih =>
  rw [writeStarts,ih (o+1) _ (by simp only [List.length_cons] at ha;omega)]
  have ne : a≠T+o := by simp only [List.length_cons] at ha;omega
  exact Function.update_of_ne ne _ _
lemma writeStarts_value (T o start : ℕ) (L : List ℕ) (heap : ℕ→Option ℕ)
 (j : ℕ) (hj : j<L.length) : writeStarts T o start L heap (T+o+j)=some (start+L[j]) := by
 induction L generalizing o heap j with
 | nil => simp at hj
 | cons v vs ih =>
  cases j with
  | zero =>
   rw [writeStarts,writeStarts_outside]
   · simp
   · left;omega
  | succ j =>
   simpa only [writeStarts,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    ih (o+1) _ j (by simpa using hj)
end
end ExactFourierCircuits.UniformCacheTimingForwardRows
