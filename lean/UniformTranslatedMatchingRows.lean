import UniformMatchingAxisTableMachine
import UniformCrossShearTableMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformTranslatedMatchingRows
open UniformMachine UniformColoring
open UniformInPlaceMachine (Row)
open UniformCrossShearTableMachine (RowFields Table putRow)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section

/-- Raw three-field rows are translated into a fresh bank. Only endpoints
change; coefficient addresses stay exact. No scalar value participates. -/
def boot : List Op := [.literal 4994 0,.literal 4995 1,.literal 4996 3]
def body : List Op := [.mul 4998 4994 4996,.add 4998 4991 4998,.getNat 5000 4998,
  .add 4998 4998 4995,.getNat 5001 4998,.add 4998 4998 4995,.getNat 5002 4998,
  .add 5000 4993 5000,.add 5001 4993 5001,
  .mul 4999 4994 4996,.add 4999 4992 4999,.putNat 4999 5000,
  .add 4999 4999 4995,.putNat 4999 5001,.add 4999 4999 4995,.putNat 4999 5002,
  .add 4994 4994 4995]
def program : Program := boot.map Op.code++[.branchLT 4994 4990 4 22]++body.map Op.code++[.jump 3,.halt]
theorem program_length : program.length=23 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem body_code : BlockAt body program 4 := by intro i hi;change i<17 at hi;interval_cases i <;> rfl
theorem branch_code : program[3]?=some (.branchLT 4994 4990 4 22) := rfl
theorem jump_code : program[21]?=some (.jump 3) := rfl
theorem halt_code : program[22]?=some .halt := rfl
def translated (o : ℕ) (row : Row) : Row := ⟨o+row.dst,o+row.src,row.coefficient⟩
def edge (o : ℕ) (e : Edge) : Edge := ⟨o+e.left,o+e.right,by simpa using e.different⟩
theorem conflict_iff (o : ℕ) (e f : Edge) : Conflict (edge o e) (edge o f)↔Conflict e f := by
  simp [Conflict,Incident,edge]
theorem matching {M : ℕ} (o : ℕ) (E : Fin M→Edge)
    (h:UniformMatchingAxisTableMachine.Matching E) :
    UniformMatchingAxisTableMachine.Matching (fun i=>edge o (E i)) := by
  intro i j hij
  simpa only [conflict_iff] using h i j hij
theorem inRange {M v R : ℕ} (o : ℕ) (E : Fin M→Edge)
    (h:UniformMatchingAxisTableMachine.InRange v E) (extent:o+v≤R) :
    UniformMatchingAxisTableMachine.InRange R (fun i=>edge o (E i)) := by
  intro i
  have hi:=h i
  simp only [edge]
  omega

structure Header (count A D o i : ℕ) (s : State) : Prop where
  count : s.natReg 4990=count
  source : s.natReg 4991=A
  destination : s.natReg 4992=D
  offset : s.natReg 4993=o
  index : s.natReg 4994=i
  one : s.natReg 4995=1
  three : s.natReg 4996=3
  pc : s.pc=3
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀q,q<4994 ∨ 5002<q→u.natReg q=s.natReg q
theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (f:Frame s u) (g:Frame u v) : Frame s v :=
  ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
    g.2.2.2.1.trans f.2.2.2.1,fun q h=>(g.2.2.2.2 q h).trans (f.2.2.2.2 q h)⟩
def Outside (D count : ℕ) (s u : State) : Prop :=
  ∀a,a<D ∨ D+3*count≤a→u.natHeap a=s.natHeap a
def nextRow (s : State) := setPC (applyBlock body (setPC s 4)) 3
theorem nextRow_frame (s : State) : Frame s (nextRow s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q h
  simp (disch:=omega) [nextRow,body,applyBlock,Op.apply,setPC,writeNat,next]
theorem nextRow_header {count A D o i : ℕ} {s : State} (h:Header count A D o i s) :
    Header count A D o (i+1) (nextRow s) := by
  constructor <;> simp [nextRow,body,applyBlock,Op.apply,setPC,writeNat,next,
    h.count,h.source,h.destination,h.offset,h.index,h.one,h.three]
theorem nextRow_heap {count A D o i : ℕ} {s : State} (h:Header count A D o i s)
    (row : Row) (hf:RowFields (A+3*i) row s.natHeap) :
    (nextRow s).natHeap=putRow (D+3*i) (translated o row) s.natHeap := by
  obtain ⟨h0,h1,h2⟩:=hf
  simp only [Nat.mul_comm,Nat.add_assoc] at h0 h1 h2
  simp [nextRow,body,applyBlock,Op.apply,setPC,writeNat,next,putRow,translated,
    h.source,h.destination,h.offset,h.index,h.one,h.three,Nat.add_assoc,Nat.mul_comm,h0,h1,h2]
theorem nextRow_fields {count A D o i : ℕ} {s : State} (h:Header count A D o i s)
    (row : Row) (hf:RowFields (A+3*i) row s.natHeap) :
    RowFields (D+3*i) (translated o row) (nextRow s).natHeap := by
  rw [nextRow_heap h row hf]
  simp [RowFields,putRow,translated]
theorem nextRow_outside {count A D o i : ℕ} {s : State} (h:Header count A D o i s)
    (row : Row) (hf:RowFields (A+3*i) row s.natHeap) (hi:i<count) : Outside D count s (nextRow s) := by
  intro a ha
  rw [nextRow_heap h row hf]
  exact UniformCrossShearTableMachine.putRow_outside (D+3*i) a (translated o row) s.natHeap (by omega)

theorem iteration {n count A D o i B v : ℕ} (x : Fin n→ℂ) (s : State)
    (h:Header count A D o i s) (hi:i<count) (row : Row)
    (hf:RowFields (A+3*i) row s.natHeap) (hv:row.dst<v ∧ row.src<v)
    (code:23≤B) (aBound:A+3*count≤B) (dBound:D+3*count≤B)
    (rangeBound:o+v≤B) (bound:WordBound B s) :
    BoundedRuns program n x B s 19 (nextRow s) := by
  have countB:count≤B:=by simpa only [h.count] using bound.2.1 4990
  have hc:row.coefficient≤B:=(bound.2.2.1 (A+3*i+2) row.coefficient hf.2.2).2
  let e:=setPC s 4
  have eb:=changePC_bound B s 4 bound (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next bound
    (by simp [step,branch_code,h.pc,h.index,h.count,hi,e,setPC]) (.refl eb)
  obtain ⟨h0,h1,h2⟩:=hf
  simp only [Nat.mul_comm,Nat.add_assoc] at h0 h1 h2
  have bodyRun:=block_runs body program 4 n B x e body_code rfl eb
    (by change 4+17≤B;omega)
    (by simp [body,readable,Op.readable,Op.apply,writeNat,next,e,setPC,
      h.source,h.index,h.one,h.three,Nat.add_assoc,h0,h1,h2])
    (by simp [body,peak,Op.peak,Op.apply,writeNat,next,e,setPC,
      h.source,h.destination,h.offset,h.index,h.one,h.three,Nat.add_assoc,h0,h1,h2];omega)
  have pc:(applyBlock body e).pc=21:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock body e) 1 (nextRow s):=.next bodyRun.final_bound
    (by
      change step program n x (applyBlock body e)=.running (setPC (applyBlock body e) 3)
      simp only [step,pc,jump_code]
      rfl)
    (.refl (changePC_bound B _ 3 bodyRun.final_bound (by omega)))
  convert (branch.trans bodyRun).trans jump using 1
  rfl

def Partial (D o i : ℕ) (rows : List Row) (s : State) : Prop :=
  ∀j,(hj:j<rows.length)→j < i→RowFields (D+3*j) (translated o (rows[j]'hj)) s.natHeap
theorem fields_before (D j i : ℕ) (hi:j < i) (row earlier : Row) (heap : ℕ→Option ℕ)
    (h:RowFields (D+3*j) earlier heap) : RowFields (D+3*j) earlier (putRow (D+3*i) row heap) := by
  unfold RowFields at h ⊢
  rw [UniformCrossShearTableMachine.putRow_outside (D+3*i) (D+3*j) row heap (by omega),
    UniformCrossShearTableMachine.putRow_outside (D+3*i) (D+3*j+1) row heap (by omega),
    UniformCrossShearTableMachine.putRow_outside (D+3*i) (D+3*j+2) row heap (by omega)]
  exact h
theorem nextRow_partial {A D o i : ℕ} {rows : List Row} {s : State}
    (h:Header rows.length A D o i s) (hi:i<rows.length) (src:Table A rows s)
    (hp:Partial D o i rows s) : Partial D o (i+1) rows (nextRow s) := by
  intro j hj hjp
  by_cases he:j=i
  · subst j
    exact nextRow_fields h _ (src i hi)
  · rw [nextRow_heap h _ (src i hi)]
    exact fields_before D j i (by omega) _ _ _ (hp j hj (by omega))
theorem Outside.source {A D : ℕ} {rows : List Row} {s u : State}
    (outside:Outside D rows.length s u) (sep:A+3*rows.length≤D) (src:Table A rows s) : Table A rows u := by
  intro j hj
  have h:=src j hj
  unfold RowFields at h ⊢
  rw [outside (A+3*j) (Or.inl (by omega)),outside (A+3*j+1) (Or.inl (by omega)),
    outside (A+3*j+2) (Or.inl (by omega))]
  exact h
theorem Outside.trans {D count : ℕ} {s u v : State} (f:Outside D count s u) (g:Outside D count u v) :
    Outside D count s v := fun a h=>(g a h).trans (f a h)

theorem loop_execution (n B A D o v remaining : ℕ) (rows : List Row) (x : Fin n→ℂ)
    (range:∀row∈rows,row.dst<v ∧ row.src<v) (sep:A+3*rows.length≤D)
    (code:23≤B) (aBound:A+3*rows.length≤B) (dBound:D+3*rows.length≤B) (rangeBound:o+v≤B) :
    ∀i s,i+remaining=rows.length→Header rows.length A D o i s→Table A rows s→
    Partial D o i rows s→WordBound B s→∃u,
    BoundedExecution program n x B s (19*remaining+2) u ∧ Table A rows u ∧
    Partial D o rows.length rows u ∧ Frame s u ∧ Outside D rows.length s u ∧ u.pc=22 := by
  induction remaining with
  | zero =>
    intro i s eq h src values bound
    have he:i=rows.length:=by omega
    let u:=setPC s 22
    have ub:=changePC_bound B s 22 bound (by omega)
    refine ⟨u,?_,src,?_,.refl s,fun _ _=>rfl,rfl⟩
    · simp only [Nat.mul_zero,Nat.zero_add]
      exact .next bound (by simp [step,branch_code,h.pc,h.index,h.count,he,u,setPC])
        (.halt ub (by simp [step,halt_code,u,setPC]))
    · intro j hj hji
      exact values j hj (by omega)
  | succ remaining ih =>
    intro i s eq h src values bound
    have hi:i<rows.length:=by omega
    have first:=iteration x s h hi (rows[i]'hi) (src i hi)
      (range _ (List.getElem_mem hi)) code aBound dBound rangeBound bound
    have outside:=nextRow_outside h _ (src i hi) hi
    obtain ⟨u,last,source,result,frame,rest,pcu⟩:=ih (i+1) (nextRow s) (by omega)
      (nextRow_header h) (outside.source sep src) (nextRow_partial h hi src values) first.final_bound
    refine ⟨u,?_,source,result,(nextRow_frame s).trans frame,outside.trans rest,pcu⟩
    convert first.executes last using 1
    omega

def bootState (s : State) := applyBlock boot s
theorem boot_frame (s : State) : Frame s (bootState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q h
  simp (disch:=omega) [bootState,boot,applyBlock,Op.apply,writeNat,next]
theorem boot_header {count A D o : ℕ} {s : State} (pc:s.pc=0)
    (countVal:s.natReg 4990=count) (source:s.natReg 4991=A)
    (dest:s.natReg 4992=D) (offset:s.natReg 4993=o) : Header count A D o 0 (bootState s) := by
  constructor <;> simp [bootState,boot,applyBlock,Op.apply,writeNat,next,pc,countVal,source,dest,offset]

/-- Execute all retained original rows. The producer itself establishes the
translated table; every scalar/flag and every unrelated memory word survives. -/
theorem execution (n B A D o v : ℕ) (rows : List Row) (x : Fin n→ℂ) (s : State)
    (pc:s.pc=0) (countVal:s.natReg 4990=rows.length) (source:s.natReg 4991=A)
    (dest:s.natReg 4992=D) (offset:s.natReg 4993=o) (src:Table A rows s)
    (range:∀row∈rows,row.dst<v ∧ row.src<v) (sep:A+3*rows.length≤D)
    (code:23≤B) (aBound:A+3*rows.length≤B) (dBound:D+3*rows.length≤B)
    (rangeBound:o+v≤B) (bound:WordBound B s) : ∃u,
    BoundedExecution program n x B s (19*rows.length+5) u ∧
    Table D (rows.map (translated o)) u ∧ Table A rows u ∧
    Frame s u ∧ Outside D rows.length s u ∧ u.pc=22 := by
  have first:=block_runs boot program 0 n B x s boot_code pc bound (by change 0+3≤B;omega)
    (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
  have empty:Partial D o 0 rows (bootState s):=by intro j hj hp;omega
  obtain ⟨u,last,source',values,frame,outside,pcu⟩:=loop_execution n B A D o v rows.length rows x
    range sep code aBound dBound rangeBound 0 (bootState s) (by omega)
    (boot_header pc countVal source dest offset) src empty first.final_bound
  refine ⟨u,?_,?_,source',(boot_frame s).trans frame,outside,pcu⟩
  · convert first.executes last using 1
    change 19*rows.length+5=3+(19*rows.length+2)
    omega
  · intro j hj
    simpa only [List.length_map,List.getElem_map] using values j (by simpa using hj) (by simpa using hj)

end
end ExactFourierCircuits.UniformTranslatedMatchingRows
