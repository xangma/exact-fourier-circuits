import UniformRadixTwoMachine
import UniformRadixRowTableMachine
import UniformRadixPowerBankMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformOffsetLinearMachine
open UniformMachine
open UniformPreparationMachine (Row opcode)

/-- Nat register 0 supplies row count, register 9 the first output address.
Three Nat-heap entries per row hold opcode, left address and right address.
All scalar arithmetic uses exactly the original instruction alphabet. -/
def program : Program := [
  .natLiteral 2 1,.natLiteral 3 3,.natLiteral 1 0,
  .branchLT 1 0 4 31,.natBinary .mul 4 1 3,.natBinary .add 4 4 137,.loadNat 5 4,
  .natBinary .add 4 4 2,.loadNat 6 4,.natBinary .add 4 4 2,.loadNat 7 4,
  .loadScalar 0 6,.loadScalar 1 7,.natLiteral 8 1,.branchLT 5 8 15 17,
  .fieldBinary .add 2 0 1,.jump 27,.natLiteral 8 2,.branchLT 5 8 19 21,
  .fieldBinary .sub 2 0 1,.jump 27,.natLiteral 8 3,.branchLT 5 8 23 25,
  .fieldBinary .mul 2 0 1,.jump 27,.fieldBinary .div 2 0 1,.jump 27,
  .storeScalar 9 2,.natBinary .add 9 9 2,.natBinary .add 1 1 2,.jump 3,.halt]

theorem program_length : program.length=32 := rfl

def rowCost : FieldOp → ℕ
  | .add => 18 | .sub => 20 | .mul => 22 | .div => 22

theorem rowCost_bound (op : FieldOp) : rowCost op ≤ 22 := by cases op <;> decide

noncomputable section

/-- Table validity is local: a successful field instruction includes the division
certificate, and no complex equality test occurs in the program. -/
def Ready (row : Row) (s : State) (a b v : Scalar) : Prop :=
  s.pc = 3 ∧ s.natReg 1 < s.natReg 0 ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧
  s.natHeap (s.natReg 137+3 * s.natReg 1) = some (opcode row.op) ∧
  s.natHeap (s.natReg 137+3 * s.natReg 1 + 1) = some row.left ∧
  s.natHeap (s.natReg 137+3 * s.natReg 1 + 2) = some row.right ∧
  s.scalarHeap row.left = some a ∧ s.scalarHeap row.right = some b ∧
  evalField row.op a b = some v

def entered (s : State) : State := { s with pc := 4 }
def rawPointer (s : State) : State := writeNat (entered s) 4 (3*s.natReg 1)
def pointer (s : State) : State := writeNat (rawPointer s) 4 (s.natReg 137+3*s.natReg 1)
def tagState (row : Row) (s : State) : State := writeNat (pointer s) 5 (opcode row.op)
def leftPointer (row : Row) (s : State) : State := writeNat (tagState row s) 4 (s.natReg 137+3 * s.natReg 1 + 1)
def leftState (row : Row) (s : State) : State := writeNat (leftPointer row s) 6 row.left
def rightPointer (row : Row) (s : State) : State := writeNat (leftState row s) 4 (s.natReg 137+3 * s.natReg 1 + 2)
def rightState (row : Row) (s : State) : State := writeNat (rightPointer row s) 7 row.right
def leftValue (row : Row) (s : State) (a : Scalar) : State := writeScalar (rightState row s) 0 a
def rightValue (row : Row) (s : State) (a b : Scalar) : State := writeScalar (leftValue row s a) 1 b
def dispatch (row : Row) (s : State) (a b : Scalar) : State := writeNat (rightValue row s a b) 8 1

def arithmeticPC : FieldOp → ℕ
  | .add => 15 | .sub => 19 | .mul => 23 | .div => 25

def arithmeticState (row : Row) (s : State) (a b : Scalar) : State :=
  let z := dispatch row s a b
  match row.op with
  | .add => { z with pc := 15 }
  | .sub => { writeNat { z with pc := 17 } 8 2 with pc := 19 }
  | .mul => { writeNat { writeNat { z with pc := 17 } 8 2 with pc := 21 } 8 3 with pc := 23 }
  | .div => { writeNat { writeNat { z with pc := 17 } 8 2 with pc := 21 } 8 3 with pc := 25 }

def computed (row : Row) (s : State) (a b v : Scalar) : State :=
  { writeScalar (arithmeticState row s a b) 2 v with pc := 27 }
def stored (row : Row) (s : State) (a b v : Scalar) : State :=
  { next (computed row s a b v) with scalarHeap := Function.update s.scalarHeap (s.natReg 9) (some v) }
def advanced (row : Row) (s : State) (a b v : Scalar) : State :=
  writeNat (stored row s a b v) 9 (s.natReg 9 + 1)
def rowEnd (row : Row) (s : State) (a b v : Scalar) : State :=
  { writeNat (advanced row s a b v) 1 (s.natReg 1 + 1) with pc := 3 }

theorem prefix_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s 11 (dispatch row s a b) := by
  obtain ⟨hpc, hi, h1, h3, hop, hl, hr, ha, hb, _⟩ := hr
  simp only [Nat.add_comm] at hop hl hr
  refine .next (u := entered s) ?_ (.next (u := rawPointer s) ?_ (.next (u := pointer s) ?_ (.next (u := tagState row s) ?_ (.next (u := leftPointer row s) ?_ (.next (u := leftState row s) ?_ (.next (u := rightPointer row s) ?_ (.next (u := rightState row s) ?_ (.next (u := leftValue row s a) ?_ (.next (u := rightValue row s a b) ?_ (.next (u := dispatch row s a b) ?_ (.refl _)))))))))))
  all_goals simp [step, program, entered, pointer, rawPointer, tagState, leftPointer, leftState,
    rightPointer, rightState, leftValue, rightValue, dispatch, writeNat, writeScalar,
    next, hpc, hi, h1, h3, hop, hl, hr, ha, hb, evalNat,Nat.mul_comm,Nat.add_comm]
  all_goals (congr 1;omega)

theorem dispatch_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b : Scalar) :
    Runs program n x (dispatch row s a b)
      (match row.op with | .add => 1 | .sub => 3 | .mul => 5 | .div => 5)
      (arithmeticState row s a b) := by
  cases hop : row.op
  · exact .next (by simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer, rawPointer,
      entered, writeNat, writeScalar, next]) (.refl _)
  · refine .next (u := { dispatch row s a b with pc := 17 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 17 } 8 2) ?_
      (.next ?_ (.refl _)))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer, rawPointer,
      entered, writeNat, writeScalar, next]
  · refine .next (u := { dispatch row s a b with pc := 17 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 17 } 8 2) ?_
      (.next (u := { writeNat { dispatch row s a b with pc := 17 } 8 2 with pc := 21 }) ?_
      (.next (u := writeNat { writeNat { dispatch row s a b with pc := 17 } 8 2 with pc := 21 } 8 3) ?_
      (.next ?_ (.refl _)))))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer, rawPointer,
      entered, writeNat, writeScalar, next]
  · refine .next (u := { dispatch row s a b with pc := 17 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 17 } 8 2) ?_
      (.next (u := { writeNat { dispatch row s a b with pc := 17 } 8 2 with pc := 21 }) ?_
      (.next (u := writeNat { writeNat { dispatch row s a b with pc := 17 } 8 2 with pc := 21 } 8 3) ?_
      (.next ?_ (.refl _)))))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer, rawPointer,
      entered, writeNat, writeScalar, next]


theorem suffix_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (h1 : s.natReg 2 = 1) (hv : evalField row.op a b = some v) :
    Runs program n x (arithmeticState row s a b) 6 (rowEnd row s a b v) := by
  refine .next (u := writeScalar (arithmeticState row s a b) 2 v) ?_
    (.next (u := computed row s a b v) ?_
    (.next (u := stored row s a b v) ?_
    (.next (u := advanced row s a b v) ?_
    (.next (u := writeNat (advanced row s a b v) 1 (s.natReg 1 + 1)) ?_
    (.next ?_ (.refl _))))))
  all_goals cases hop : row.op <;>
    simp only [hop] at hv <;>
    simp [step, program, rowEnd, advanced, stored, computed, arithmeticState,
      dispatch, rightValue, leftValue, rightState, rightPointer, leftState,
      leftPointer, tagState, pointer, rawPointer, entered, writeNat, writeScalar, next,
      evalNat, hop, h1, hv, Nat.add_comm]

theorem row_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s (rowCost row.op) (rowEnd row s a b v) := by
  have h := (prefix_runs n x row s a b v hr).trans
    ((dispatch_runs n x row s a b).trans (suffix_runs n x row s a b v hr.2.2.1 hr.2.2.2.2.2.2.2.2.2))
  cases hop : row.op <;> simpa [rowCost, hop] using h

/-- One instruction record's frame: no input, output, root or integer-heap effect. -/
theorem row_frame (row : Row) (s : State) (a b v : Scalar) :
    (rowEnd row s a b v).pc = 3 ∧
    (rowEnd row s a b v).natReg 0 = s.natReg 0 ∧
    (rowEnd row s a b v).natReg 1 = s.natReg 1 + 1 ∧
    (rowEnd row s a b v).natReg 2 = s.natReg 2 ∧
    (rowEnd row s a b v).natReg 3 = s.natReg 3 ∧
    (rowEnd row s a b v).natReg 9 = s.natReg 9 + 1 ∧
    (rowEnd row s a b v).natHeap = s.natHeap ∧
    (rowEnd row s a b v).scalarHeap = Function.update s.scalarHeap (s.natReg 9) (some v) ∧
    (rowEnd row s a b v).outputs = s.outputs ∧
    (rowEnd row s a b v).rootOrders = s.rootOrders := by
  cases hop : row.op <;> simp [hop, rowEnd, advanced, stored, computed, arithmeticState,
    dispatch, rightValue, leftValue, rightState, rightPointer, leftState,
    leftPointer, tagState, pointer, rawPointer, entered, writeNat, writeScalar, next]


def totalCost (rows:List Row) : ℕ := (rows.map (fun row=>rowCost row.op)).sum

theorem totalCost_bound (rows:List Row) : totalCost rows≤22*rows.length := by
  induction rows with
  | nil => simp [totalCost]
  | cons row rows ih =>
    have h:=rowCost_bound row.op
    simp only [totalCost,List.map_cons,List.sum_cons,List.length_cons] at *;omega

inductive ValidSchedule : List Row → State → State → Prop where
  | nil (s : State) : ValidSchedule [] s s
  | cons {row : Row} {rows : List Row} {s u : State} {a b v : Scalar}
      (ready : Ready row s a b v)
      (tail : ValidSchedule rows (rowEnd row s a b v) u) :
      ValidSchedule (row :: rows) s u

theorem ValidSchedule.runs {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) (n : ℕ) (x : Fin n → ℂ) :
    Runs program n x s (totalCost rows) u := by
  induction h with
  | nil s => exact .refl s
  | @cons row rows s u a b v hr _ ih =>
    simpa [totalCost] using (row_runs n x row s a b v hr).trans ih

theorem ValidSchedule.pc {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) (hpc : s.pc = 3) : u.pc = 3 := by
  induction h with
  | nil s => exact hpc
  | @cons row rows s u a b v hr _ ih => exact ih (row_frame row s a b v).1

theorem ValidSchedule.counters {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) :
    u.natReg 1 = s.natReg 1 + rows.length ∧
    u.natReg 9 = s.natReg 9 + rows.length ∧
    u.natReg 0 = s.natReg 0 ∧ u.natHeap = s.natHeap ∧
    u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  induction h with
  | nil s => simp
  | @cons row rows s u a b v hr _ ih =>
    have hf := row_frame row s a b v
    obtain ⟨_,h0,h1,_,_,h9,hn,_,ho,hd⟩ := hf
    simpa [h0,h1,h9,hn,ho,hd, Nat.add_assoc, Nat.add_left_comm,Nat.add_comm] using ih

def Counters (k a d : ℕ) (s : State) : Prop :=
  3 ≤ s.pc ∧ s.pc ≤ 31 ∧ s.natReg 0 = k ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧ s.natReg 137=d ∧
  s.natReg 1 ≤ k ∧ (4 ≤ s.pc → s.pc ≤ 29 → s.natReg 1 < k) ∧
  s.natReg 9 ≤ a + k ∧ (s.pc ≠ 29 → s.natReg 9 = a + s.natReg 1) ∧
  (s.pc=5→s.natReg 4=3*s.natReg 1) ∧
  (6 ≤ s.pc → s.pc ≤ 7 → s.natReg 4 = d+3*s.natReg 1) ∧
  (8 ≤ s.pc → s.pc ≤ 9 → s.natReg 4 = d+3*s.natReg 1+1) ∧
  (s.pc = 29 → s.natReg 9 = a+s.natReg 1+1)

def Interior (k a d B : ℕ) (s : State) : Prop := WordBound B s ∧ Counters k a d s

theorem store_bound (B : ℕ) (s : State) (v : Scalar) (hs : WordBound B s)
    (hpc : s.pc + 1 ≤ B) :
    WordBound B { next s with scalarHeap := Function.update s.scalarHeap (s.natReg 9) (some v) } := by
  obtain ⟨_, hr, hn, hc, ho, hd⟩ := hs
  refine ⟨hpc,hr,hn,?_,ho,hd⟩
  intro j w hw
  by_cases hj : j = s.natReg 9
  · subst j; exact hr 9
  · exact hc j w (by simpa [hj] using hw)

/-- All successful interior instructions preserve the counters and word bound.
This includes table loads, destination increments and the loop exit. -/
theorem step_interior (n : ℕ) (x : Fin n → ℂ) (k a d B : ℕ) (s u : State)
    (hB : d+4*k+a+42 ≤ B) (hs : Interior k a d B s)
    (h : step program n x s = .running u) : Interior k a d B u := by
  obtain ⟨hb,hlo,hhi,hk,h1,h3,hbase,hi,hstrict,haddr,hrel,hraw,hptr1,hptr2,hplus⟩ := hs
  have hpc : s.pc+1 ≤ B := by omega
  have hscalar (dst : ℕ) (v : Scalar) := writeScalar_bound B s dst v hb hpc
  have hnat (dst value : ℕ) (hv : value ≤ B) := writeNat_bound B s dst value hb hpc hv
  have hrel' : s.pc = 29 ∨ s.natReg 9 = a+s.natReg 1 := by
    by_cases hp : s.pc = 29
    · exact Or.inl hp
    · exact Or.inr (hrel hp)
  have hstrict' : s.pc < 4 ∨ 29 < s.pc ∨ s.natReg 1 < k := by
    by_cases hlo : 4 ≤ s.pc
    · by_cases hhi : s.pc ≤ 29
      · exact Or.inr (Or.inr (hstrict hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  have hptr1' : s.pc < 6 ∨ 7 < s.pc ∨ s.natReg 4 = d+3*s.natReg 1 := by
    by_cases hlo : 6 ≤ s.pc
    · by_cases hhi : s.pc ≤ 7
      · exact Or.inr (Or.inr (hptr1 hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  have hptr2' : s.pc < 8 ∨ 9 < s.pc ∨ s.natReg 4 = d+3*s.natReg 1+1 := by
    by_cases hlo : 8 ≤ s.pc
    · by_cases hhi : s.pc ≤ 9
      · exact Or.inr (Or.inr (hptr2 hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  interval_cases hp : s.pc
  · by_cases he : s.natReg 1 < k
    · simp [step,program,hp,hk,he] at h; subst u
      refine ⟨changePC_bound B s 4 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,hk,he] at h; subst u
      refine ⟨changePC_bound B s 31 hb (by omega), ?_⟩
      simp [Counters]; omega
  · simp [step,program,hp,h3,evalNat] at h; subst u
    refine ⟨hnat 4 (s.natReg 1*3) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · have hptr:=hraw rfl
    simp [step,program,hp,hbase,evalNat] at h;subst u
    refine ⟨hnat 4 (s.natReg 4+d) (by omega),?_⟩
    simp [Counters,writeNat,next,hp];omega
  · cases ht : s.natHeap (s.natReg 4) with
    | none => simp [step,program,hp,ht] at h
    | some v =>
      simp [step,program,hp,ht] at h; subst u
      refine ⟨hnat 5 v (hb.2.2.1 _ _ ht).2, ?_⟩
      simp [Counters,writeNat,next,hp]; omega
  · simp [step,program,hp,h1,evalNat] at h; subst u
    refine ⟨hnat 4 (s.natReg 4+1) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · cases ht : s.natHeap (s.natReg 4) with
    | none => simp [step,program,hp,ht] at h
    | some v =>
      simp [step,program,hp,ht] at h; subst u
      refine ⟨hnat 6 v (hb.2.2.1 _ _ ht).2, ?_⟩
      simp [Counters,writeNat,next,hp]; omega
  · simp [step,program,hp,h1,evalNat] at h; subst u
    refine ⟨hnat 4 (s.natReg 4+1) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · cases ht : s.natHeap (s.natReg 4) with
    | none => simp [step,program,hp,ht] at h
    | some v =>
      simp [step,program,hp,ht] at h; subst u
      refine ⟨hnat 7 v (hb.2.2.1 _ _ ht).2, ?_⟩
      simp [Counters,writeNat,next,hp]; omega
  · cases ht : s.scalarHeap (s.natReg 6) with
    | none => simp [step,program,hp,ht] at h
    | some v =>
      simp [step,program,hp,ht] at h; subst u
      refine ⟨hscalar 0 v, ?_⟩
      simp [Counters,writeScalar,next,hp]; omega
  · cases ht : s.scalarHeap (s.natReg 7) with
    | none => simp [step,program,hp,ht] at h
    | some v =>
      simp [step,program,hp,ht] at h; subst u
      refine ⟨hscalar 1 v, ?_⟩
      simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨hnat 8 1 (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 8
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 15 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 17 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .add) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 27 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨hnat 8 2 (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 8
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 19 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 21 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .sub) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 27 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨hnat 8 3 (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 8
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 23 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 25 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .mul) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 27 hb (by omega), ?_⟩
    simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .div) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 27 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨store_bound B s _ hb (by simpa [hp] using hpc), ?_⟩
    simp [Counters,next,hp]; omega
  · simp [step,program,hp,h1,evalNat] at h; subst u
    refine ⟨hnat 9 (s.natReg 9+1) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · have hdest := hplus rfl
    simp [step,program,hp,h1,evalNat] at h; subst u
    refine ⟨hnat 1 (s.natReg 1+1) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 3 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h


def initialized (s : State) : State := writeNat (writeNat (writeNat s 2 1) 3 3) 1 0

theorem startup_bounded (n : ℕ) (x : Fin n → ℂ) (k a d B : ℕ) (s : State)
    (hB : d+4*k+a+42 ≤ B) (hpc : s.pc = 0) (hb : WordBound B s) :
    BoundedRuns program n x B s 3 (initialized s) := by
  have hb1 := writeNat_bound B s 2 1 hb (by omega) (by omega)
  have hb2 := writeNat_bound B (writeNat s 2 1) 3 3 hb1
    (by simp [writeNat,next,hpc]; omega) (by omega)
  have hb3 := writeNat_bound B (writeNat (writeNat s 2 1) 3 3) 1 0 hb2
    (by simp [writeNat,next,hpc]; omega) (by omega)
  refine .next (u := writeNat s 2 1) hb ?_
    (.next (u := writeNat (writeNat s 2 1) 3 3) hb1 ?_
    (.next hb2 ?_ (.refl hb3)))
  all_goals simp [step,program,initialized,writeNat,next,hpc]

theorem initialized_counters (k a d : ℕ) (s : State)
    (hpc : s.pc = 0) (hk : s.natReg 0 = k) (ha : s.natReg 9 = a) (hd:s.natReg 137=d) :
    Counters k a d (initialized s) := by
  simp [Counters,initialized,writeNat,next,hpc,hk,ha,hd]

theorem exit_executes (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 3) (hi : s.natReg 0 ≤ s.natReg 1) :
    Executes program n x s 2 {s with pc := 31} := by
  refine .next ?_ (.halt ?_)
  · simp [step,program,hpc,Nat.not_lt.mpr hi]
  · simp [step,program]



theorem interpreted_schedule (n : ℕ) (x : Fin n → ℂ) (rows : List Row) (a d B : ℕ)
    (s u : State) (hB : d+4*rows.length+a+42 ≤ B)
    (hpc : s.pc = 0) (hk : s.natReg 0 = rows.length) (ha : s.natReg 9 = a)
    (hd:s.natReg 137=d) (hb : WordBound B s) (valid : ValidSchedule rows (initialized s) u) :
    BoundedExecution program n x B s (totalCost rows+5) {u with pc := 31} ∧
      totalCost rows+5 ≤ 22*rows.length+5 ∧
      u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.natHeap = s.natHeap := by
  have hstart := startup_bounded n x rows.length a d B s hB hpc hb
  have hc := initialized_counters rows.length a d s hpc hk ha hd
  have hi : Interior rows.length a d B (initialized s) := ⟨hstart.final_bound,hc⟩
  have hr := valid.runs n x
  have hrun := hr.bounded_of_invariant (Interior rows.length a d B) hi
    (fun _ h => h.1) (fun s u h => step_interior n x rows.length a d B s u hB h)
  have hufit := hrun.final_bound
  have hfinal := valid.counters
  have huc : Counters rows.length a d u := by
    have hpres : ∀ s u, Interior rows.length a d B s → step program n x s = .running u →
        Interior rows.length a d B u := fun s u h => step_interior n x rows.length a d B s u hB h
    -- Recover the same invariant from the actual segment, without assuming its end state.
    have general : ∀ {s u t}, Runs program n x s t u → Interior rows.length a d B s →
        Interior rows.length a d B u := by
      intro s u t h
      induction h with
      | refl _ => exact id
      | next hs _ ih => intro h; exact ih (hpres _ _ h hs)
    exact (general hr hi).2
  have hcounter : u.natReg 1 = rows.length := by
    simpa [initialized,writeNat,next] using hfinal.1
  have hu0 := huc.2.2.1
  have hupc := valid.pc (by simp [initialized,writeNat,next,hpc])
  have hex := exit_executes n x u hupc (by omega)
  have hbexit := hex.bounded_of_invariant (Interior rows.length a d B)
    ⟨hufit,huc⟩ (fun _ h => h.1)
    (fun s u h => step_interior n x rows.length a d B s u hB h)
  refine ⟨?_,by have h := totalCost_bound rows; omega,?_,?_,?_⟩
  · convert hstart.executes (hrun.executes hbexit) using 1; omega
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.1
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.2
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.1




/-- Complete integer metadata and unrelated scalar-register frame. -/
def Frame (s u:State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,r=0 ∨ 10≤r→u.natReg r=s.natReg r) ∧ (∀r,3≤r→u.scalarReg r=s.scalarReg r)

theorem Frame.refl (s:State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v:State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem row_full_frame (row:Row) (s:State) (a b v:Scalar) : Frame s (rowEnd row s a b v) := by
  obtain ⟨_,_,_,_,_,_,hh,_,ho,hr⟩:=row_frame row s a b v
  refine ⟨hh,ho,hr,?_,?_⟩
  · intro r hr
    cases hop:row.op <;> simp [rowEnd,advanced,stored,computed,arithmeticState,dispatch,rightValue,leftValue,rightState,
      rightPointer,leftState,leftPointer,tagState,pointer,rawPointer,entered,writeNat,writeScalar,next,hop,
      Function.update_of_ne (show r≠1 by omega),Function.update_of_ne (show r≠4 by omega),
      Function.update_of_ne (show r≠5 by omega),Function.update_of_ne (show r≠6 by omega),
      Function.update_of_ne (show r≠7 by omega),Function.update_of_ne (show r≠8 by omega),
      Function.update_of_ne (show r≠9 by omega)]
  · intro r hr
    cases hop:row.op <;> simp [rowEnd,advanced,stored,computed,arithmeticState,dispatch,rightValue,leftValue,rightState,
      rightPointer,leftState,leftPointer,tagState,pointer,rawPointer,entered,writeNat,writeScalar,next,hop,
      Function.update_of_ne (show r≠0 by omega),Function.update_of_ne (show r≠1 by omega),Function.update_of_ne (show r≠2 by omega)]

theorem initialized_frame (s:State) : Frame s (initialized s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
  intro r hr
  simp [initialized,writeNat,next,Function.update_of_ne (show r≠1 by omega),
    Function.update_of_ne (show r≠2 by omega),Function.update_of_ne (show r≠3 by omega)]

def Outside (a k:ℕ) (heap:ℕ→Option Scalar) (s:State) : Prop :=
  ∀i,(i < a ∨ a+k ≤ i)→s.scalarHeap i=heap i

theorem ValidSchedule.frame {rows:List Row} {s u:State} (h:ValidSchedule rows s u) : Frame s u := by
  induction h with
  | nil s => exact .refl s
  | @cons row rows s u a b v hr _ ih => exact (row_full_frame row s a b v).trans ih

theorem ValidSchedule.outside {rows:List Row} {s u:State} (h:ValidSchedule rows s u) :
    Outside (s.natReg 9) rows.length s.scalarHeap u := by
  induction h with
  | nil s => intro i hi;rfl
  | @cons row rows s u a b v hr _ ih =>
    intro i hi
    have hf:=row_frame row s a b v
    have h9: (rowEnd row s a b v).natReg 9=s.natReg 9+1:=hf.2.2.2.2.2.1
    have he:(rowEnd row s a b v).scalarHeap=Function.update s.scalarHeap (s.natReg 9) (some v):=hf.2.2.2.2.2.2.2.1
    have hi':i < (rowEnd row s a b v).natReg 9 ∨ (rowEnd row s a b v).natReg 9+rows.length ≤ i:=by
      simp only [List.length_cons] at hi;rw [h9];omega
    rw [ih i hi',he,Function.update_of_ne (show i≠s.natReg 9 by simp only [List.length_cons] at hi;omega)]

/-- Generic bounded execution accepts local operand/guard certificates, never
an uncounted linear action. Its FFT specialization constructs those certificates. -/
theorem interpreted_schedule_frame (n:ℕ) (x:Fin n→ℂ) (rows:List Row) (a d B:ℕ)
    (s u:State) (hB:d+4*rows.length+a+42≤B) (hp:s.pc=0) (hk:s.natReg 0=rows.length)
    (ha:s.natReg 9=a) (hd:s.natReg 137=d) (hs:WordBound B s)
    (valid:ValidSchedule rows (initialized s) u) :
    BoundedExecution program n x B s (totalCost rows+5) {u with pc:=31} ∧
    totalCost rows+5≤22*rows.length+5 ∧ Frame s {u with pc:=31} ∧ Outside a rows.length s.scalarHeap u := by
  have hrun:=interpreted_schedule n x rows a d B s u hB hp hk ha hd hs valid
  refine ⟨hrun.1,hrun.2.1,(initialized_frame s).trans valid.frame,?_⟩
  have hout:=valid.outside
  simpa [initialized,writeNat,next,ha] using hout



namespace FFT
open UniformRadixTwoDAG
open UniformRadixTwoMachine (prepBase coefficientAddress row dataScalar preparedScalar leftScalar rightScalar)
open OAI.ExactFourier

def shiftedRow (k A:ℕ) (j:Fin (count k)) : Row := UniformRadixRowTableMachine.shiftRow A (row k j)
def rows (k A:ℕ) : List Row := (List.finRange (count k)).map (shiftedRow k A)

@[simp] theorem rows_length (k A:ℕ) : (rows k A).length=count k := by simp [rows]

/-- Exactly the row-printer and scalar-bank producer postconditions. No final
FFT action or valid schedule is an entry field. -/
structure Entry (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) : Prop where
  pc:s.pc=0
  count:s.natReg 0=UniformRadixTwoDAG.count k
  destination:s.natReg 9=A+width k
  tableBase:s.natReg 137=d
  table:∀j:Fin (UniformRadixTwoDAG.count k),
    s.natHeap (d+3*j.val)=some (opcode (shiftedRow k A j).op) ∧
    s.natHeap (d+3*j.val+1)=some (shiftedRow k A j).left ∧
    s.natHeap (d+3*j.val+2)=some (shiftedRow k A j).right
  input:∀i:Fin (width k),s.scalarHeap (A+i.val)=some (dataScalar (x i))
  powers:∀c:Fin (width k),s.scalarHeap (A+coefficientAddress k c.val)=some (preparedScalar (omega^c.val))

structure Frontier (k A d t:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) : Prop where
  pc:s.pc=3
  count:s.natReg 0=UniformRadixTwoDAG.count k
  index:s.natReg 1=t
  one:s.natReg 2=1
  three:s.natReg 3=3
  destination:s.natReg 9=A+width k+t
  tableBase:s.natReg 137=d
  table:∀j:Fin (UniformRadixTwoDAG.count k),
    s.natHeap (d+3*j.val)=some (opcode (shiftedRow k A j).op) ∧
    s.natHeap (d+3*j.val+1)=some (shiftedRow k A j).left ∧
    s.natHeap (d+3*j.val+2)=some (shiftedRow k A j).right
  data:∀i,i<width k+t→s.scalarHeap (A+i)=some (dataScalar (natValues k omega x i))
  powers:∀c:Fin (width k),s.scalarHeap (A+coefficientAddress k c.val)=some (preparedScalar (preparedBank k omega c.val))

theorem initialized_frontier (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State)
    (h:Entry k A d omega x s) : Frontier k A d 0 omega x (initialized s) := by
  constructor
  · simp [initialized,writeNat,next,h.pc]
  · simpa [initialized,writeNat,next] using h.count
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simpa [initialized,writeNat,next] using h.destination
  · simpa [initialized,writeNat,next] using h.tableBase
  · exact h.table
  · intro i hi
    have hd:=h.input ⟨i,by omega⟩
    change s.scalarHeap (A+i)=some (dataScalar (natValues k omega x i))
    rw [show natValues k omega x i=x ⟨i,by omega⟩ from natValues_input k omega x ⟨i,by omega⟩]
    exact hd
  · intro c
    simpa [initialized,writeNat,next,preparedBank_eq k omega c.val c.isLt] using h.powers c

theorem row_ready (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (j:Fin (count k)) (s:State)
    (h:Frontier k A d j.val omega x s) : Ready (shiftedRow k A j) s
      (leftScalar k omega x (instruction k j)) (rightScalar k omega x (instruction k j))
      (dataScalar (natValues k omega x (width k+j.val))) := by
  refine ⟨h.pc,by rw [h.index,h.count];exact j.isLt,h.one,h.three,?_,?_,?_,?_,?_,?_⟩
  · simpa [h.index,h.tableBase] using (h.table j).1
  · simpa [h.index,h.tableBase] using (h.table j).2.1
  · simpa [h.index,h.tableBase] using (h.table j).2.2
  · have hbefore (r:ℕ) (hr:r∈(instruction k j).refs) : r < width k+j.val:=printed_refs_before k j r hr
    have hscalar:=instruction_scalar_bound k j
    cases hg:instruction k j with
    | add a b => simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
    | sub a b => simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
    | scale c a =>
      have hc:c<width k:=hscalar c (by simp [hg,Op.scalars])
      simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar] using h.powers ⟨c,hc⟩
  · have hbefore (r:ℕ) (hr:r∈(instruction k j).refs) : r < width k+j.val:=printed_refs_before k j r hr
    cases hg:instruction k j with
    | add a b => simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data b (hbefore b (by simp [hg,Op.refs]))
    | sub a b => simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data b (hbefore b (by simp [hg,Op.refs]))
    | scale c a => simpa [shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
  · change evalField (row k j).op _ _=_
    rw [printed_gate]
    exact UniformRadixTwoMachine.eval_row k omega x _

def advance (k A:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (j:Fin (count k)) (s:State) : State :=
  rowEnd (shiftedRow k A j) s (leftScalar k omega x (instruction k j))
    (rightScalar k omega x (instruction k j)) (dataScalar (natValues k omega x (width k+j.val)))

theorem advance_frontier (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (j:Fin (count k)) (s:State)
    (h:Frontier k A d j.val omega x s) : Frontier k A d (j.val+1) omega x (advance k A omega x j s) := by
  obtain ⟨hp,h0,hj,h2,h3,h9,hn,hheap,_,_⟩:=row_frame (shiftedRow k A j) s
    (leftScalar k omega x (instruction k j)) (rightScalar k omega x (instruction k j))
    (dataScalar (natValues k omega x (width k+j.val)))
  have hf:=row_full_frame (shiftedRow k A j) s (leftScalar k omega x (instruction k j))
    (rightScalar k omega x (instruction k j)) (dataScalar (natValues k omega x (width k+j.val)))
  change Frontier k A d (j.val+1) omega x (rowEnd _ s _ _ _)
  constructor
  · exact hp
  · exact h0.trans h.count
  · rw [hj,h.index]
  · exact h2.trans h.one
  · exact h3.trans h.three
  · rw [h9,h.destination];omega
  · exact (hf.2.2.2.1 137 (by omega)).trans h.tableBase
  · simpa [hn] using h.table
  · intro i hi
    rw [hheap,h.destination]
    by_cases he:i=width k+j.val
    · subst i;simp [Nat.add_assoc]
    · rw [Function.update_of_ne (by omega)]
      exact h.data i (by omega)
  · intro c
    rw [hheap,h.destination]
    have hb:=UniformRadixTwoMachine.coefficientAddress_ge k c.val
    have hjb:=j.isLt
    rw [Function.update_of_ne (show A+coefficientAddress k c.val≠A+width k+j.val by unfold prepBase at hb;omega)]
    exact h.powers c

def rowsFrom (k A t l:ℕ) (h:t+l≤count k) : List Row :=
  List.ofFn (fun j:Fin l=>shiftedRow k A ⟨t+j.val,by omega⟩)

theorem rowsFrom_succ (k A t l:ℕ) (h:t+(l+1)≤count k) :
    rowsFrom k A t (l+1) h=shiftedRow k A ⟨t,by omega⟩::rowsFrom k A (t+1) l (by omega) := by
  unfold rowsFrom;rw [List.ofFn_succ]
  congr 1;apply congrArg List.ofFn;funext j;apply congrArg (shiftedRow k A);apply Fin.ext
  simp only [Fin.val_succ];omega

def finish (k A:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) :
    (l t:ℕ)→t+l≤count k→State→State
  | 0,_,_,s=>s
  | l+1,t,h,s=>finish k A omega x l (t+1) (by omega) (advance k A omega x ⟨t,by omega⟩ s)

theorem finish_valid (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (l t:ℕ) (hlt:t+l≤count k)
    (s:State) (h:Frontier k A d t omega x s) :
    ValidSchedule (rowsFrom k A t l hlt) s (finish k A omega x l t hlt s) ∧
    Frontier k A d (t+l) omega x (finish k A omega x l t hlt s) := by
  induction l generalizing t s with
  | zero => exact ⟨.nil s,h⟩
  | succ l ih =>
    let j:Fin (count k):=⟨t,by omega⟩
    have hr:=row_ready k A d omega x j s h
    have hf:=advance_frontier k A d omega x j s h
    have hi:=ih (t+1) (by omega) (advance k A omega x j s) hf
    rw [rowsFrom_succ]
    exact ⟨.cons hr hi.1,by simpa [finish,j,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi.2⟩

def finalState (k A:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) : State :=
  finish k A omega x (count k) 0 (by omega) (initialized s)

theorem compiled_schedule (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) (h:Entry k A d omega x s) :
    ValidSchedule (rows k A) (initialized s) (finalState k A omega x s) ∧
    Frontier k A d (count k) omega x (finalState k A omega x s) := by
  have hv:=finish_valid k A d omega x (count k) 0 (by omega) (initialized s) (initialized_frontier k A d omega x s h)
  have he:rowsFrom k A 0 (count k) (by omega)=rows k A:=by simp [rowsFrom,rows,List.ofFn_eq_map]
  simpa only [he,Nat.zero_add,finalState] using hv

def Values (k A:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) : Prop :=
  ∀r:Ref k,s.scalarHeap (A+refNat r)=some (dataScalar (values k omega x r))
def Outputs (k A:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) : Prop :=
  ∀i:Fin (width k),s.scalarHeap (A+count k+i.val)=some (dataScalar (run k omega x i))

theorem final_values (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) (h:Entry k A d omega x s) :
    Values k A omega x (finalState k A omega x s) := by
  intro r
  have hv:=(compiled_schedule k A d omega x s h).2.data (refNat r) (refNat_bound r)
  simpa [natValues_ref] using hv

theorem final_outputs (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) (h:Entry k A d omega x s) :
    Outputs k A omega x (finalState k A omega x s) := by
  intro i
  have hv:=final_values k A d omega x s h (output k i)
  have hr:run k omega x i=values k omega x (output k i):=
    (runPrefix_correct k omega x (count k) (le_refl _) _ (refNat_bound (output k i))).trans (natValues_ref k omega x (output k i))
  simpa [UniformRadixTwoMachine.output_address,hr,Nat.add_assoc] using hv

/-- Actual offset execution of the printed radix-two topology. The certificate
contains localized producer/input facts, not an FFT action or valid schedule. -/
theorem bounded_execution (k A d:ℕ) (omega:ℂ) (x:Fin (width k)→ℂ) (s:State) (B:ℕ)
    (h:Entry k A d omega x s) (hB:d+4*count k+(A+width k)+42≤B) (hs:WordBound B s) :
    BoundedExecution program (width k) x B s (totalCost (rows k A)+5) {finalState k A omega x s with pc:=31} ∧
    totalCost (rows k A)+5≤22*count k+5 ∧ Frame s {finalState k A omega x s with pc:=31} ∧
    Outside (A+width k) (count k) s.scalarHeap (finalState k A omega x s) ∧
    Values k A omega x (finalState k A omega x s) ∧ Outputs k A omega x (finalState k A omega x s) := by
  have hi:=interpreted_schedule_frame (width k) x (rows k A) (A+width k) d B s (finalState k A omega x s)
    (by simpa using hB) h.pc (by simpa using h.count) h.destination h.tableBase hs (compiled_schedule k A d omega x s h).1
  exact ⟨hi.1,by simpa using hi.2.1,hi.2.2.1,by simpa using hi.2.2.2,final_values k A d omega x s h,final_outputs k A d omega x s h⟩

theorem specified_outputs (k A d:ℕ) (x:Fin (width k)→ℂ) (s:State) (h:Entry k A d (zeta (width k)) x s) :
    ∀i:Fin (width k),(finalState k A (zeta (width k)) x s).scalarHeap (A+count k+i.val)=
      some (dataScalar ((fourierMatrix (width k)).mulVec x i)) := by
  simpa [Outputs,run_specified] using final_outputs k A d (zeta (width k)) x s h

/-- Direct producer links, retaining the literal shifted row syntax. -/
theorem table_of_printer (k A d:ℕ) (s:State) (h:UniformRadixRowTableMachine.Printed k d A (count k) s) :
    ∀j:Fin (count k),s.natHeap (d+3*j.val)=some (opcode (shiftedRow k A j).op) ∧
    s.natHeap (d+3*j.val+1)=some (shiftedRow k A j).left ∧ s.natHeap (d+3*j.val+2)=some (shiftedRow k A j).right :=
  fun j=>h j j.isLt

theorem powers_of_bank (k A:ℕ) (omega:ℂ) (s:State)
    (h:UniformRadixPowerBankMachine.Bank (width k) (A+prepBase k) omega s) :
    ∀c:Fin (width k),s.scalarHeap (A+coefficientAddress k c.val)=some (preparedScalar (omega^c.val)) := by
  intro c
  have hv:=h c.val c.isLt
  rw [UniformRadixPowerBankMachine.coefficientAddress_eq k c.val c.isLt]
  simpa [Nat.add_assoc,UniformRadixPowerBankMachine.prepared,preparedScalar] using hv


/-- This interpreter's local allocation fits logarithmically many bits in the
FFT width. Existing unrelated state must still fit the SAME ambient bound. -/
theorem envelope_power (k A d:ℕ) : d+4*count k+(A+width k)+42≤A+d+2^(2*k+8) := by
  have hp:=UniformRadixTwoMachine.memoryBound_power k
  unfold UniformRadixTwoMachine.memoryBound at hp;omega

/-- Actual specified Fourier values in the resulting physical heap, with no
input schedule or action certificate. Output emission remains a separate loop. -/
theorem specified_execution (k A d:ℕ) (x:Fin (width k)→ℂ) (s:State) (B:ℕ)
    (h:Entry k A d (zeta (width k)) x s) (hB:d+4*count k+(A+width k)+42≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program (width k) x B s t u ∧ t≤22*count k+5 ∧ Frame s u ∧
    Outside (A+width k) (count k) s.scalarHeap u ∧
    (∀i:Fin (width k),u.scalarHeap (A+count k+i.val)=some (dataScalar ((fourierMatrix (width k)).mulVec x i))) := by
  have hr:=bounded_execution k A d (zeta (width k)) x s B h hB hs
  exact ⟨{finalState k A (zeta (width k)) x s with pc:=31},_,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,
    specified_outputs k A d x s h⟩

end FFT


namespace TaggedFFT
open UniformRadixTwoDAG
open UniformRadixTwoMachine (prepBase coefficientAddress row preparedScalar)
open OAI.ExactFourier

def dependencyEval : Op ℕ→(ℕ→Bool)→Bool
  | .add a b,f=>f a || f b
  | .sub a b,f=>f a || f b
  | .scale _ a,f=>f a

theorem dependencyEval_congr (op:Op ℕ) (f g:ℕ→Bool) (h:∀r,r∈op.refs→f r=g r) :
    dependencyEval op f=dependencyEval op g := by
  cases op with
  | add a b => simp [dependencyEval,h a (by simp [Op.refs]),h b (by simp [Op.refs])]
  | sub a b => simp [dependencyEval,h a (by simp [Op.refs]),h b (by simp [Op.refs])]
  | scale c a => exact h a (by simp [Op.refs])

/-- The exact dependency-bit recurrence of the actual printed gates. Prepared
scales preserve the source bit; add/sub use the machine's conservative OR. -/
def dependencyPrefix (k:ℕ) (input:Fin (width k)→Bool) : (t:ℕ)→t≤count k→ℕ→Bool
  | 0,_=>fun r=>if h:r<width k then input ⟨r,h⟩ else false
  | t+1,h=>
    let old:=dependencyPrefix k input t (by omega)
    Function.update old (width k+t) (dependencyEval (instruction k ⟨t,by omega⟩) old)

theorem dependencyPrefix_stable (k:ℕ) (input:Fin (width k)→Bool) (t:ℕ) (ht:t≤count k)
    (u:ℕ) (hu:u≤t) (r:ℕ) (hr:r<width k+u) :
    dependencyPrefix k input t ht r=dependencyPrefix k input u (hu.trans ht) r := by
  induction t generalizing u with
  | zero =>
    have he:u=0:=by omega
    subst u
    rfl
  | succ t ih =>
    by_cases he:u=t+1
    · subst u;rfl
    · have hut:u≤t:=by omega
      rw [dependencyPrefix,Function.update_of_ne (by omega)]
      exact ih (by omega) u hut hr

def dependencyValue (k:ℕ) (input:Fin (width k)→Bool) : ℕ→Bool :=
  dependencyPrefix k input (count k) le_rfl

theorem dependencyValue_input (k:ℕ) (input:Fin (width k)→Bool) (i:Fin (width k)) :
    dependencyValue k input i.val=input i := by
  rw [dependencyValue,dependencyPrefix_stable k input (count k) le_rfl 0 (by omega) i.val (by simp)]
  simp [dependencyPrefix,i.isLt]

theorem dependencyValue_gate (k:ℕ) (input:Fin (width k)→Bool) (j:Fin (count k)) :
    dependencyValue k input (width k+j.val)=dependencyEval (instruction k j) (dependencyValue k input) := by
  have hs:=dependencyPrefix_stable k input (count k) le_rfl (j.val+1) (by omega) (width k+j.val) (by omega)
  unfold dependencyValue
  rw [hs,dependencyPrefix,Function.update_self]
  apply dependencyEval_congr
  intro r hr
  exact (dependencyPrefix_stable k input (count k) le_rfl j.val (by omega) r (printed_refs_before k j r hr)).symm

theorem dependencyPrefix_prepared (k:ℕ) (input:Fin (width k)→Bool) (hi:∀i,input i=false)
    (t:ℕ) (ht:t≤count k) (r:ℕ) : dependencyPrefix k input t ht r=false := by
  induction t generalizing r with
  | zero => simp [dependencyPrefix,hi]
  | succ t ih =>
    rw [dependencyPrefix]
    by_cases he:r=width k+t
    · subst r;rw [Function.update_self]
      cases instruction k ⟨t,by omega⟩ <;> simp [dependencyEval,ih (by omega)]
    · rw [Function.update_of_ne he];exact ih (by omega) r

theorem dependencyValue_prepared (k:ℕ) (input:Fin (width k)→Bool) (hi:∀i,input i=false) (r:ℕ) :
    dependencyValue k input r=false:=dependencyPrefix_prepared k input hi (count k) le_rfl r

/-- Numerical values and dependency bits are tracked separately and then
recombined into the actual machine Scalar. No value equality retags a cell. -/
def scalarValue (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (r:ℕ) : Scalar :=
  ⟨natValues k omega (fun i=>(input i).value) r,dependencyValue k (fun i=>(input i).dependent) r⟩

theorem scalar_ext {a b:Scalar} (hv:a.value=b.value) (hd:a.dependent=b.dependent) : a=b := by
  cases a;cases b;cases hv;cases hd;rfl

theorem scalarValue_input (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (i:Fin (width k)) :
    scalarValue k omega input i.val=input i := by
  apply scalar_ext
  · exact natValues_input k omega (fun i=>(input i).value) i
  · exact dependencyValue_input k (fun i=>(input i).dependent) i

def leftScalar (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) : Op ℕ→Scalar
  | .add a _ | .sub a _=>scalarValue k omega input a
  | .scale c _=>preparedScalar (preparedBank k omega c)
def rightScalar (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) : Op ℕ→Scalar
  | .add _ b | .sub _ b=>scalarValue k omega input b
  | .scale _ a=>scalarValue k omega input a

theorem eval_row (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (j:Fin (count k)) :
    evalField (row k j).op (leftScalar k omega input (instruction k j))
      (rightScalar k omega input (instruction k j))=some (scalarValue k omega input (width k+j.val)) := by
  have hn:=printed_gate k omega (fun i=>(input i).value) j
  have hd:=dependencyValue_gate k (fun i=>(input i).dependent) j
  cases hg:instruction k j <;> simp [row,UniformRadixTwoMachine.rowOf,hg,leftScalar,rightScalar,
    scalarValue,preparedScalar,evalField,Op.evalBank,dependencyEval] at hn hd ⊢
  all_goals exact ⟨hn.symm,hd.symm⟩


abbrev shiftedRow := FFT.shiftedRow
abbrev rows := FFT.rows
@[simp] theorem rows_length (k A:ℕ) : (rows k A).length=count k:=FFT.rows_length k A

structure Entry (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) : Prop where
  pc:s.pc=0
  count:s.natReg 0=UniformRadixTwoDAG.count k
  destination:s.natReg 9=A+width k
  tableBase:s.natReg 137=d
  table:∀j:Fin (UniformRadixTwoDAG.count k),
    s.natHeap (d+3*j.val)=some (opcode (shiftedRow k A j).op) ∧
    s.natHeap (d+3*j.val+1)=some (shiftedRow k A j).left ∧
    s.natHeap (d+3*j.val+2)=some (shiftedRow k A j).right
  input:∀i:Fin (width k),s.scalarHeap (A+i.val)=some (input i)
  powers:∀c:Fin (width k),s.scalarHeap (A+coefficientAddress k c.val)=some (preparedScalar (omega^c.val))

structure Frontier (k A d t:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) : Prop where
  pc:s.pc=3
  count:s.natReg 0=UniformRadixTwoDAG.count k
  index:s.natReg 1=t
  one:s.natReg 2=1
  three:s.natReg 3=3
  destination:s.natReg 9=A+width k+t
  tableBase:s.natReg 137=d
  table:∀j:Fin (UniformRadixTwoDAG.count k),
    s.natHeap (d+3*j.val)=some (opcode (shiftedRow k A j).op) ∧
    s.natHeap (d+3*j.val+1)=some (shiftedRow k A j).left ∧
    s.natHeap (d+3*j.val+2)=some (shiftedRow k A j).right
  data:∀i,i<width k+t→s.scalarHeap (A+i)=some (scalarValue k omega input i)
  powers:∀c:Fin (width k),s.scalarHeap (A+coefficientAddress k c.val)=some (preparedScalar (preparedBank k omega c.val))

theorem initialized_frontier (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State)
    (h:Entry k A d omega input s) : Frontier k A d 0 omega input (initialized s) := by
  constructor
  · simp [initialized,writeNat,next,h.pc]
  · simpa [initialized,writeNat,next] using h.count
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simpa [initialized,writeNat,next] using h.destination
  · simpa [initialized,writeNat,next] using h.tableBase
  · exact h.table
  · intro i hi
    have hd:=h.input ⟨i,by omega⟩
    change s.scalarHeap (A+i)=some (scalarValue k omega input i)
    rw [scalarValue_input k omega input ⟨i,by omega⟩]
    exact hd
  · intro c
    simpa [initialized,writeNat,next,preparedBank_eq k omega c.val c.isLt] using h.powers c

theorem row_ready (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (j:Fin (count k)) (s:State)
    (h:Frontier k A d j.val omega input s) : Ready (shiftedRow k A j) s
      (leftScalar k omega input (instruction k j)) (rightScalar k omega input (instruction k j))
      (scalarValue k omega input (width k+j.val)) := by
  refine ⟨h.pc,by rw [h.index,h.count];exact j.isLt,h.one,h.three,?_,?_,?_,?_,?_,?_⟩
  · simpa [h.index,h.tableBase] using (h.table j).1
  · simpa [h.index,h.tableBase] using (h.table j).2.1
  · simpa [h.index,h.tableBase] using (h.table j).2.2
  · have hbefore (r:ℕ) (hr:r∈(instruction k j).refs) : r < width k+j.val:=printed_refs_before k j r hr
    have hscalar:=instruction_scalar_bound k j
    cases hg:instruction k j with
    | add a b => simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
    | sub a b => simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
    | scale c a =>
      have hc:c<width k:=hscalar c (by simp [hg,Op.scalars])
      simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,leftScalar] using h.powers ⟨c,hc⟩
  · have hbefore (r:ℕ) (hr:r∈(instruction k j).refs) : r < width k+j.val:=printed_refs_before k j r hr
    cases hg:instruction k j with
    | add a b => simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data b (hbefore b (by simp [hg,Op.refs]))
    | sub a b => simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data b (hbefore b (by simp [hg,Op.refs]))
    | scale c a => simpa [shiftedRow,FFT.shiftedRow,UniformRadixRowTableMachine.shiftRow,row,UniformRadixTwoMachine.rowOf,hg,rightScalar]
        using h.data a (hbefore a (by simp [hg,Op.refs]))
  · change evalField (row k j).op _ _=_
    exact eval_row k omega input j

def advance (k A:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (j:Fin (count k)) (s:State) : State :=
  rowEnd (shiftedRow k A j) s (leftScalar k omega input (instruction k j))
    (rightScalar k omega input (instruction k j)) (scalarValue k omega input (width k+j.val))

theorem advance_frontier (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (j:Fin (count k)) (s:State)
    (h:Frontier k A d j.val omega input s) : Frontier k A d (j.val+1) omega input (advance k A omega input j s) := by
  obtain ⟨hp,h0,hj,h2,h3,h9,hn,hheap,_,_⟩:=row_frame (shiftedRow k A j) s
    (leftScalar k omega input (instruction k j)) (rightScalar k omega input (instruction k j))
    (scalarValue k omega input (width k+j.val))
  have hf:=row_full_frame (shiftedRow k A j) s (leftScalar k omega input (instruction k j))
    (rightScalar k omega input (instruction k j)) (scalarValue k omega input (width k+j.val))
  change Frontier k A d (j.val+1) omega input (rowEnd _ s _ _ _)
  constructor
  · exact hp
  · exact h0.trans h.count
  · rw [hj,h.index]
  · exact h2.trans h.one
  · exact h3.trans h.three
  · rw [h9,h.destination];omega
  · exact (hf.2.2.2.1 137 (by omega)).trans h.tableBase
  · simpa [hn] using h.table
  · intro i hi
    rw [hheap,h.destination]
    by_cases he:i=width k+j.val
    · subst i;simp [Nat.add_assoc]
    · rw [Function.update_of_ne (by omega)]
      exact h.data i (by omega)
  · intro c
    rw [hheap,h.destination]
    have hb:=UniformRadixTwoMachine.coefficientAddress_ge k c.val
    have hjb:=j.isLt
    rw [Function.update_of_ne (show A+coefficientAddress k c.val≠A+width k+j.val by unfold prepBase at hb;omega)]
    exact h.powers c

def rowsFrom (k A t l:ℕ) (h:t+l≤count k) : List Row :=
  List.ofFn (fun j:Fin l=>shiftedRow k A ⟨t+j.val,by omega⟩)

theorem rowsFrom_succ (k A t l:ℕ) (h:t+(l+1)≤count k) :
    rowsFrom k A t (l+1) h=shiftedRow k A ⟨t,by omega⟩::rowsFrom k A (t+1) l (by omega) := by
  unfold rowsFrom;rw [List.ofFn_succ]
  congr 1;apply congrArg List.ofFn;funext j;apply congrArg (shiftedRow k A);apply Fin.ext
  simp only [Fin.val_succ];omega

def finish (k A:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) :
    (l t:ℕ)→t+l≤count k→State→State
  | 0,_,_,s=>s
  | l+1,t,h,s=>finish k A omega input l (t+1) (by omega) (advance k A omega input ⟨t,by omega⟩ s)

theorem finish_valid (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (l t:ℕ) (hlt:t+l≤count k)
    (s:State) (h:Frontier k A d t omega input s) :
    ValidSchedule (rowsFrom k A t l hlt) s (finish k A omega input l t hlt s) ∧
    Frontier k A d (t+l) omega input (finish k A omega input l t hlt s) := by
  induction l generalizing t s with
  | zero => exact ⟨.nil s,h⟩
  | succ l ih =>
    let j:Fin (count k):=⟨t,by omega⟩
    have hr:=row_ready k A d omega input j s h
    have hf:=advance_frontier k A d omega input j s h
    have hi:=ih (t+1) (by omega) (advance k A omega input j s) hf
    rw [rowsFrom_succ]
    exact ⟨.cons hr hi.1,by simpa [finish,j,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi.2⟩

def finalState (k A:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) : State :=
  finish k A omega input (count k) 0 (by omega) (initialized s)

theorem compiled_schedule (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) (h:Entry k A d omega input s) :
    ValidSchedule (rows k A) (initialized s) (finalState k A omega input s) ∧
    Frontier k A d (count k) omega input (finalState k A omega input s) := by
  have hv:=finish_valid k A d omega input (count k) 0 (by omega) (initialized s) (initialized_frontier k A d omega input s h)
  have he:rowsFrom k A 0 (count k) (by omega)=rows k A:=by simp [rowsFrom,rows,FFT.rows,List.ofFn_eq_map]
  simpa only [he,Nat.zero_add,finalState] using hv


def Values (k A:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) : Prop :=
  ∀r:Ref k,s.scalarHeap (A+refNat r)=some (scalarValue k omega input (refNat r))
def Outputs (k A:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) : Prop :=
  ∀i:Fin (width k),s.scalarHeap (A+count k+i.val)=some (scalarValue k omega input (count k+i.val))

theorem final_values (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) (h:Entry k A d omega input s) :
    Values k A omega input (finalState k A omega input s) := by
  intro r
  exact (compiled_schedule k A d omega input s h).2.data (refNat r) (refNat_bound r)

theorem final_outputs (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) (h:Entry k A d omega input s) :
    Outputs k A omega input (finalState k A omega input s) := by
  intro i
  have hv:=final_values k A d omega input s h (output k i)
  simpa [UniformRadixTwoMachine.output_address,Nat.add_assoc] using hv

theorem bounded_execution (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State) (B:ℕ)
    (h:Entry k A d omega input s) (hB:d+4*count k+(A+width k)+42≤B) (hs:WordBound B s) :
    BoundedExecution program (width k) (fun i=>(input i).value) B s (totalCost (rows k A)+5) {finalState k A omega input s with pc:=31} ∧
    totalCost (rows k A)+5≤22*count k+5 ∧ Frame s {finalState k A omega input s with pc:=31} ∧
    Outside (A+width k) (count k) s.scalarHeap (finalState k A omega input s) ∧
    Values k A omega input (finalState k A omega input s) ∧ Outputs k A omega input (finalState k A omega input s) := by
  have hi:=interpreted_schedule_frame (width k) (fun i=>(input i).value) (rows k A) (A+width k) d B s (finalState k A omega input s)
    (by simpa using hB) h.pc (by simpa using h.count) h.destination h.tableBase hs (compiled_schedule k A d omega input s h).1
  exact ⟨hi.1,by simpa using hi.2.1,hi.2.2.1,by simpa using hi.2.2.2,final_values k A d omega input s h,final_outputs k A d omega input s h⟩


/-- Numerical projection is the previously proved radix-two FFT, independently
of the actual conservative input flags. -/
theorem output_value (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (i:Fin (width k)) :
    (scalarValue k omega input (count k+i.val)).value=run k omega (fun i=>(input i).value) i := by
  have hr:run k omega (fun i=>(input i).value) i=
      natValues k omega (fun i=>(input i).value) (refNat (output k i)):=
    runPrefix_correct k omega (fun i=>(input i).value) (count k) le_rfl _ (refNat_bound (output k i))
  simpa only [UniformRadixTwoMachine.output_address,scalarValue] using hr.symm

theorem output_dependency (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (i:Fin (width k)) :
    (scalarValue k omega input (count k+i.val)).dependent=
      dependencyValue k (fun i=>(input i).dependent) (count k+i.val) := rfl

theorem output_specified_value (k:ℕ) (input:Fin (width k)→Scalar) (i:Fin (width k)) :
    (scalarValue k (zeta (width k)) input (count k+i.val)).value=
      (fourierMatrix (width k)).mulVec (fun i=>(input i).value) i := by
  rw [output_value,run_specified]

theorem output_prepared (k:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar)
    (hp:∀i,(input i).dependent=false) (i:Fin (width k)) :
    scalarValue k omega input (count k+i.val)=preparedScalar (run k omega (fun i=>(input i).value) i) := by
  apply scalar_ext
  · exact output_value k omega input i
  · exact dependencyValue_prepared k (fun i=>(input i).dependent) hp _

/-- Mixed tagged inputs, including false-tag padded zeros, execute without any
retagging. Both the exact Fourier value and exact evaluated output bit are proved. -/
theorem specified_execution (k A d:ℕ) (input:Fin (width k)→Scalar) (s:State) (B:ℕ)
    (h:Entry k A d (zeta (width k)) input s) (hB:d+4*count k+(A+width k)+42≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program (width k) (fun i=>(input i).value) B s t u ∧ t≤22*count k+5 ∧ Frame s u ∧
    Outside (A+width k) (count k) s.scalarHeap u ∧
    (∀i:Fin (width k),u.scalarHeap (A+count k+i.val)=some
      ⟨(fourierMatrix (width k)).mulVec (fun i=>(input i).value) i,
        dependencyValue k (fun i=>(input i).dependent) (count k+i.val)⟩) := by
  have hr:=bounded_execution k A d (zeta (width k)) input s B h hB hs
  refine ⟨{finalState k A (zeta (width k)) input s with pc:=31},_,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,?_⟩
  intro i
  have ho:=hr.2.2.2.2.2 i
  change _=some _ at ho ⊢
  rw [ho]
  apply congrArg some
  apply scalar_ext
  · exact output_specified_value k input i
  · rfl

/-- Kernel/spectrum FFTs on prepared scalars remain prepared. Numerical equality
alone never discharges this flag statement. -/
theorem prepared_execution (k A d:ℕ) (input:Fin (width k)→Scalar) (s:State) (B:ℕ)
    (hp:∀i,(input i).dependent=false) (h:Entry k A d (zeta (width k)) input s)
    (hB:d+4*count k+(A+width k)+42≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program (width k) (fun i=>(input i).value) B s t u ∧ t≤22*count k+5 ∧ Frame s u ∧
    Outside (A+width k) (count k) s.scalarHeap u ∧
    (∀i:Fin (width k),u.scalarHeap (A+count k+i.val)=some
      (preparedScalar ((fourierMatrix (width k)).mulVec (fun i=>(input i).value) i))) := by
  obtain ⟨u,t,hr,ht,hf,ho,hspec⟩:=specified_execution k A d input s B h hB hs
  refine ⟨u,t,hr,ht,hf,ho,?_⟩
  intro i
  rw [hspec i]
  have hd:=dependencyValue_prepared k (fun i=>(input i).dependent) hp (count k+i.val)
  simp [hd,preparedScalar]

/-- Both producers supply the exact same physical address/tag contract. -/
theorem entry_of_producers (k A d:ℕ) (omega:ℂ) (input:Fin (width k)→Scalar) (s:State)
    (hp:s.pc=0) (hc:s.natReg 0=count k) (hw:s.natReg 9=A+width k) (hd:s.natReg 137=d)
    (ht:UniformRadixRowTableMachine.Printed k d A (count k) s)
    (hi:∀i:Fin (width k),s.scalarHeap (A+i.val)=some (input i))
    (hpow:UniformRadixPowerBankMachine.Bank (width k) (A+prepBase k) omega s) : Entry k A d omega input s :=
  ⟨hp,hc,hw,hd,FFT.table_of_printer k A d s ht,hi,FFT.powers_of_bank k A omega s hpow⟩

end TaggedFFT
end
end ExactFourierCircuits.UniformOffsetLinearMachine
