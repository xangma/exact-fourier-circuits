import UniformMachineRuns
import UniformScalarPreparation

set_option autoImplicit false

/-! A fixed bytecode interpreter for prepared arithmetic DAGs. Tables supplied
at entry contain only opcode/address integers and already prepared scalars.
Their production is a separate charged phase; this module does not assume that
phase is free or prove the complete all-length algorithm. -/
namespace ExactFourierCircuits.UniformPreparationMachine
open UniformMachine

/-- Operands are scalar-heap addresses. There is no expression-tree evaluation. -/
structure Row where
  op : FieldOp
  left : ℕ
  right : ℕ
  deriving DecidableEq

def opcode : FieldOp → ℕ
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3

/-- Nat register 0 supplies row count, register 9 the first output address.
Three Nat-heap entries per row hold opcode, left address and right address.
All scalar arithmetic uses exactly the original instruction alphabet. -/
def program : Program := [
  .natLiteral 2 1, .natLiteral 3 3, .natLiteral 1 0,
  .branchLT 1 0 4 30,
  .natBinary .mul 4 1 3, .loadNat 5 4,
  .natBinary .add 4 4 2, .loadNat 6 4,
  .natBinary .add 4 4 2, .loadNat 7 4,
  .loadScalar 0 6, .loadScalar 1 7,
  .natLiteral 8 1, .branchLT 5 8 14 16,
  .fieldBinary .add 2 0 1, .jump 26,
  .natLiteral 8 2, .branchLT 5 8 18 20,
  .fieldBinary .sub 2 0 1, .jump 26,
  .natLiteral 8 3, .branchLT 5 8 22 24,
  .fieldBinary .mul 2 0 1, .jump 26,
  .fieldBinary .div 2 0 1, .jump 26,
  .storeScalar 9 2, .natBinary .add 9 9 2,
  .natBinary .add 1 1 2, .jump 3, .halt]

def rowCost : FieldOp → ℕ
  | .add => 17 | .sub => 19 | .mul => 21 | .div => 21

theorem rowCost_bound (op : FieldOp) : rowCost op ≤ 21 := by cases op <;> decide

noncomputable section

/-- Table validity is local: a successful field instruction includes the division
certificate, and no complex equality test occurs in the program. -/
def Ready (row : Row) (s : State) (a b v : Scalar) : Prop :=
  s.pc = 3 ∧ s.natReg 1 < s.natReg 0 ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧
  s.natHeap (3 * s.natReg 1) = some (opcode row.op) ∧
  s.natHeap (3 * s.natReg 1 + 1) = some row.left ∧
  s.natHeap (3 * s.natReg 1 + 2) = some row.right ∧
  s.scalarHeap row.left = some a ∧ s.scalarHeap row.right = some b ∧
  a.dependent = false ∧ b.dependent = false ∧ evalField row.op a b = some v

def entered (s : State) : State := { s with pc := 4 }
def pointer (s : State) : State := writeNat (entered s) 4 (3 * s.natReg 1)
def tagState (row : Row) (s : State) : State := writeNat (pointer s) 5 (opcode row.op)
def leftPointer (row : Row) (s : State) : State := writeNat (tagState row s) 4 (3 * s.natReg 1 + 1)
def leftState (row : Row) (s : State) : State := writeNat (leftPointer row s) 6 row.left
def rightPointer (row : Row) (s : State) : State := writeNat (leftState row s) 4 (3 * s.natReg 1 + 2)
def rightState (row : Row) (s : State) : State := writeNat (rightPointer row s) 7 row.right
def leftValue (row : Row) (s : State) (a : Scalar) : State := writeScalar (rightState row s) 0 a
def rightValue (row : Row) (s : State) (a b : Scalar) : State := writeScalar (leftValue row s a) 1 b
def dispatch (row : Row) (s : State) (a b : Scalar) : State := writeNat (rightValue row s a b) 8 1

def arithmeticPC : FieldOp → ℕ
  | .add => 14 | .sub => 18 | .mul => 22 | .div => 24

def arithmeticState (row : Row) (s : State) (a b : Scalar) : State :=
  let z := dispatch row s a b
  match row.op with
  | .add => { z with pc := 14 }
  | .sub => { writeNat { z with pc := 16 } 8 2 with pc := 18 }
  | .mul => { writeNat { writeNat { z with pc := 16 } 8 2 with pc := 20 } 8 3 with pc := 22 }
  | .div => { writeNat { writeNat { z with pc := 16 } 8 2 with pc := 20 } 8 3 with pc := 24 }

def computed (row : Row) (s : State) (a b v : Scalar) : State :=
  { writeScalar (arithmeticState row s a b) 2 v with pc := 26 }
def stored (row : Row) (s : State) (a b v : Scalar) : State :=
  { next (computed row s a b v) with scalarHeap := Function.update s.scalarHeap (s.natReg 9) (some v) }
def advanced (row : Row) (s : State) (a b v : Scalar) : State :=
  writeNat (stored row s a b v) 9 (s.natReg 9 + 1)
def rowEnd (row : Row) (s : State) (a b v : Scalar) : State :=
  { writeNat (advanced row s a b v) 1 (s.natReg 1 + 1) with pc := 3 }

theorem prefix_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s 10 (dispatch row s a b) := by
  obtain ⟨hpc, hi, h1, h3, hop, hl, hr, ha, hb, _, _, _⟩ := hr
  refine .next (u := entered s) ?_ (.next (u := pointer s) ?_ (.next (u := tagState row s) ?_ (.next (u := leftPointer row s) ?_ (.next (u := leftState row s) ?_ (.next (u := rightPointer row s) ?_ (.next (u := rightState row s) ?_ (.next (u := leftValue row s a) ?_ (.next (u := rightValue row s a b) ?_ (.next (u := dispatch row s a b) ?_ (.refl _))))))))))
  all_goals simp [step, program, entered, pointer, tagState, leftPointer, leftState,
    rightPointer, rightState, leftValue, rightValue, dispatch, writeNat, writeScalar,
    next, hpc, hi, h1, h3, hop, hl, hr, ha, hb, evalNat, Nat.mul_comm]

theorem dispatch_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b : Scalar) :
    Runs program n x (dispatch row s a b)
      (match row.op with | .add => 1 | .sub => 3 | .mul => 5 | .div => 5)
      (arithmeticState row s a b) := by
  cases hop : row.op
  · exact .next (by simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer,
      entered, writeNat, writeScalar, next]) (.refl _)
  · refine .next (u := { dispatch row s a b with pc := 16 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 16 } 8 2) ?_
      (.next ?_ (.refl _)))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer,
      entered, writeNat, writeScalar, next]
  · refine .next (u := { dispatch row s a b with pc := 16 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 16 } 8 2) ?_
      (.next (u := { writeNat { dispatch row s a b with pc := 16 } 8 2 with pc := 20 }) ?_
      (.next (u := writeNat { writeNat { dispatch row s a b with pc := 16 } 8 2 with pc := 20 } 8 3) ?_
      (.next ?_ (.refl _)))))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer,
      entered, writeNat, writeScalar, next]
  · refine .next (u := { dispatch row s a b with pc := 16 }) ?_
      (.next (u := writeNat { dispatch row s a b with pc := 16 } 8 2) ?_
      (.next (u := { writeNat { dispatch row s a b with pc := 16 } 8 2 with pc := 20 }) ?_
      (.next (u := writeNat { writeNat { dispatch row s a b with pc := 16 } 8 2 with pc := 20 } 8 3) ?_
      (.next ?_ (.refl _)))))
    all_goals simp [step, program, arithmeticState, dispatch, opcode, hop, rightValue,
      leftValue, rightState, rightPointer, leftState, leftPointer, tagState, pointer,
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
      leftPointer, tagState, pointer, entered, writeNat, writeScalar, next,
      evalNat, hop, h1, hv, Nat.add_comm]

theorem row_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s (rowCost row.op) (rowEnd row s a b v) := by
  have h := (prefix_runs n x row s a b v hr).trans
    ((dispatch_runs n x row s a b).trans (suffix_runs n x row s a b v hr.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2))
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
    leftPointer, tagState, pointer, entered, writeNat, writeScalar, next]

/-- Register and heap operands are prepared; division cannot manufacture a
certificate or branch on a complex value. -/
theorem eval_prepared (op : FieldOp) (a b v : Scalar)
    (ha : a.dependent = false) (hb : b.dependent = false)
    (hv : evalField op a b = some v) : v.dependent = false := by
  cases op <;> simp [evalField, ha, hb] at hv
  all_goals first | (subst v; rfl) | (obtain ⟨_, rfl⟩ := hv; rfl)

def totalCost (rows : List Row) : ℕ := (rows.map (fun row => rowCost row.op)).sum

theorem totalCost_bound (rows : List Row) : totalCost rows ≤ 21 * rows.length := by
  induction rows with
  | nil => simp [totalCost]
  | cons row rows ih =>
    have h := rowCost_bound row.op
    simp only [totalCost, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- This records concrete bytecode/heap validity for a sequence, not an
uncounted circuit primitive or an assumed runtime recurrence. -/
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


def Counters (k a : ℕ) (s : State) : Prop :=
  3 ≤ s.pc ∧ s.pc ≤ 30 ∧ s.natReg 0 = k ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧
  s.natReg 1 ≤ k ∧ (4 ≤ s.pc → s.pc ≤ 28 → s.natReg 1 < k) ∧
  s.natReg 9 ≤ a + k ∧ (s.pc ≠ 28 → s.natReg 9 = a + s.natReg 1) ∧
  (5 ≤ s.pc → s.pc ≤ 6 → s.natReg 4 = 3*s.natReg 1) ∧
  (7 ≤ s.pc → s.pc ≤ 8 → s.natReg 4 = 3*s.natReg 1+1) ∧
  (s.pc = 28 → s.natReg 9 = a+s.natReg 1+1)

def Interior (k a B : ℕ) (s : State) : Prop := WordBound B s ∧ Counters k a s

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
theorem step_interior (n : ℕ) (x : Fin n → ℂ) (k a B : ℕ) (s u : State)
    (hB : 4*k+a+40 ≤ B) (hs : Interior k a B s)
    (h : step program n x s = .running u) : Interior k a B u := by
  obtain ⟨hb,hlo,hhi,hk,h1,h3,hi,hstrict,haddr,hrel,hptr1,hptr2,hplus⟩ := hs
  have hpc : s.pc+1 ≤ B := by omega
  have hscalar (dst : ℕ) (v : Scalar) := writeScalar_bound B s dst v hb hpc
  have hnat (dst value : ℕ) (hv : value ≤ B) := writeNat_bound B s dst value hb hpc hv
  have hrel' : s.pc = 28 ∨ s.natReg 9 = a+s.natReg 1 := by
    by_cases hp : s.pc = 28
    · exact Or.inl hp
    · exact Or.inr (hrel hp)
  have hstrict' : s.pc < 4 ∨ 28 < s.pc ∨ s.natReg 1 < k := by
    by_cases hlo : 4 ≤ s.pc
    · by_cases hhi : s.pc ≤ 28
      · exact Or.inr (Or.inr (hstrict hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  have hptr1' : s.pc < 5 ∨ 6 < s.pc ∨ s.natReg 4 = 3*s.natReg 1 := by
    by_cases hlo : 5 ≤ s.pc
    · by_cases hhi : s.pc ≤ 6
      · exact Or.inr (Or.inr (hptr1 hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  have hptr2' : s.pc < 7 ∨ 8 < s.pc ∨ s.natReg 4 = 3*s.natReg 1+1 := by
    by_cases hlo : 7 ≤ s.pc
    · by_cases hhi : s.pc ≤ 8
      · exact Or.inr (Or.inr (hptr2 hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  interval_cases hp : s.pc
  · by_cases he : s.natReg 1 < k
    · simp [step,program,hp,hk,he] at h; subst u
      refine ⟨changePC_bound B s 4 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,hk,he] at h; subst u
      refine ⟨changePC_bound B s 30 hb (by omega), ?_⟩
      simp [Counters]; omega
  · simp [step,program,hp,h3,evalNat] at h; subst u
    refine ⟨hnat 4 (s.natReg 1*3) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
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
      refine ⟨changePC_bound B s 14 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 16 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .add) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 26 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨hnat 8 2 (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 8
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 18 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 20 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .sub) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 26 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨hnat 8 3 (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 8
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 22 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 24 hb (by omega), ?_⟩
      simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .mul) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 26 hb (by omega), ?_⟩
    simp [Counters]; omega
  · obtain ⟨v,rfl⟩ := field_step_write (dst := 2) (left := 0) (right := 1)
      (op := .div) (by simp [program,hp]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp [Counters,writeScalar,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 26 hb (by omega), ?_⟩
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

theorem startup_bounded (n : ℕ) (x : Fin n → ℂ) (k a B : ℕ) (s : State)
    (hB : 4*k+a+40 ≤ B) (hpc : s.pc = 0) (hb : WordBound B s) :
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

theorem initialized_counters (k a : ℕ) (s : State)
    (hpc : s.pc = 0) (hk : s.natReg 0 = k) (ha : s.natReg 9 = a) :
    Counters k a (initialized s) := by
  simp [Counters,initialized,writeNat,next,hpc,hk,ha]

theorem exit_executes (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 3) (hi : s.natReg 0 ≤ s.natReg 1) :
    Executes program n x s 2 {s with pc := 30} := by
  refine .next ?_ (.halt ?_)
  · simp [step,program,hpc,Nat.not_lt.mpr hi]
  · simp [step,program]

/-- Every bytecode instruction, table load and memory write is charged.
The entry table preparation is intentionally an explicit remaining premise. -/
theorem interpreted_schedule (n : ℕ) (x : Fin n → ℂ) (rows : List Row) (a B : ℕ)
    (s u : State) (hB : 4*rows.length+a+40 ≤ B)
    (hpc : s.pc = 0) (hk : s.natReg 0 = rows.length) (ha : s.natReg 9 = a)
    (hb : WordBound B s) (valid : ValidSchedule rows (initialized s) u) :
    BoundedExecution program n x B s (totalCost rows+5) {u with pc := 30} ∧
      totalCost rows+5 ≤ 21*rows.length+5 ∧
      u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.natHeap = s.natHeap := by
  have hstart := startup_bounded n x rows.length a B s hB hpc hb
  have hc := initialized_counters rows.length a s hpc hk ha
  have hi : Interior rows.length a B (initialized s) := ⟨hstart.final_bound,hc⟩
  have hr := valid.runs n x
  have hrun := hr.bounded_of_invariant (Interior rows.length a B) hi
    (fun _ h => h.1) (fun s u h => step_interior n x rows.length a B s u hB h)
  have hufit := hrun.final_bound
  have hfinal := valid.counters
  have huc : Counters rows.length a u := by
    have hpres : ∀ s u, Interior rows.length a B s → step program n x s = .running u →
        Interior rows.length a B u := fun s u h => step_interior n x rows.length a B s u hB h
    -- Recover the same invariant from the actual segment, without assuming its end state.
    have general : ∀ {s u t}, Runs program n x s t u → Interior rows.length a B s →
        Interior rows.length a B u := by
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
  have hbexit := hex.bounded_of_invariant (Interior rows.length a B)
    ⟨hufit,huc⟩ (fun _ h => h.1)
    (fun s u h => step_interior n x rows.length a B s u hB h)
  refine ⟨?_,by have h := totalCost_bound rows; omega,?_,?_,?_⟩
  · convert hstart.executes (hrun.executes hbexit) using 1; omega
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.1
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.2
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.1

end
end ExactFourierCircuits.UniformPreparationMachine
