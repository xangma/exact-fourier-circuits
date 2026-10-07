import UniformMachineRuns
import UniformReplayPrint

set_option autoImplicit false

namespace ExactFourierCircuits.UniformInPlaceMachine
open UniformMachine UniformReplayPrint OAI.ExactFourier

/- Register 0 supplies k. Three Nat-heap words per row contain destination,
   source and prepared coefficient addresses. Every update replaces scalarHeap
   at its destination. The program never branches on a scalar value. -/
def program : UniformMachine.Program :=
  [.natLiteral 2 1, .natLiteral 3 3, .natLiteral 1 0,
   .branchLT 1 0 4 18,
   .natBinary .mul 4 1 3, .loadNat 5 4,
   .natBinary .add 4 4 2, .loadNat 6 4,
   .natBinary .add 4 4 2, .loadNat 7 4,
   .loadScalar 0 5, .loadScalar 1 6, .loadScalar 2 7,
   .fieldBinary .mul 3 2 1, .fieldBinary .add 0 0 3,
   .storeScalar 5 0, .natBinary .add 1 1 2, .jump 3, .halt]

theorem program_length : program.length = 19 := rfl

structure Row where
  dst : ℕ
  src : ℕ
  coefficient : ℕ
  deriving DecidableEq, Repr

noncomputable section

def prepared (c : ℂ) : Scalar := ⟨c,false⟩
def product (c b : Scalar) : Scalar := ⟨c.value * b.value,b.dependent⟩
def result (a b c : Scalar) : Scalar :=
  ⟨a.value + c.value * b.value,a.dependent || b.dependent⟩

theorem prepared_mul (c b : Scalar) (hc : c.dependent = false) :
    evalField .mul c b = some (product c b) := by simp [evalField,product,hc]

theorem result_add (a b c : Scalar) :
    evalField .add a (product c b) = some (result a b c) := rfl

structure Ready (row : Row) (s : State) (a b c : Scalar) : Prop where
  pc : s.pc = 3
  index : s.natReg 1 < s.natReg 0
  one : s.natReg 2 = 1
  three : s.natReg 3 = 3
  dst : s.natHeap (3*s.natReg 1) = some row.dst
  src : s.natHeap (3*s.natReg 1+1) = some row.src
  coefficient : s.natHeap (3*s.natReg 1+2) = some row.coefficient
  dstValue : s.scalarHeap row.dst = some a
  srcValue : s.scalarHeap row.src = some b
  coefficientValue : s.scalarHeap row.coefficient = some c
  coefficientPrepared : c.dependent = false

def initialized (s : State) : State := writeNat (writeNat (writeNat s 2 1) 3 3) 1 0

def entered (s : State) : State := {s with pc := 4}
def pointer (s : State) : State := writeNat (entered s) 4 (3*s.natReg 1)
def dstState (row : Row) (s : State) : State := writeNat (pointer s) 5 row.dst
def srcPointer (row : Row) (s : State) : State := writeNat (dstState row s) 4 (3*s.natReg 1+1)
def srcState (row : Row) (s : State) : State := writeNat (srcPointer row s) 6 row.src
def coefficientPointer (row : Row) (s : State) : State := writeNat (srcState row s) 4 (3*s.natReg 1+2)
def coefficientState (row : Row) (s : State) : State := writeNat (coefficientPointer row s) 7 row.coefficient
def dstValue (row : Row) (s : State) (a : Scalar) : State := writeScalar (coefficientState row s) 0 a
def srcValue (row : Row) (s : State) (a b : Scalar) : State := writeScalar (dstValue row s a) 1 b
def coefficientValue (row : Row) (s : State) (a b c : Scalar) : State := writeScalar (srcValue row s a b) 2 c
def multiplied (row : Row) (s : State) (a b c : Scalar) : State :=
  writeScalar (coefficientValue row s a b c) 3 (product c b)
def added (row : Row) (s : State) (a b c : Scalar) : State :=
  writeScalar (multiplied row s a b c) 0 (result a b c)
def stored (row : Row) (s : State) (a b c : Scalar) : State :=
  {next (added row s a b c) with scalarHeap := Function.update s.scalarHeap row.dst (some (result a b c))}
def advanced (row : Row) (s : State) (a b c : Scalar) : State :=
  writeNat (stored row s a b c) 1 (s.natReg 1+1)
def rowEnd (row : Row) (s : State) (a b c : Scalar) : State :=
  {advanced row s a b c with pc := 3}

theorem startup_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hp : s.pc = 0) :
    Runs program n x s 3 (initialized s) := by
  refine .next (u := writeNat s 2 1) ?_ (.next (u := writeNat (writeNat s 2 1) 3 3) ?_ (.next ?_ (.refl _)))
  all_goals simp [step,program,initialized,writeNat,next,hp]

theorem row_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b c : Scalar)
    (hr : Ready row s a b c) : Runs program n x s 15 (rowEnd row s a b c) := by
  rcases hr with ⟨hp,hi,h1,h3,hd,hs,hc,ha,hb,hv,hprep⟩
  refine .next (u := entered s) ?_ (.next (u := pointer s) ?_ (.next (u := dstState row s) ?_
    (.next (u := srcPointer row s) ?_ (.next (u := srcState row s) ?_
    (.next (u := coefficientPointer row s) ?_ (.next (u := coefficientState row s) ?_
    (.next (u := dstValue row s a) ?_ (.next (u := srcValue row s a b) ?_
    (.next (u := coefficientValue row s a b c) ?_ (.next (u := multiplied row s a b c) ?_
    (.next (u := added row s a b c) ?_ (.next (u := stored row s a b c) ?_
    (.next (u := advanced row s a b c) ?_ (.next ?_ (.refl _)))))))))))))))
  all_goals simp [step,program,entered,pointer,dstState,srcPointer,srcState,coefficientPointer,
    coefficientState,dstValue,srcValue,coefficientValue,multiplied,added,stored,advanced,rowEnd,
    writeNat,writeScalar,next,evalNat,hp,hi,h1,h3,hd,hs,hc,ha,hb,hv,
    prepared_mul c b hprep,result_add,Nat.mul_comm]

theorem row_frame (row : Row) (s : State) (a b c : Scalar) :
    (rowEnd row s a b c).pc = 3 ∧
    (rowEnd row s a b c).natReg 0 = s.natReg 0 ∧
    (rowEnd row s a b c).natReg 1 = s.natReg 1+1 ∧
    (rowEnd row s a b c).natReg 2 = s.natReg 2 ∧
    (rowEnd row s a b c).natReg 3 = s.natReg 3 ∧
    (rowEnd row s a b c).natHeap = s.natHeap ∧
    (rowEnd row s a b c).scalarHeap = Function.update s.scalarHeap row.dst (some (result a b c)) ∧
    (rowEnd row s a b c).outputs = s.outputs ∧
    (rowEnd row s a b c).rootOrders = s.rootOrders := by
  simp [rowEnd,advanced,stored,added,multiplied,coefficientValue,srcValue,dstValue,
    coefficientState,coefficientPointer,srcState,srcPointer,dstState,pointer,entered,writeNat,writeScalar,next]

/-- A prepared-address producer may assign rational/signed-bank references any
    actual scalar-heap slot. No complex equality test chooses an address. -/
structure Locations (r : ℕ) where
  rational : ℚ → ℕ
  positive : Fin r → ℕ
  negative : Fin r → ℕ

def Locations.address {r : ℕ} (p : Locations r) : Coefficient r → ℕ
  | .rational q => p.rational q
  | .prepared i neg => if neg then p.negative i else p.positive i

def rowOf {r : ℕ} (p : Locations r) (code : ShearCode ℕ r) : Row :=
  ⟨code.dst,code.src,p.address code.coefficient⟩

inductive ValidSchedule {r : ℕ} (bank : Fin r → ℂ) (p : Locations r) :
    List (ShearCode ℕ r) → State → State → Prop where
  | nil (s : State) : ValidSchedule bank p [] s s
  | cons {code : ShearCode ℕ r} {codes : List (ShearCode ℕ r)} {s u : State} {a b : Scalar}
      (ready : Ready (rowOf p code) s a b (prepared (code.coefficient.eval bank)))
      (tail : ValidSchedule bank p codes
        (rowEnd (rowOf p code) s a b (prepared (code.coefficient.eval bank))) u) :
      ValidSchedule bank p (code::codes) s u

theorem ValidSchedule.runs {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u)
    (n : ℕ) (x : Fin n → ℂ) : Runs program n x s (15*codes.length) u := by
  induction h with
  | nil s => exact .refl s
  | cons hr _ ih => simpa [List.length_cons,Nat.mul_add,Nat.add_comm] using (row_runs n x _ _ _ _ _ hr).trans ih

theorem ValidSchedule.frame {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u) :
    u.natReg 0 = s.natReg 0 ∧ u.natReg 1 = s.natReg 1+codes.length ∧
    u.natReg 2 = s.natReg 2 ∧ u.natReg 3 = s.natReg 3 ∧
    u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  induction h with
  | nil s => simp
  | @cons code codes s u a b hr _ ih =>
    have f := row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))
    simpa [f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,f.2.2.2.2.2.1,
      f.2.2.2.2.2.2.2.1,f.2.2.2.2.2.2.2.2,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem ValidSchedule.pc {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u)
    (hpc : s.pc = 3) : u.pc = 3 := by
  induction h with
  | nil _ => exact hpc
  | cons _ _ ih => exact ih rfl

def heapValue (s : State) (i : ℕ) : ℂ := (s.scalarHeap i).map Scalar.value |>.getD 0

theorem row_semantics {r : ℕ} (bank : Fin r → ℂ) (p : Locations r) (code : ShearCode ℕ r)
    (s : State) (a b : Scalar)
    (hr : Ready (rowOf p code) s a b (prepared (code.coefficient.eval bank))) :
    heapValue (rowEnd (rowOf p code) s a b (prepared (code.coefficient.eval bank))) =
      (code.eval bank).act (heapValue s) := by
  funext i
  have f := (row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))).2.2.2.2.2.2.1
  simp only [heapValue]
  rw [f]
  have hdst : s.scalarHeap code.dst = some a := hr.dstValue
  have hsrc : s.scalarHeap code.src = some b := hr.srcValue
  by_cases hi : i = code.dst
  · subst i
    simp [heapValue,rowOf,result,prepared,ShearCode.eval,Shear.act,hdst,hsrc]
  · simp [heapValue,rowOf,hi,ShearCode.eval,Shear.act]

theorem ValidSchedule.semantics {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u) :
    heapValue u = runShears (codes.map (ShearCode.eval bank)) (heapValue s) := by
  induction h with
  | nil s => rfl
  | cons hr _ ih => rw [List.map_cons,runShears_cons,← row_semantics _ _ _ _ _ _ hr]; exact ih

theorem storeScalar_bound (B : ℕ) (s : State) (dst : ℕ) (v : Scalar)
    (hs : WordBound B s) (hp : s.pc+1 ≤ B) (hd : dst ≤ B) :
    WordBound B {next s with scalarHeap := Function.update s.scalarHeap dst (some v)} := by
  refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro a w hw
  by_cases ha : a = dst
  · subst a; exact hd
  · exact hs.2.2.2.1 a w (by simpa [ha] using hw)

theorem startup_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 20 ≤ B) (hp : s.pc = 0) (hs : WordBound B s) :
    BoundedRuns program n x B s 3 (initialized s) := by
  have h1 := writeNat_bound B s 2 1 hs (by omega) (by omega)
  have h2 := writeNat_bound B (writeNat s 2 1) 3 3 h1 (by simp [writeNat,next]; omega) (by omega)
  have h3 := writeNat_bound B (writeNat (writeNat s 2 1) 3 3) 1 0 h2
    (by simp [writeNat,next]; omega) (by omega)
  refine .next hs ?_ (.next h1 ?_ (.next h2 ?_ (.refl h3)))
  all_goals simp [step,program,initialized,writeNat,next,hp]

theorem row_bounded (n : ℕ) (x : Fin n → ℂ) (B k : ℕ) (row : Row) (s : State)
    (a b c : Scalar) (hr : Ready row s a b c) (hB : 3*k+20 ≤ B)
    (hk : s.natReg 0 = k) (hs : WordBound B s) :
    BoundedRuns program n x B s 15 (rowEnd row s a b c) := by
  have hindex : s.natReg 1 < k := hr.index.trans_eq hk
  have hd := (hs.2.2.1 _ _ hr.dst).2
  have hsrc := (hs.2.2.1 _ _ hr.src).2
  have hcoef := (hs.2.2.1 _ _ hr.coefficient).2
  have h0 : WordBound B (entered s) := changePC_bound B s 4 hs (by omega)
  have h1 : WordBound B (pointer s) := writeNat_bound B _ _ _ h0
    (by change 5 ≤ B; omega) (by omega)
  have h2 : WordBound B (dstState row s) := writeNat_bound B _ _ _ h1
    (by change 6 ≤ B; omega) hd
  have h3 : WordBound B (srcPointer row s) := writeNat_bound B _ _ _ h2
    (by change 7 ≤ B; omega) (by omega)
  have h4 : WordBound B (srcState row s) := writeNat_bound B _ _ _ h3
    (by change 8 ≤ B; omega) hsrc
  have h5 : WordBound B (coefficientPointer row s) := writeNat_bound B _ _ _ h4
    (by change 9 ≤ B; omega) (by omega)
  have h6 : WordBound B (coefficientState row s) := writeNat_bound B _ _ _ h5
    (by change 10 ≤ B; omega) hcoef
  have h7 : WordBound B (dstValue row s a) := writeScalar_bound B _ _ _ h6 (by change 11 ≤ B; omega)
  have h8 : WordBound B (srcValue row s a b) := writeScalar_bound B _ _ _ h7 (by change 12 ≤ B; omega)
  have h9 : WordBound B (coefficientValue row s a b c) := writeScalar_bound B _ _ _ h8 (by change 13 ≤ B; omega)
  have h10 : WordBound B (multiplied row s a b c) := writeScalar_bound B _ _ _ h9 (by change 14 ≤ B; omega)
  have h11 : WordBound B (added row s a b c) := writeScalar_bound B _ _ _ h10 (by change 15 ≤ B; omega)
  have h12 : WordBound B (stored row s a b c) := storeScalar_bound B _ _ _ h11 (by change 16 ≤ B; omega) hd
  have h13 : WordBound B (advanced row s a b c) := writeNat_bound B _ _ _ h12
    (by change 17 ≤ B; omega) (by omega)
  have hf : WordBound B (rowEnd row s a b c) := changePC_bound B _ 3 h13 (by omega)
  rcases hr with ⟨hp,hi,hOne,hThree,hD,hS,hC,hA,hBb,hV,hprep⟩
  refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_
    (.next h4 ?_ (.next h5 ?_ (.next h6 ?_ (.next h7 ?_ (.next h8 ?_
    (.next h9 ?_ (.next h10 ?_ (.next h11 ?_ (.next h12 ?_ (.next h13 ?_ (.refl hf)))))))))))))))
  all_goals simp [step,program,entered,pointer,dstState,srcPointer,srcState,coefficientPointer,
    coefficientState,dstValue,srcValue,coefficientValue,multiplied,added,stored,advanced,rowEnd,
    writeNat,writeScalar,next,evalNat,hp,hi,hOne,hThree,hD,hS,hC,hA,hBb,hV,
    prepared_mul c b hprep,result_add,Nat.mul_comm]

theorem ValidSchedule.bounded {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u)
    (n : ℕ) (x : Fin n → ℂ) (B k : ℕ) (hB : 3*k+20 ≤ B)
    (hk : s.natReg 0 = k) (hs : WordBound B s) :
    BoundedRuns program n x B s (15*codes.length) u := by
  induction h with
  | nil s => exact .refl hs
  | @cons code codes s u a b hr _ ih =>
    have hrow := row_bounded n x B k (rowOf p code) s a b _ hr hB hk hs
    have hf := row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))
    simpa [List.length_cons,Nat.mul_add,Nat.add_comm] using
      hrow.trans (ih (hf.2.1.trans hk) hrow.final_bound)

theorem exit_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 20 ≤ B) (hs : WordBound B s) (hp : s.pc = 3)
    (hi : ¬s.natReg 1 < s.natReg 0) :
    BoundedExecution program n x B s 2 {s with pc := 18} := by
  refine .next hs ?_ (.halt (changePC_bound B s 18 hs (by omega)) ?_)
  all_goals simp [step,program,hp,hi]

/-- Exactly 15 instructions per in-place row, plus three initialization
    instructions and the final branch/halt. No field/heap operation is free. -/
theorem interpreted_schedule {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s u : State)
    (hB : 3*codes.length+20 ≤ B) (hp : s.pc = 0) (hk : s.natReg 0 = codes.length)
    (hs : WordBound B s) (valid : ValidSchedule bank p codes (initialized s) u) :
    BoundedExecution program n x B s (15*codes.length+5) {u with pc := 18} ∧
    heapValue u = runShears (codes.map (ShearCode.eval bank)) (heapValue s) ∧
    u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  have hb := startup_bounded n x B s (by omega) hp hs
  have hi0 : (initialized s).natReg 0 = codes.length := by simpa [initialized,writeNat,next] using hk
  have hr := valid.bounded n x B codes.length hB hi0 hb.final_bound
  have hf := valid.frame
  have hi : u.natReg 1 = codes.length := by simpa [initialized,writeNat,next] using hf.2.1
  have hu0 : u.natReg 0 = codes.length := hf.1.trans hi0
  have hpc := valid.pc (by simp [initialized,writeNat,next,hp])
  have hex := exit_bounded n x B u (by omega) hr.final_bound hpc (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · convert hb.executes (hr.executes hex) using 1; omega
  · exact valid.semantics.trans (congrArg (runShears (codes.map (ShearCode.eval bank))) (show heapValue (initialized s) = heapValue s from rfl))
  · simpa [initialized,writeNat,next] using hf.2.2.2.2.1
  · simpa [initialized,writeNat,next] using hf.2.2.2.2.2.1
  · simpa [initialized,writeNat,next] using hf.2.2.2.2.2.2

/-- Literal integer table layout, a local postcondition of a charged producer. -/
def Table {r : ℕ} (p : Locations r) : List (ShearCode ℕ r) → ℕ → State → Prop
  | [], _, _ => True
  | code::codes, i, s =>
      s.natHeap (3*i) = some code.dst ∧ s.natHeap (3*i+1) = some code.src ∧
      s.natHeap (3*i+2) = some (p.address code.coefficient) ∧ Table p codes (i+1) s

def DataReady {r : ℕ} (codes : List (ShearCode ℕ r)) (s : State) : Prop :=
  ∀ code ∈ codes, (∃ a, s.scalarHeap code.dst = some a) ∧ (∃ b, s.scalarHeap code.src = some b)

/-- Signed references and rational coefficients are bound to the actual scalar
    heap slots. Their arithmetic preparation is a separate charged phase. -/
def CoefficientsReady {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State) : Prop :=
  ∀ code ∈ codes, s.scalarHeap (p.address code.coefficient) =
    some (prepared (code.coefficient.eval bank))

def Separated {r : ℕ} (p : Locations r) (codes : List (ShearCode ℕ r)) : Prop :=
  ∀ code ∈ codes, ∀ ref ∈ codes, code.dst ≠ p.address ref.coefficient

theorem Table.heap_congr {r : ℕ} (p : Locations r) (codes : List (ShearCode ℕ r))
    (i : ℕ) (s t : State) (h : t.natHeap = s.natHeap) : Table p codes i t ↔ Table p codes i s := by
  induction codes generalizing i with
  | nil => rfl
  | cons code codes ih => simp [Table,h,ih]

theorem initialized_table {r : ℕ} (p : Locations r) (codes : List (ShearCode ℕ r))
    (s : State) (h : Table p codes 0 s) : Table p codes 0 (initialized s) :=
  (Table.heap_congr p codes 0 s (initialized s) rfl).2 h

theorem heap_present_after_update (s t : State) (d : ℕ) (v : Scalar)
    (h : t.scalarHeap = Function.update s.scalarHeap d (some v))
    (a : ℕ) (ha : ∃ z, s.scalarHeap a = some z) : ∃ z, t.scalarHeap a = some z := by
  by_cases he : a = d
  · subst a; exact ⟨v,by simp [h]⟩
  · obtain ⟨z,hz⟩ := ha
    exact ⟨z,by simpa [h,he] using hz⟩

/-- Local table/data/coefficient facts produce the complete actual schedule.
    No semantic action or execution certificate is assumed. -/
theorem build_schedule {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State)
    (hp : s.pc = 3) (h1 : s.natReg 2 = 1) (h3 : s.natReg 3 = 3)
    (hcount : s.natReg 1 + codes.length ≤ s.natReg 0)
    (ht : Table p codes (s.natReg 1) s) (hd : DataReady codes s)
    (hc : CoefficientsReady bank p codes s) (hsep : Separated p codes) :
    ∃ u, ValidSchedule bank p codes s u := by
  induction codes generalizing s with
  | nil => exact ⟨s,.nil s⟩
  | cons code codes ih =>
    obtain ⟨hD,hS,hC,htail⟩ := ht
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hd code (by simp)
    have hcoef := hc code (by simp)
    have ready : Ready (rowOf p code) s a b (prepared (code.coefficient.eval bank)) :=
      ⟨hp,by simp only [List.length_cons] at hcount; omega,h1,h3,hD,hS,hC,ha,hb,hcoef,rfl⟩
    let t := rowEnd (rowOf p code) s a b (prepared (code.coefficient.eval bank))
    have f := row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))
    have tt : Table p codes (t.natReg 1) t := by
      rw [show t.natReg 1 = s.natReg 1+1 from f.2.2.1]
      exact (Table.heap_congr p codes _ s t f.2.2.2.2.2.1).2 htail
    have td : DataReady codes t := by
      intro q hq
      have hqold := hd q (by simp [hq])
      exact ⟨heap_present_after_update s t _ _ f.2.2.2.2.2.2.1 q.dst hqold.1,
        heap_present_after_update s t _ _ f.2.2.2.2.2.2.1 q.src hqold.2⟩
    have tc : CoefficientsReady bank p codes t := by
      intro q hq
      have hne := (hsep code (by simp) q (by simp [hq])).symm
      rw [show t.scalarHeap = Function.update s.scalarHeap code.dst
        (some (result a b (prepared (code.coefficient.eval bank)))) from f.2.2.2.2.2.2.1,
        Function.update_of_ne hne]
      exact hc q (by simp [hq])
    have ts : Separated p codes := by
      intro q hq ref href
      exact hsep q (by simp [hq]) ref (by simp [href])
    have count : t.natReg 1 + codes.length ≤ t.natReg 0 := by
      rw [show t.natReg 1 = s.natReg 1+1 from f.2.2.1,show t.natReg 0 = s.natReg 0 from f.2.1]
      simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hcount
    obtain ⟨u,hu⟩ := ih t f.1 (f.2.2.2.1.trans h1) (f.2.2.2.2.1.trans h3) count tt td tc ts
    exact ⟨u,.cons ready hu⟩

/-- The producer obligations mention only concrete table entries, initialized
    data locations and prepared coefficients; they do not assume runShears. -/
structure ProducerPost {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State) : Prop where
  table : Table p codes 0 s
  data : DataReady codes s
  coefficients : CoefficientsReady bank p codes s
  separated : Separated p codes

theorem actual_printed_execution {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 3*codes.length+20 ≤ B) (hp : s.pc = 0) (hk : s.natReg 0 = codes.length)
    (hs : WordBound B s) (post : ProducerPost bank p codes s) :
    ∃ u, BoundedExecution program n x B s (15*codes.length+5) {u with pc := 18} ∧
      heapValue u = runShears (codes.map (ShearCode.eval bank)) (heapValue s) ∧
      u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  have hdata : DataReady codes (initialized s) := post.data
  have hcoef : CoefficientsReady bank p codes (initialized s) := post.coefficients
  obtain ⟨u,hvalid⟩ := build_schedule bank p codes (initialized s)
    (by simp [initialized,writeNat,next,hp]) (by simp [initialized,writeNat,next])
    (by simp [initialized,writeNat,next]) (by simp [initialized,writeNat,next,hk])
    (by simpa [initialized,writeNat,next] using initialized_table p codes s post.table)
    hdata hcoef post.separated
  exact ⟨u,interpreted_schedule bank p codes n x B s u hB hp hk hs hvalid⟩

theorem row_source_preserved {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (code : ShearCode ℕ r) (s : State) (a b : Scalar) :
    (rowEnd (rowOf p code) s a b (prepared (code.coefficient.eval bank))).scalarHeap code.src =
      s.scalarHeap code.src := by
  rw [(row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))).2.2.2.2.2.2.1]
  exact Function.update_of_ne code.different.symm _ _

theorem row_dependency (a b c : Scalar) : (result a b c).dependent = (a.dependent || b.dependent) := rfl

theorem ValidSchedule.untouched {r : ℕ} {bank : Fin r → ℂ} {p : Locations r}
    {codes : List (ShearCode ℕ r)} {s u : State} (h : ValidSchedule bank p codes s u)
    (q : ℕ) (hq : ∀ c ∈ codes, q ≠ c.dst) : u.scalarHeap q = s.scalarHeap q := by
  induction h with
  | nil _ => rfl
  | @cons code codes s u a b hr _ ih =>
    rw [ih (by intro c hc; exact hq c (by simp [hc])),
      (row_frame (rowOf p code) s a b (prepared (code.coefficient.eval bank))).2.2.2.2.2.2.1]
    exact Function.update_of_ne (hq code (by simp)) _ _

theorem CoefficientsReady.rational {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State) (h : CoefficientsReady bank p codes s)
    (code : ShearCode ℕ r) (hc : code ∈ codes) (q : ℚ) (he : code.coefficient = .rational q) :
    s.scalarHeap (p.rational q) = some (prepared (q : ℂ)) := by
  simpa [he,Locations.address,Coefficient.eval] using h code hc

theorem CoefficientsReady.positive {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State) (h : CoefficientsReady bank p codes s)
    (code : ShearCode ℕ r) (hc : code ∈ codes) (i : Fin r) (he : code.coefficient = .prepared i false) :
    s.scalarHeap (p.positive i) = some (prepared (bank i)) := by
  simpa [he,Locations.address,Coefficient.eval] using h code hc

theorem CoefficientsReady.negative {r : ℕ} (bank : Fin r → ℂ) (p : Locations r)
    (codes : List (ShearCode ℕ r)) (s : State) (h : CoefficientsReady bank p codes s)
    (code : ShearCode ℕ r) (hc : code ∈ codes) (i : Fin r) (he : code.coefficient = .prepared i true) :
    s.scalarHeap (p.negative i) = some (prepared (-bank i)) := by
  simpa [he,Locations.address,Coefficient.eval] using h code hc

/-- Printing logical coordinates at an explicit injective integer address map.
    This is a table-production operation, not an instruction of the interpreter. -/
def mapCode {ι : Type} {r : ℕ} (e : ι ↪ ℕ) (c : ShearCode ι r) : ShearCode ℕ r :=
  ⟨e c.dst,e c.src,fun h => c.different (e.injective h),c.coefficient⟩

theorem mapCode_act {ι : Type} {r : ℕ} (bank : Fin r → ℂ) (e : ι ↪ ℕ)
    (c : ShearCode ι r) (v : ℕ → ℂ) :
    ((mapCode e c).eval bank).act v ∘ e = (c.eval bank).act (v ∘ e) := by
  classical
  funext i
  by_cases hi : i = c.dst
  · subst i; simp [mapCode,ShearCode.eval,Shear.act]
  · have he : e i ≠ e c.dst := fun h => hi (e.injective h)
    simp [mapCode,ShearCode.eval,Shear.act,hi,he]

theorem mapped_runShears {ι : Type} {r : ℕ} (bank : Fin r → ℂ) (e : ι ↪ ℕ)
    (codes : List (ShearCode ι r)) (v : ℕ → ℂ) :
    runShears ((codes.map (mapCode e)).map (ShearCode.eval bank)) v ∘ e =
      runShears (codes.map (ShearCode.eval bank)) (v ∘ e) := by
  induction codes generalizing v with
  | nil => rfl
  | cons c codes ih =>
    rw [List.map_cons,List.map_cons,runShears_cons,ih,List.map_cons,runShears_cons,mapCode_act]

theorem actual_typed_printed_execution {ι : Type} {r : ℕ} (bank : Fin r → ℂ)
    (p : Locations r) (e : ι ↪ ℕ) (codes : List (ShearCode ι r))
    (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 3*codes.length+20 ≤ B) (hp : s.pc = 0) (hk : s.natReg 0 = codes.length)
    (hs : WordBound B s) (post : ProducerPost bank p (codes.map (mapCode e)) s) :
    ∃ u, BoundedExecution program n x B s (15*codes.length+5) {u with pc := 18} ∧
      heapValue u ∘ e = runShears (codes.map (ShearCode.eval bank)) (heapValue s ∘ e) ∧
      u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  obtain ⟨u,hu,hsem,hframe⟩ := actual_printed_execution bank p (codes.map (mapCode e)) n x B s
    (by simpa using hB) hp (by simpa using hk) hs post
  refine ⟨u,by simpa using hu,?_,hframe⟩
  exact (congrArg (fun v : ℕ → ℂ => v ∘ e) hsem).trans (mapped_runShears bank e codes (heapValue s))

/-- Actual fixed interpreter execution of the printed two-pass replay, with all
    borrowed values restored. Table/coefficient production remains explicit. -/
theorem actual_replay_execution {r a k w : ℕ} (P : UniformReplayPrint.Program r a k)
    (outputs : Fin w → Fin (a+1+k)) (bank : Fin r → ℂ) (p : Locations r)
    (e : ((Fin a ⊕ Fin k) ⊕ Fin w) ↪ ℕ) (xs : Fin a → ℂ) (zs : Fin k → ℂ) (ys : Fin w → ℂ)
    (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 3*(replayCode P outputs).length+20 ≤ B) (hp : s.pc = 0)
    (hk : s.natReg 0 = (replayCode P outputs).length) (hs : WordBound B s)
    (post : ProducerPost bank p ((replayCode P outputs).map (mapCode e)) s)
    (hdata : heapValue s ∘ e = Sum.elim (Sum.elim xs zs) ys) :
    ∃ u, BoundedExecution program n x B s (15*(replayCode P outputs).length+5) {u with pc := 18} ∧
      heapValue u ∘ e = Sum.elim (Sum.elim xs zs) (fun j => ys j + (P.eval bank).eval xs (outputs j)) ∧
      15*(replayCode P outputs).length+5 ≤ 120*k+30*w+5 ∧
      u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  obtain ⟨u,hu,hsem,hframe⟩ := actual_typed_printed_execution bank p e (replayCode P outputs)
    n x B s hB hp hk hs post
  refine ⟨u,hu,?_,?_,hframe⟩
  · rw [hdata,replayCode_spec] at hsem
    exact hsem
  · have h := replayCode_length P outputs
    omega

end
end ExactFourierCircuits.UniformInPlaceMachine
