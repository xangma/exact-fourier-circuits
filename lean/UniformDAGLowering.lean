import UniformPreparationMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformDAGLowering
open UniformMachine UniformPreparationMachine

abbrev DProgram := UniformScalarPreparation.Program
abbrev DInstruction := UniformScalarPreparation.Instruction

/-- A leaf is copied by adding the prepared zero at address zero. Binary
    operands refer directly to prior stored results, preserving DAG sharing. -/
def lowerInstruction {r j : ℕ} (a : ℕ) : DInstruction r j → Row
  | .rational _ => ⟨.add, 1 + r + j, 0⟩
  | .root i => ⟨.add, 1 + i.val, 0⟩
  | .add l q => ⟨.add, a + l.val, a + q.val⟩
  | .sub l q => ⟨.sub, a + l.val, a + q.val⟩
  | .mul l q => ⟨.mul, a + l.val, a + q.val⟩
  | .divide l q => ⟨.div, a + l.val, a + q.val⟩

def compile {r : ℕ} : {k : ℕ} → DProgram r k → ℕ → List Row
  | 0, .nil, _ => []
  | _ + 1, .step p i, a => compile p a ++ [lowerInstruction a i]

/-- Cons accumulation avoids repeatedly copying a growing prefix. -/
def compileReverse {r : ℕ} : {k : ℕ} → DProgram r k → ℕ → List Row
  | 0, .nil, _ => []
  | _ + 1, .step p i, a => lowerInstruction a i :: compileReverse p a

def compileLinear {r k : ℕ} (p : DProgram r k) (a : ℕ) : List Row :=
  (compileReverse p a).reverse

theorem compileLinear_eq {r k : ℕ} (p : DProgram r k) (a : ℕ) :
    compileLinear p a = compile p a := by
  induction p with
  | nil => rfl
  | step p i ih =>
    change (lowerInstruction a i :: compileReverse p a).reverse = compile p a ++ [lowerInstruction a i]
    rw [List.reverse_cons]
    exact congrArg (fun rows => rows ++ [lowerInstruction a i]) ih

def bytecode : List Row → List ℕ
  | [] => []
  | row :: rows => opcode row.op :: row.left :: row.right :: bytecode rows

theorem bytecode_length (rows : List Row) : (bytecode rows).length = 3 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [bytecode, ih]; omega

theorem bytecode_get (rows : List Row) (j : ℕ) (row : Row) (h : rows[j]? = some row) :
    (bytecode rows)[3 * j]? = some (opcode row.op) ∧
    (bytecode rows)[3 * j + 1]? = some row.left ∧
    (bytecode rows)[3 * j + 2]? = some row.right := by
  induction rows generalizing j with
  | nil => simp at h
  | cons first rows ih =>
    cases j with
    | zero => simp at h; subst row; exact ⟨rfl, rfl, rfl⟩
    | succ j =>
      have ht : rows[j]? = some row := by simpa using h
      simpa [bytecode, Nat.mul_succ, Nat.add_assoc] using ih j ht

theorem compile_length {r k : ℕ} (p : DProgram r k) (a : ℕ) : (compile p a).length = k := by
  induction p with
  | nil => rfl
  | step p i ih => simp [compile, ih]

theorem compile_prefix_get {r k : ℕ} (p : DProgram r k) (i : DInstruction r k)
    (a j : ℕ) (hj : j < k) : (compile (.step p i) a)[j]? = (compile p a)[j]? := by
  exact List.getElem?_append_left (by simpa [compile_length] using hj)

theorem compile_last_get {r k : ℕ} (p : DProgram r k) (i : DInstruction r k) (a : ℕ) :
    (compile (.step p i) a)[k]? = some (lowerInstruction a i) := by
  calc
    (compile (.step p i) a)[k]? = (compile (.step p i) a)[(compile p a).length]? :=
      congrArg (fun j => (compile (.step p i) a)[j]?) (compile_length p a).symm
    _ = some (lowerInstruction a i) := List.getElem?_concat_length

noncomputable section

def NatTable (rows : List Row) (s : State) : Prop :=
  ∀ j row, rows[j]? = some row →
    s.natHeap (3 * j) = some (opcode row.op) ∧
    s.natHeap (3 * j + 1) = some row.left ∧ s.natHeap (3 * j + 2) = some row.right

theorem bytecode_natTable (rows : List Row) (s : State)
    (h : s.natHeap = fun j => (bytecode rows)[j]?) : NatTable rows s := by
  intro j row hj
  simp only [h]
  exact bytecode_get rows j row hj

def RootsReady {r : ℕ} (roots : Fin r → ℂ) (s : State) : Prop :=
  s.scalarHeap 0 = some ⟨0, false⟩ ∧
    ∀ j : Fin r, s.scalarHeap (1 + j.val) = some ⟨roots j, false⟩

def LiteralReady {r j : ℕ} (i : DInstruction r j) (s : State) : Prop :=
  match i with
  | .rational q => s.scalarHeap (1 + r + j) = some ⟨(q : ℂ), false⟩
  | _ => True

def LiteralsReady {r : ℕ} : {k : ℕ} → DProgram r k → State → Prop
  | 0, .nil, _ => True
  | _ + 1, .step p i, s => LiteralsReady p s ∧ LiteralReady i s

def BaseHeap (a : ℕ) (s u : State) : Prop := ∀ j, j < a → u.scalarHeap j = s.scalarHeap j

def Values {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ) (a : ℕ) (s : State) : Prop :=
  ∀ j : Fin k, s.scalarHeap (a + j.val) = some ⟨p.eval roots j, false⟩

def Registers (K a j : ℕ) (s : State) : Prop :=
  s.pc = 3 ∧ s.natReg 0 = K ∧ s.natReg 1 = j ∧ s.natReg 2 = 1 ∧
    s.natReg 3 = 3 ∧ s.natReg 9 = a + j

theorem schedule_append {xs ys : List Row} {s u v : State}
    (hx : ValidSchedule xs s u) (hy : ValidSchedule ys u v) : ValidSchedule (xs ++ ys) s v := by
  induction hx with
  | nil _ => exact hy
  | cons hr _ ih => exact .cons hr (ih hy)

theorem instruction_operands {r k K : ℕ} (p : DProgram r k) (i : DInstruction r k)
    (roots : Fin r → ℂ) (a : ℕ) (s u : State) (hk : k < K) (ha : r + K + 1 ≤ a)
    (hroots : RootsReady roots s) (hliteral : LiteralReady i s)
    (hbase : BaseHeap a s u) (hvalues : Values p roots a u)
    (hvalid : i.Admissible (p.eval roots)) : ∃ l q : Scalar,
    u.scalarHeap (lowerInstruction a i).left = some l ∧
    u.scalarHeap (lowerInstruction a i).right = some q ∧
    l.dependent = false ∧ q.dependent = false ∧
    evalField (lowerInstruction a i).op l q = some ⟨i.eval roots (p.eval roots), false⟩ := by
  cases i with
  | rational q =>
    refine ⟨⟨(q : ℂ), false⟩, ⟨0, false⟩, ?_, ?_, rfl, rfl, ?_⟩
    · change u.scalarHeap (1 + r + k) = _
      rw [hbase _ (by omega)]
      exact hliteral
    · change u.scalarHeap 0 = _
      rw [hbase 0 (by omega)]
      exact hroots.1
    · simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]
  | root j =>
    refine ⟨⟨roots j, false⟩, ⟨0, false⟩, ?_, ?_, rfl, rfl, ?_⟩
    · change u.scalarHeap (1 + j.val) = _
      rw [hbase _ (by omega)]
      exact hroots.2 j
    · change u.scalarHeap 0 = _
      rw [hbase 0 (by omega)]
      exact hroots.1
    · simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]
  | add l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | sub l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | mul l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | divide l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval,
        UniformScalarPreparation.Instruction.Admissible] at hvalid ⊢; exact hvalid⟩

theorem natTable_prefix {r k : ℕ} (p : DProgram r k) (i : DInstruction r k) (a : ℕ)
    (s : State) (h : NatTable (compile (.step p i) a) s) : NatTable (compile p a) s := by
  intro j row hj
  have hidx : j < k := by
    simpa [compile_length] using (List.getElem?_eq_some_iff.1 hj).choose
  apply h j row
  rw [compile_prefix_get p i a j hidx]
  exact hj

/-- Actual interpreter validity follows from the typed DAG's division
    certificates and initialized literal/root/bytecode tables. Every prior
    result is loaded from its stored address; no expression is reevaluated. -/
theorem compile_valid {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ)
    (K a : ℕ) (s : State) (hsize : k ≤ K) (ha : r + K + 1 ≤ a)
    (hregs : Registers K a 0 s) (hroots : RootsReady roots s)
    (hliterals : LiteralsReady p s) (htable : NatTable (compile p a) s)
    (hvalid : p.Admissible roots) : ∃ u : State,
    ValidSchedule (compile p a) s u ∧ Registers K a k u ∧
      Values p roots a u ∧ BaseHeap a s u := by
  induction p generalizing K a s with
  | nil =>
    refine ⟨s, .nil _, hregs, ?_, fun _ _ => rfl⟩
    intro j
    exact Fin.elim0 j
  | @step j p i ih =>
    obtain ⟨v, hv, hregv, hvalues, hbase⟩ :=
      ih K a s (by omega) ha hregs hroots hliterals.1
        (natTable_prefix p i a s htable) hvalid.1
    obtain ⟨l, q, hl, hq, hld, hqd, heval⟩ :=
      instruction_operands p i roots a s v (by omega) ha hroots hliterals.2 hbase hvalues hvalid.2
    let row := lowerInstruction a i
    let value : Scalar := ⟨i.eval roots (p.eval roots), false⟩
    let u := rowEnd row v l q value
    obtain ⟨hop, hleft, hright⟩ := htable j row (compile_last_get p i a)
    have hnatheap : v.natHeap = s.natHeap := hv.counters.2.2.2.1
    obtain ⟨hpv, hKv, hjv, honev, hthreev, hadrv⟩ := hregv
    have hready : Ready row v l q value := by
      refine ⟨hpv, ?_, honev, hthreev, ?_, ?_, ?_, hl, hq, hld, hqd, heval⟩
      · omega
      · simpa only [hjv, hnatheap] using hop
      · simpa only [hjv, hnatheap] using hleft
      · simpa only [hjv, hnatheap] using hright
    have htail : ValidSchedule [row] v u := .cons hready (.nil u)
    have hall : ValidSchedule (compile (.step p i) a) s u := by
      simpa only [compile] using schedule_append hv htail
    obtain ⟨hpcu, hKu, hju, honeu, hthreeu, hadru, _, hheap, _, _⟩ := row_frame row v l q value
    refine ⟨u, hall, ?_, ?_, ?_⟩
    · refine ⟨hpcu, hKu.trans hKv, ?_, honeu.trans honev, hthreeu.trans hthreev, ?_⟩
      · simpa only [hjv] using hju
      · simpa only [hadrv, Nat.add_assoc] using hadru
    · intro index
      refine Fin.lastCases ?_ (fun index => ?_) index
      · simp only [UniformScalarPreparation.Program.eval, Fin.snoc_last]
        change (rowEnd row v l q value).scalarHeap (a + j) = some value
        rw [hheap, hadrv, Function.update_self]
      · simp only [UniformScalarPreparation.Program.eval, Fin.snoc_castSucc, Fin.val_castSucc]
        rw [hheap, hadrv, Function.update_of_ne (by have hi := index.isLt; omega)]
        exact hvalues index
    · intro addr haddr
      rw [hheap, hadrv, Function.update_of_ne (by omega)]
      exact hbase addr haddr

theorem literals_heap_eq {r k : ℕ} (p : DProgram r k) (s u : State)
    (h : u.scalarHeap = s.scalarHeap) : LiteralsReady p u ↔ LiteralsReady p s := by
  induction p with
  | nil => rfl
  | step p i ih =>
    simp only [LiteralsReady]
    apply and_congr ih
    cases i <;> simp [LiteralReady, h]

theorem instruction_addresses {r j K : ℕ} (i : DInstruction r j) (a : ℕ)
    (hj : j < K) (ha : r + K + 1 ≤ a) :
    (lowerInstruction a i).left < a + j ∧ (lowerInstruction a i).right < a + j := by
  cases i with
  | rational _ => simp only [lowerInstruction]; omega
  | root root => have hi := root.isLt; simp only [lowerInstruction]; omega
  | add l q | sub l q | mul l q | divide l q =>
    have hl := l.isLt
    have hq := q.isLt
    simp only [lowerInstruction]; omega

theorem values_output {r o : ℕ} (d : UniformScalarPreparation.DAG r o)
    (roots : Fin r → ℂ) (valid : d.Admissible roots) (a : ℕ) (s : State)
    (h : Values d.program roots a s) (j : Fin o) :
    s.scalarHeap (a + (d.output j).val) = some ⟨d.run roots valid j, false⟩ := by
  exact h (d.output j)

/-- The actual fixed interpreter executes the compiled typed DAG in linear
    charged time. Entry tables, supplied roots and rational leaves are explicit
    initialized-heap premises, whose production remains a separate phase. -/
theorem interpreted_DAG {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ)
    (valid : p.Admissible roots) (n : ℕ) (x : Fin n → ℂ) (a B : ℕ) (s : State)
    (hspace : r + k + 1 ≤ a) (hB : 4 * k + a + 40 ≤ B) (hpc : s.pc = 0)
    (hk : s.natReg 0 = k) (ha : s.natReg 9 = a) (hb : WordBound B s)
    (hroots : RootsReady roots s) (hliterals : LiteralsReady p s)
    (htable : NatTable (compile p a) s) : ∃ u : State,
    BoundedExecution UniformPreparationMachine.program n x B s (totalCost (compile p a) + 5) u ∧
      totalCost (compile p a) + 5 ≤ 21 * k + 5 ∧ Values p roots a u ∧ BaseHeap a s u ∧
      u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.natHeap = s.natHeap := by
  have hregs : Registers k a 0 (initialized s) := by
    simp [Registers, initialized, writeNat, next, hpc, hk, ha]
  have hlit : LiteralsReady p (initialized s) :=
    (literals_heap_eq p s (initialized s) rfl).mpr hliterals
  obtain ⟨u, hschedule, _, hvalues, hbase⟩ :=
    compile_valid p roots k a (initialized s) (by rfl) hspace hregs hroots hlit htable valid
  obtain ⟨hex, hcost, hout, hroot, hnat⟩ := interpreted_schedule n x (compile p a) a B s u
    (by simpa only [compile_length] using hB) hpc
    (by simpa only [compile_length] using hk) ha hb hschedule
  exact ⟨{ u with pc := 30 }, hex, by simpa only [compile_length] using hcost,
    hvalues, hbase, hout, hroot, hnat⟩

/-- The natural packed address choice leaves roots/literals below all results. -/
theorem interpreted_DAG_packed {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ)
    (valid : p.Admissible roots) (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 5 * k + r + 41 ≤ B) (hpc : s.pc = 0) (hk : s.natReg 0 = k)
    (ha : s.natReg 9 = r + k + 1) (hb : WordBound B s)
    (hroots : RootsReady roots s) (hliterals : LiteralsReady p s)
    (htable : NatTable (compile p (r + k + 1)) s) : ∃ u : State,
    BoundedExecution UniformPreparationMachine.program n x B s
      (totalCost (compile p (r + k + 1)) + 5) u ∧
      totalCost (compile p (r + k + 1)) + 5 ≤ 21 * k + 5 ∧
      Values p roots (r + k + 1) u ∧ BaseHeap (r + k + 1) s u ∧
      u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.natHeap = s.natHeap := by
  exact interpreted_DAG p roots valid n x (r + k + 1) B s (by rfl) (by omega)
    hpc hk ha hb hroots hliterals htable

end
end ExactFourierCircuits.UniformDAGLowering
