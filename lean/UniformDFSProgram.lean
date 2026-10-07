import UniformTraversalMachine
import UniformSectorPacking

set_option autoImplicit false

namespace ExactFourierCircuits.UniformDFSProgram
open UniformMachine UniformTraversal

/- Registers 0,...,13: depth, axis count, prefix address, next digit, radix,
   radix-table base, stack base, output base, output count, 1, 2,
   pointer, temporary, 0. Two heap words per depth store parent and next digit.
   The prepared table stores radices only; no iterator or host-array operation. -/
def program : Program :=
  [.branchLT 0 1 1 15,
   .natBinary .add 11 5 0, .loadNat 4 11, .natLiteral 3 0,
   .branchLT 3 4 5 19,
   .natBinary .mul 11 0 10, .natBinary .add 11 6 11,
   .storeNat 11 2, .natBinary .add 11 11 9,
   .natBinary .add 12 3 9, .storeNat 11 12,
   .natBinary .mul 2 2 4, .natBinary .add 2 2 3,
   .natBinary .add 0 0 9, .jump 0,
   .natBinary .add 11 7 8, .storeNat 11 2,
   .natBinary .add 8 8 9, .jump 19,
   .branchLT 13 0 20 29,
   .natBinary .sub 0 0 9,
   .natBinary .mul 11 0 10, .natBinary .add 11 6 11,
   .loadNat 2 11, .natBinary .add 11 11 9, .loadNat 3 11,
   .natBinary .add 11 5 0, .loadNat 4 11, .jump 4,
   .halt]

theorem program_length : program.length = 30 := rfl

/-- Running segments compose before the one final halt. -/
inductive Runs (n : ℕ) (x : Fin n → ℂ) : State → ℕ → State → Prop where
  | refl (s : State) : Runs n x s 0 s
  | next {s u v : State} {t : ℕ} (h : step program n x s = .running u)
      (tail : Runs n x u t v) : Runs n x s (t + 1) v

namespace Runs
theorem trans {n a b : ℕ} {x : Fin n → ℂ} {s u v : State}
    (h : Runs n x s a u) (h' : Runs n x u b v) : Runs n x s (a + b) v := by
  induction h with
  | refl => simpa using h'
  | next hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next hs (ih h')

theorem finish {n a b : ℕ} {x : Fin n → ℂ} {s u v : State}
    (h : Runs n x s a u) (h' : Executes program n x u b v) :
    Executes program n x s (a + b) v := by
  induction h with
  | refl => simpa using h'
  | next hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next hs (ih h')
end Runs

inductive BoundedRuns (n : ℕ) (x : Fin n → ℂ) (B : ℕ) : State → ℕ → State → Prop where
  | refl (s : State) (h : WordBound B s) : BoundedRuns n x B s 0 s
  | next {s u v : State} {t : ℕ} (bound : WordBound B s)
      (h : step program n x s = .running u) (tail : BoundedRuns n x B u t v) :
      BoundedRuns n x B s (t + 1) v

namespace BoundedRuns
theorem runs {n B a : ℕ} {x : Fin n → ℂ} {s v : State}
    (h : BoundedRuns n x B s a v) : Runs n x s a v := by
  induction h with
  | refl s _ => exact .refl s
  | next _ hs _ ih => exact .next hs ih

theorem final_bound {n B a : ℕ} {x : Fin n → ℂ} {s v : State}
    (h : BoundedRuns n x B s a v) : WordBound B v := by
  induction h with
  | refl _ hs => exact hs
  | next _ _ _ ih => exact ih

theorem trans {n B a b : ℕ} {x : Fin n → ℂ} {s u v : State}
    (h : BoundedRuns n x B s a u) (h' : BoundedRuns n x B u b v) :
    BoundedRuns n x B s (a + b) v := by
  induction h with
  | refl => simpa using h'
  | next hb hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next hb hs (ih h')

theorem finish {n B a b : ℕ} {x : Fin n → ℂ} {s u v : State}
    (h : BoundedRuns n x B s a u) (h' : BoundedExecution program n x B u b v) :
    BoundedExecution program n x B s (a + b) v := by
  induction h with
  | refl => simpa using h'
  | next hb hs _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using BoundedExecution.next hb hs (ih h')
end BoundedRuns

def setPC (s : State) (p : ℕ) : State := {s with pc := p}
def store (s : State) (a v : ℕ) : State :=
  {next s with natHeap := Function.update s.natHeap a (some v)}
def constants (s : State) : Prop := s.natReg 9 = 1 ∧ s.natReg 10 = 2 ∧ s.natReg 13 = 0

def enter (s : State) (r : ℕ) : State :=
  writeNat (writeNat (writeNat (setPC s 1) 11 (s.natReg 5 + s.natReg 0)) 4 r) 3 0
def child1 (s : State) : State := writeNat (setPC s 5) 11 (s.natReg 0 * s.natReg 10)
def child2 (s : State) : State := writeNat (child1 s) 11 (s.natReg 6 + s.natReg 0 * s.natReg 10)
def child3 (s : State) : State := store (child2 s) (s.natReg 6 + s.natReg 0 * s.natReg 10) (s.natReg 2)
def child4 (s : State) : State := writeNat (child3 s) 11 (s.natReg 6 + s.natReg 0 * s.natReg 10 + s.natReg 9)
def child5 (s : State) : State := writeNat (child4 s) 12 (s.natReg 3 + s.natReg 9)
def child6 (s : State) : State := store (child5 s)
  (s.natReg 6 + s.natReg 0 * s.natReg 10 + s.natReg 9) (s.natReg 3 + s.natReg 9)
def child7 (s : State) : State := writeNat (child6 s) 2 (s.natReg 2 * s.natReg 4)
def child8 (s : State) : State := writeNat (child7 s) 2 (s.natReg 2 * s.natReg 4 + s.natReg 3)
def child9 (s : State) : State := writeNat (child8 s) 0 (s.natReg 0 + s.natReg 9)
def child (s : State) : State := setPC (child9 s) 0
def emit1 (s : State) : State := writeNat (setPC s 15) 11 (s.natReg 7 + s.natReg 8)
def emit2 (s : State) : State := store (emit1 s) (s.natReg 7 + s.natReg 8) (s.natReg 2)
def emit3 (s : State) : State := writeNat (emit2 s) 8 (s.natReg 8 + s.natReg 9)
def emit (s : State) : State := setPC (emit3 s) 19
def pop1 (s : State) : State := writeNat (setPC s 20) 0 (s.natReg 0 - s.natReg 9)
def pop2 (s : State) : State := writeNat (pop1 s) 11 ((s.natReg 0 - s.natReg 9) * s.natReg 10)
def pop3 (s : State) : State := writeNat (pop2 s) 11 (s.natReg 6 + (s.natReg 0 - s.natReg 9) * s.natReg 10)
def pop4 (s : State) (a : ℕ) : State := writeNat (pop3 s) 2 a
def pop5 (s : State) (a : ℕ) : State := writeNat (pop4 s a) 11
  (s.natReg 6 + (s.natReg 0 - s.natReg 9) * s.natReg 10 + s.natReg 9)
def pop6 (s : State) (a d : ℕ) : State := writeNat (pop5 s a) 3 d
def pop7 (s : State) (a d : ℕ) : State := writeNat (pop6 s a d) 11 (s.natReg 5 + (s.natReg 0 - s.natReg 9))
def pop8 (s : State) (a d r : ℕ) : State := writeNat (pop7 s a d) 4 r
def pop (s : State) (a d r : ℕ) : State := setPC (pop8 s a d r) 4

theorem enter_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 0)
    (hl : s.natReg 0 < s.natReg 1) (r : ℕ)
    (hr : s.natHeap (s.natReg 5 + s.natReg 0) = some r) : Runs n x s 4 (enter s r) := by
  refine .next (u := setPC s 1) ?_ (.next (u := writeNat (setPC s 1) 11 (s.natReg 5 + s.natReg 0)) ?_
    (.next (u := writeNat (writeNat (setPC s 1) 11 (s.natReg 5 + s.natReg 0)) 4 r) ?_
      (.next ?_ (.refl (enter s r)))))
  all_goals simp [step, program, hpc, hl, hr, enter, setPC, writeNat, next, evalNat]

theorem child_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 4)
    (hd : s.natReg 3 < s.natReg 4) : Runs n x s 11 (child s) := by
  refine .next (u := setPC s 5) ?_ (.next (u := child1 s) ?_ (.next (u := child2 s) ?_
    (.next (u := child3 s) ?_ (.next (u := child4 s) ?_ (.next (u := child5 s) ?_
      (.next (u := child6 s) ?_ (.next (u := child7 s) ?_ (.next (u := child8 s) ?_
        (.next (u := child9 s) ?_ (.next ?_ (.refl (child s))))))))))))
  all_goals simp [step, program, hpc, hd, child, child1, child2, child3, child4, child5,
    child6, child7, child8, child9, store, setPC, writeNat, next, evalNat]

theorem leaf_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 0)
    (hl : ¬s.natReg 0 < s.natReg 1) : Runs n x s 5 (emit s) := by
  refine .next (u := setPC s 15) ?_ (.next (u := emit1 s) ?_ (.next (u := emit2 s) ?_
    (.next (u := emit3 s) ?_ (.next ?_ (.refl (emit s))))))
  all_goals simp [step, program, hpc, hl, emit, emit1, emit2, emit3, store, setPC, writeNat, next, evalNat]

theorem exhausted_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 4)
    (hd : ¬s.natReg 3 < s.natReg 4) : Runs n x s 1 (setPC s 19) := by
  exact .next (by simp [step, program, hpc, hd, setPC]) (.refl _)

theorem pop_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 19)
    (hc : constants s) (hp : 0 < s.natReg 0) (a d r : ℕ)
    (ha : s.natHeap (s.natReg 6 + (s.natReg 0 - 1) * 2) = some a)
    (hd : s.natHeap (s.natReg 6 + (s.natReg 0 - 1) * 2 + 1) = some d)
    (hr : s.natHeap (s.natReg 5 + (s.natReg 0 - 1)) = some r) : Runs n x s 10 (pop s a d r) := by
  obtain ⟨h1,h2,h0⟩ := hc
  refine .next (u := setPC s 20) ?_ (.next (u := pop1 s) ?_ (.next (u := pop2 s) ?_
    (.next (u := pop3 s) ?_ (.next (u := pop4 s a) ?_ (.next (u := pop5 s a) ?_
      (.next (u := pop6 s a d) ?_ (.next (u := pop7 s a d) ?_
        (.next (u := pop8 s a d r) ?_ (.next ?_ (.refl (pop s a d r)))))))))))
  all_goals simp [step, program, hpc, hp, h1, h2, h0, ha, hd, hr, pop, pop1, pop2, pop3, pop4,
    pop5, pop6, pop7, pop8, setPC, writeNat, next, evalNat]

theorem halt_executes (n : ℕ) (x : Fin n → ℂ) (s : State) (hpc : s.pc = 19)
    (hc : constants s) (hd : s.natReg 0 = 0) : Executes program n x s 2 (setPC s 29) := by
  have h0 := hc.2.2
  refine .next (u := setPC s 29) ?_ (.halt ?_)
  all_goals simp [step, program, hpc, h0, hd, setPC]

def treeCost : List ℕ → ℕ
  | [] => 5
  | r :: rs => 5 + r * (treeCost rs + 21)
theorem treeCost_balance (rs : List ℕ) : treeCost rs + 21 = 26 * nodeCount rs := by
  induction rs with
  | nil => norm_num [treeCost, nodeCount]
  | cons r rs ih => simp only [treeCost, nodeCount]; rw [ih]; ring
theorem treeCost_bound (rs : List ℕ) : treeCost rs + 2 ≤ 26 * nodeCount rs + 2 := by
  have h := treeCost_balance rs
  omega

def headers (ell : ℕ) (s : State) : Prop :=
  s.natReg 1 = ell ∧ s.natReg 5 = 0 ∧ s.natReg 6 = ell ∧
    s.natReg 7 = 3 * ell ∧ constants s

def radicesAt (rs : List ℕ) (d : ℕ) (s : State) : Prop :=
  ∀ i : Fin rs.length, s.natHeap (d + i.val) = some (rs.get i)

/-- Logical reference evaluator only. Execution theorems below connect its
    results to the literal bytecode; the program does not invoke this function. -/
def children (visit : State → State) : ℕ → State → State
  | 0, s => setPC s 19
  | k + 1, s => children visit k (pop (visit (child s))
      (s.natReg 2) (s.natReg 3 + 1) (s.natReg 4))

def tree : List ℕ → State → State
  | [], s => emit s
  | r :: rs, s => children (tree rs) r (enter s r)

structure Effect (ell d A c p : ℕ) (s t : State) : Prop where
  pc : t.pc = 19
  header : headers ell t
  depth : t.natReg 0 = d
  address : t.natReg 2 = A
  count : t.natReg 8 = c + p
  low : ∀ a, a < ell + 2 * d → t.natHeap a = s.natHeap a
  previous : ∀ j, j < c → t.natHeap (3 * ell + j) = s.natHeap (3 * ell + j)
  output : ∀ j, j < p → t.natHeap (3 * ell + c + j) = some (A * p + j)

theorem enter_properties (ell : ℕ) (s : State) (r : ℕ) (hh : headers ell s) :
    (enter s r).pc = 4 ∧ headers ell (enter s r) ∧
    (enter s r).natReg 0 = s.natReg 0 ∧ (enter s r).natReg 2 = s.natReg 2 ∧
    (enter s r).natReg 3 = 0 ∧ (enter s r).natReg 4 = r ∧
    (enter s r).natReg 8 = s.natReg 8 ∧ (enter s r).natHeap = s.natHeap := by
  simpa [enter, setPC, writeNat, next, headers, constants] using hh

theorem child_properties (ell : ℕ) (s : State) (hh : headers ell s) :
    (child s).pc = 0 ∧ headers ell (child s) ∧
    (child s).natReg 0 = s.natReg 0 + 1 ∧
    (child s).natReg 2 = s.natReg 2 * s.natReg 4 + s.natReg 3 ∧
    (child s).natReg 8 = s.natReg 8 ∧
    (child s).natHeap = Function.update
      (Function.update s.natHeap (ell + s.natReg 0 * 2) (some (s.natReg 2)))
      (ell + s.natReg 0 * 2 + 1) (some (s.natReg 3 + 1)) := by
  obtain ⟨hL,hT,hs,hO,h1,h2,h0⟩ := hh
  simp [child, child1, child2, child3, child4, child5, child6, child7, child8,
    child9, store, setPC, writeNat, next, hs, h1, h2, headers, constants, hL, hT, hO, h0]

theorem pop_properties (ell : ℕ) (s : State) (A j r : ℕ) (hh : headers ell s) :
    (pop s A j r).pc = 4 ∧ headers ell (pop s A j r) ∧
    (pop s A j r).natReg 0 = s.natReg 0 - 1 ∧
    (pop s A j r).natReg 2 = A ∧ (pop s A j r).natReg 3 = j ∧
    (pop s A j r).natReg 4 = r ∧ (pop s A j r).natReg 8 = s.natReg 8 ∧
    (pop s A j r).natHeap = s.natHeap := by
  obtain ⟨hL,hT,hS,hO,h1,h2,h0⟩ := hh
  simp [pop, pop1, pop2, pop3, pop4, pop5, pop6, pop7, pop8,
    setPC, writeNat, next, h1, headers, constants, hL, hT, hS, hO, h2, h0]

theorem leaf_effect (ell d A c : ℕ) (s : State) (hh : headers ell s)
    (hd : s.natReg 0 = d) (hA : s.natReg 2 = A) (hc : s.natReg 8 = c)
    (hdl : d = ell) : Effect ell d A c 1 s (emit s) := by
  have hh0 := hh
  obtain ⟨_,_,_,hb,h1,_,_⟩ := hh0
  have hheap : (emit s).natHeap = Function.update s.natHeap (3 * ell + c) (some A) := by
    simp [emit, emit1, emit2, emit3, store, setPC, writeNat, next, hb, hc, hA]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emit, emit1, emit2, emit3, store, setPC, writeNat, next, headers, constants] using hh
  · simpa [emit, emit1, emit2, emit3, store, setPC, writeNat, next] using hd
  · simpa [emit, emit1, emit2, emit3, store, setPC, writeNat, next] using hA
  · simp [emit, emit1, emit2, emit3, store, setPC, writeNat, next, hc, h1]
  · intro a ha
    rw [hheap, Function.update_of_ne (show a ≠ 3 * ell + c by omega)]
  · intro j hj
    rw [hheap, Function.update_of_ne (show 3 * ell + j ≠ 3 * ell + c by omega)]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp [hheap]

theorem child_low (ell d : ℕ) (s : State) (hh : headers ell s)
    (hd : s.natReg 0 = d) (a : ℕ) (ha : a < ell + 2 * d) :
    (child s).natHeap a = s.natHeap a := by
  rw [(child_properties ell s hh).2.2.2.2.2]
  simp [hd, Function.update_of_ne (show a ≠ ell + d * 2 + 1 by omega),
    Function.update_of_ne (show a ≠ ell + d * 2 by omega)]

theorem child_previous (ell d : ℕ) (s : State) (hh : headers ell s)
    (hd : s.natReg 0 = d) (hdl : d < ell) (j : ℕ) :
    (child s).natHeap (3 * ell + j) = s.natHeap (3 * ell + j) := by
  rw [(child_properties ell s hh).2.2.2.2.2]
  simp [hd, Function.update_of_ne (show 3 * ell + j ≠ ell + d * 2 + 1 by omega),
    Function.update_of_ne (show 3 * ell + j ≠ ell + d * 2 by omega)]

theorem child_frame (ell d A i : ℕ) (s : State) (hh : headers ell s)
    (hd : s.natReg 0 = d) (hA : s.natReg 2 = A) (hi : s.natReg 3 = i) :
    (child s).natHeap (ell + d * 2) = some A ∧
    (child s).natHeap (ell + d * 2 + 1) = some (i + 1) := by
  rw [(child_properties ell s hh).2.2.2.2.2]
  simp [hd, hA, hi]

structure LoopEffect (ell d A c r i k p : ℕ) (s t : State) : Prop where
  pc : t.pc = 19
  header : headers ell t
  depth : t.natReg 0 = d
  address : t.natReg 2 = A
  count : t.natReg 8 = c + k * p
  low : ∀ a, a < ell + 2 * d → t.natHeap a = s.natHeap a
  previous : ∀ j, j < c → t.natHeap (3 * ell + j) = s.natHeap (3 * ell + j)
  output : ∀ j, j < k * p → t.natHeap (3 * ell + c + j) = some ((A * r + i) * p + j)

def TreeSpec (visit : State → State) (rs : List ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℂ) (ell d A c : ℕ) (s : State),
    s.pc = 0 → headers ell s → s.natReg 0 = d → s.natReg 2 = A →
    s.natReg 8 = c → d + rs.length = ell → radicesAt rs d s →
    Runs n x s (treeCost rs) (visit s) ∧ Effect ell d A c rs.prod s (visit s)

theorem children_spec (visit : State → State) (rs : List ℕ) (hv : TreeSpec visit rs)
    (n : ℕ) (x : Fin n → ℂ) (ell d A c r i k : ℕ) (s : State)
    (hpc : s.pc = 4) (hh : headers ell s) (hd : s.natReg 0 = d)
    (hA : s.natReg 2 = A) (hc : s.natReg 8 = c)
    (hi : s.natReg 3 = i) (hr : s.natReg 4 = r)
    (hdl : d + (r :: rs).length = ell) (hik : i + k = r)
    (htable : radicesAt (r :: rs) d s) :
    Runs n x s (1 + k * (treeCost rs + 21)) (children visit k s) ∧
    LoopEffect ell d A c r i k rs.prod s (children visit k s) := by
  induction k generalizing s c i with
  | zero =>
    have hir : i = r := by omega
    refine ⟨?_, ?_⟩
    · simpa [children] using exhausted_runs n x s hpc (by rw [hi, hr, hir]; omega)
    · refine ⟨rfl, hh, hd, hA, ?_, ?_, ?_, ?_⟩
      · simpa [children, setPC] using hc
      · intro a _; rfl
      · intro j _; rfl
      · intro j hj; omega
  | succ k ih =>
    have hde : d < ell := by simp only [List.length_cons] at hdl; omega
    have hir : i < r := by omega
    have cp := child_properties ell s hh
    have cdepth : (child s).natReg 0 = d + 1 := cp.2.2.1.trans (by rw [hd])
    have caddr : (child s).natReg 2 = A * r + i := by rw [cp.2.2.2.1, hA, hr, hi]
    have ccount : (child s).natReg 8 = c := cp.2.2.2.2.1.trans hc
    have ctable : radicesAt rs (d + 1) (child s) := by
      intro j
      have hj := j.isLt
      have hlen : d + (rs.length + 1) = ell := by simpa using hdl
      have htab := htable ⟨j.val + 1, by simp only [List.length_cons]; omega⟩
      have heq : d + 1 + j.val = d + (j.val + 1) := by omega
      rw [heq, child_low ell d s hh hd _ (by omega)]
      simpa [List.get_eq_getElem] using htab
    obtain ⟨hvisit, e⟩ := hv n x ell (d + 1) (A * r + i) c (child s)
      cp.1 cp.2.1 cdepth caddr ccount (by simp only [List.length_cons] at hdl; omega) ctable
    have frame := child_frame ell d A i s hh hd hA hi
    have tframe1 : (visit (child s)).natHeap (ell + d * 2) = some A :=
      (e.low _ (by omega)).trans frame.1
    have tframe2 : (visit (child s)).natHeap (ell + d * 2 + 1) = some (i + 1) :=
      (e.low _ (by omega)).trans frame.2
    have ttable : radicesAt (r :: rs) d (visit (child s)) := by
      intro j
      rw [e.low _ (by omega), child_low ell d s hh hd _ (by omega)]
      exact htable j
    have tr : (visit (child s)).natHeap d = some r := by
      simpa [List.get_eq_getElem] using ttable ⟨0, by simp⟩
    have hpop := pop_runs n x (visit (child s)) e.pc e.header.2.2.2.2
      (by rw [e.depth]; omega) A (i + 1) r
      (by simpa [e.header.2.1, e.header.2.2.1, e.depth] using tframe1)
      (by simpa [e.header.2.2.1, e.depth] using tframe2)
      (by simpa [e.header.2.1, e.depth] using tr)
    let t := pop (visit (child s)) A (i + 1) r
    have pp := pop_properties ell (visit (child s)) A (i + 1) r e.header
    have td : t.natReg 0 = d := by simpa [t, e.depth] using pp.2.2.1
    have tc : t.natReg 8 = c + rs.prod := pp.2.2.2.2.2.2.1.trans e.count
    have table : radicesAt (r :: rs) d t := by
      intro j
      rw [show t.natHeap = (visit (child s)).natHeap from pp.2.2.2.2.2.2.2]
      exact ttable j
    obtain ⟨hrest, f⟩ := ih (c + rs.prod) (i + 1) t pp.1 pp.2.1 td pp.2.2.2.1 tc
      pp.2.2.2.2.1 pp.2.2.2.2.2.1 (by omega) table
    have htree : children visit (k + 1) s = children visit k t := by
      simp only [children, t, hA, hi, hr]
    rw [htree]
    refine ⟨?_, ?_⟩
    · have hsteps := (child_runs n x s hpc (by rw [hi, hr]; exact hir)).trans
        (hvisit.trans (hpop.trans hrest))
      have heq : 11 + (treeCost rs + (10 + (1 + k * (treeCost rs + 21)))) =
          1 + (k + 1) * (treeCost rs + 21) := by ring
      simpa only [t, heq] using hsteps
    · refine ⟨f.pc, f.header, f.depth, f.address, ?_, ?_, ?_, ?_⟩
      · rw [f.count]; ring
      · intro a ha
        rw [f.low a ha, show t.natHeap = (visit (child s)).natHeap from pp.2.2.2.2.2.2.2,
          e.low a (by omega), child_low ell d s hh hd a ha]
      · intro j hj
        rw [f.previous j (by omega), show t.natHeap = (visit (child s)).natHeap from pp.2.2.2.2.2.2.2,
          e.previous j hj, child_previous ell d s hh hd hde j]
      · intro j hj
        by_cases hjp : j < rs.prod
        · have heq : 3 * ell + c + j = 3 * ell + (c + j) := by omega
          rw [heq, f.previous (c + j) (by omega),
            show t.natHeap = (visit (child s)).natHeap from pp.2.2.2.2.2.2.2]
          simpa only [← heq] using e.output j hjp
        · have hjrest : j - rs.prod < k * rs.prod := by
            simp only [Nat.add_mul, Nat.one_mul] at hj
            omega
          have ho := f.output (j - rs.prod) hjrest
          have hindex : 3 * ell + (c + rs.prod) + (j - rs.prod) = 3 * ell + c + j := by omega
          have hvalue : (A * r + (i + 1)) * rs.prod + (j - rs.prod) =
              (A * r + i) * rs.prod + j := by
            simp only [Nat.add_mul, Nat.one_mul]
            omega
          simpa only [hindex, hvalue] using ho

theorem tree_spec (rs : List ℕ) : TreeSpec (tree rs) rs := by
  induction rs with
  | nil =>
    intro n x ell d A c s hpc hh hd hA hc hdl _
    have he : d = ell := by simpa using hdl
    exact ⟨leaf_runs n x s hpc (by rw [hd, hh.1, he]; omega),
      leaf_effect ell d A c s hh hd hA hc he⟩
  | cons r rs ih =>
    intro n x ell d A c s hpc hh hd hA hc hdl ht
    have hde : d < ell := by simp only [List.length_cons] at hdl; omega
    have hrad : s.natHeap (s.natReg 5 + s.natReg 0) = some r := by
      simpa [hh.2.1, hd, List.get_eq_getElem] using ht ⟨0, by simp⟩
    have ep := enter_properties ell s r hh
    have table : radicesAt (r :: rs) d (enter s r) := by
      intro j
      rw [ep.2.2.2.2.2.2.2]
      exact ht j
    obtain ⟨hrun, e⟩ := children_spec (tree rs) rs ih n x ell d A c r 0 r (enter s r)
      ep.1 ep.2.1 (ep.2.2.1.trans hd) (ep.2.2.2.1.trans hA)
      (ep.2.2.2.2.2.2.1.trans hc) ep.2.2.2.2.1 ep.2.2.2.2.2.1 hdl (by omega) table
    refine ⟨?_, ?_⟩
    · simpa only [tree, treeCost, show 4 + (1 + r * (treeCost rs + 21)) =
          5 + r * (treeCost rs + 21) by omega] using
        (enter_runs n x s hpc (by rw [hd, hh.1]; exact hde) r hrad).trans hrun
    · refine ⟨e.pc, e.header, e.depth, e.address, ?_, ?_, ?_, ?_⟩
      · simpa [tree] using e.count
      · intro a ha
        exact (e.low a ha).trans (congrFun ep.2.2.2.2.2.2.2 a)
      · intro j hj
        exact (e.previous j hj).trans (congrFun ep.2.2.2.2.2.2.2 _)
      · intro j hj
        simpa only [tree, List.prod_cons, Nat.add_zero, Nat.mul_assoc] using e.output j hj

/-- The literal program visits every mixed-radix leaf in lexicographic order.
    Radix/table preparation is an explicit incoming-state obligation. -/
theorem complete_execution (rs : List ℕ) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 0) (hh : headers rs.length s)
    (hd : s.natReg 0 = 0) (hA : s.natReg 2 = 0) (hc : s.natReg 8 = 0)
    (ht : radicesAt rs 0 s) :
    Executes program n x s (treeCost rs + 2) (setPC (tree rs s) 29) ∧
    (setPC (tree rs s) 29).natReg 8 = rs.prod ∧
    ∀ j, j < rs.prod → (setPC (tree rs s) 29).natHeap (3 * rs.length + j) = some j := by
  obtain ⟨h, e⟩ := tree_spec rs n x rs.length 0 0 0 s hpc hh hd hA hc (by omega) ht
  refine ⟨h.finish (halt_executes n x _ e.pc e.header.2.2.2.2 e.depth), ?_, ?_⟩
  · simpa [setPC] using e.count
  · intro j hj
    simpa [setPC] using e.output j hj

theorem complete_instruction_bound (rs : List ℕ) : treeCost rs + 2 ≤ 26 * nodeCount rs + 2 :=
  treeCost_bound rs

theorem setPC_wordBound {B : ℕ} {s : State} (h : WordBound B s) (p : ℕ) (hp : p ≤ B) :
    WordBound B (setPC s p) := ⟨hp,h.2⟩

theorem store_wordBound {B : ℕ} {s : State} (h : WordBound B s) (a v : ℕ)
    (hp : s.pc + 1 ≤ B) (ha : a ≤ B) (hv : v ≤ B) : WordBound B (store s a v) := by
  refine ⟨hp,h.2.1,?_,h.2.2.2⟩
  intro j w hj
  by_cases he : j = a
  · subst j
    have hw : w = v := by simpa [store, next] using hj.symm
    subst w
    exact ⟨ha,hv⟩
  · exact h.2.2.1 j w (by simpa [store, next, he] using hj)

theorem enter_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 0)
    (hl : s.natReg 0 < s.natReg 1) (r : ℕ)
    (hr : s.natHeap (s.natReg 5 + s.natReg 0) = some r)
    (ht : s.natReg 5 + s.natReg 0 ≤ B) (hR : r ≤ B) :
    BoundedRuns n x B s 4 (enter s r) := by
  have h1 := setPC_wordBound hs 1 (by omega)
  have h2 := UniformTraversalMachine.writeNat_wordBound B _ 11 _ h1
    (by change 2 ≤ B; omega) ht
  have h3 := UniformTraversalMachine.writeNat_wordBound B _ 4 _ h2
    (by change 3 ≤ B; omega) hR
  have h4 := UniformTraversalMachine.writeNat_wordBound B _ 3 0 h3
    (by change 4 ≤ B; omega) (by omega)
  refine .next hs ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_ (.refl _ h4))))
  all_goals simp [step, program, hpc, hl, hr, enter, setPC, writeNat, next, evalNat]

def ChildBounds (s : State) (B : ℕ) : Prop :=
  s.natReg 0 * s.natReg 10 ≤ B ∧
    s.natReg 6 + s.natReg 0 * s.natReg 10 ≤ B ∧
    s.natReg 6 + s.natReg 0 * s.natReg 10 + s.natReg 9 ≤ B ∧
    s.natReg 3 + s.natReg 9 ≤ B ∧
    s.natReg 2 * s.natReg 4 ≤ B ∧
    s.natReg 2 * s.natReg 4 + s.natReg 3 ≤ B ∧
    s.natReg 0 + s.natReg 9 ≤ B

theorem child_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 4)
    (hd : s.natReg 3 < s.natReg 4) (hb : ChildBounds s B) :
    BoundedRuns n x B s 11 (child s) := by
  obtain ⟨v1,v2,v3,v4,v5,v6,v7⟩ := hb
  have h0 := setPC_wordBound hs 5 (by omega)
  have h1 : WordBound B (child1 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h0
    (by change 6 ≤ B; omega) v1
  have h2 : WordBound B (child2 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h1
    (by change 7 ≤ B; omega) v2
  have h3 : WordBound B (child3 s) := store_wordBound h2 _ _
    (by change 8 ≤ B; omega) v2 (hs.2.1 2)
  have h4 : WordBound B (child4 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h3
    (by change 9 ≤ B; omega) v3
  have h5 : WordBound B (child5 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h4
    (by change 10 ≤ B; omega) v4
  have h6 : WordBound B (child6 s) := store_wordBound h5 _ _
    (by change 11 ≤ B; omega) v3 v4
  have h7 : WordBound B (child7 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h6
    (by change 12 ≤ B; omega) v5
  have h8 : WordBound B (child8 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h7
    (by change 13 ≤ B; omega) v6
  have h9 : WordBound B (child9 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h8
    (by change 14 ≤ B; omega) v7
  have hf : WordBound B (child s) := setPC_wordBound h9 0 (by omega)
  refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_
    (.next h4 ?_ (.next h5 ?_ (.next h6 ?_ (.next h7 ?_ (.next h8 ?_
      (.next h9 ?_ (.refl _ hf)))))))))))
  all_goals simp [step, program, hpc, hd, child, child1, child2, child3, child4, child5,
    child6, child7, child8, child9, store, setPC, writeNat, next, evalNat]

theorem leaf_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 0)
    (hl : ¬s.natReg 0 < s.natReg 1)
    (hp : s.natReg 7 + s.natReg 8 ≤ B) (hc : s.natReg 8 + s.natReg 9 ≤ B) :
    BoundedRuns n x B s 5 (emit s) := by
  have h0 := setPC_wordBound hs 15 (by omega)
  have h1 : WordBound B (emit1 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h0
    (by change 16 ≤ B; omega) hp
  have h2 : WordBound B (emit2 s) := store_wordBound h1 _ _
    (by change 17 ≤ B; omega) hp (hs.2.1 2)
  have h3 : WordBound B (emit3 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h2
    (by change 18 ≤ B; omega) hc
  have hf : WordBound B (emit s) := setPC_wordBound h3 19 (by omega)
  refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_
    (.next h3 ?_ (.refl _ hf)))))
  all_goals simp [step, program, hpc, hl, emit, emit1, emit2, emit3, store, setPC, writeNat, next, evalNat]

def PopBounds (s : State) (B a d r : ℕ) : Prop :=
  (s.natReg 0 - s.natReg 9) * s.natReg 10 ≤ B ∧
    s.natReg 6 + (s.natReg 0 - s.natReg 9) * s.natReg 10 ≤ B ∧
    s.natReg 6 + (s.natReg 0 - s.natReg 9) * s.natReg 10 + s.natReg 9 ≤ B ∧
    s.natReg 5 + (s.natReg 0 - s.natReg 9) ≤ B ∧ a ≤ B ∧ d ≤ B ∧ r ≤ B

theorem pop_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 19)
    (hc : constants s) (hp : 0 < s.natReg 0) (a d r : ℕ)
    (ha : s.natHeap (s.natReg 6 + (s.natReg 0 - 1) * 2) = some a)
    (hd : s.natHeap (s.natReg 6 + (s.natReg 0 - 1) * 2 + 1) = some d)
    (hr : s.natHeap (s.natReg 5 + (s.natReg 0 - 1)) = some r)
    (hb : PopBounds s B a d r) : BoundedRuns n x B s 10 (pop s a d r) := by
  obtain ⟨v1,v2,v3,v4,va,vd,vr⟩ := hb
  obtain ⟨h1c,h2c,h0c⟩ := hc
  have h0 := setPC_wordBound hs 20 (by omega)
  have h1 : WordBound B (pop1 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h0
    (by change 21 ≤ B; omega) ((Nat.sub_le _ _).trans (hs.2.1 0))
  have h2 : WordBound B (pop2 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h1
    (by change 22 ≤ B; omega) v1
  have h3 : WordBound B (pop3 s) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h2
    (by change 23 ≤ B; omega) v2
  have h4 : WordBound B (pop4 s a) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h3
    (by change 24 ≤ B; omega) va
  have h5 : WordBound B (pop5 s a) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h4
    (by change 25 ≤ B; omega) v3
  have h6 : WordBound B (pop6 s a d) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h5
    (by change 26 ≤ B; omega) vd
  have h7 : WordBound B (pop7 s a d) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h6
    (by change 27 ≤ B; omega) v4
  have h8 : WordBound B (pop8 s a d r) := UniformTraversalMachine.writeNat_wordBound B _ _ _ h7
    (by change 28 ≤ B; omega) vr
  have hf : WordBound B (pop s a d r) := setPC_wordBound h8 4 (by omega)
  refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_
    (.next h4 ?_ (.next h5 ?_ (.next h6 ?_ (.next h7 ?_ (.next h8 ?_ (.refl _ hf))))))))))
  all_goals simp [step, program, hpc, hp, h1c, h2c, h0c, ha, hd, hr, pop, pop1, pop2, pop3,
    pop4, pop5, pop6, pop7, pop8, setPC, writeNat, next, evalNat]

theorem exhausted_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 4)
    (hd : ¬s.natReg 3 < s.natReg 4) : BoundedRuns n x B s 1 (setPC s 19) :=
  .next hs (by simp [step, program, hpc, hd, setPC])
    (.refl _ (setPC_wordBound hs 19 (by omega)))

theorem halt_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 30 ≤ B) (hs : WordBound B s) (hpc : s.pc = 19)
    (hc : constants s) (hd : s.natReg 0 = 0) : BoundedExecution program n x B s 2 (setPC s 29) := by
  have h0 := hc.2.2
  refine .next hs ?_ (.halt (setPC_wordBound hs 29 (by omega)) ?_)
  all_goals simp [step, program, hpc, h0, hd, setPC]

def Positive (rs : List ℕ) : Prop := ∀ r ∈ rs, 0 < r

theorem positive_product (rs : List ℕ) (h : Positive rs) : 0 < rs.prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => exact Nat.mul_pos (h r (by simp)) (ih (by intro q hq; exact h q (by simp [hq])))

def BoundedTreeSpec (rs : List ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℂ) (ell d A c R B : ℕ) (s : State),
    s.pc = 0 → headers ell s → s.natReg 0 = d → s.natReg 2 = A →
    s.natReg 8 = c → d + rs.length = ell → radicesAt rs d s →
    Positive rs → (A + 1) * rs.prod ≤ R → c + rs.prod ≤ R →
    30 + 3 * ell + R ≤ B → WordBound B s →
    BoundedRuns n x B s (treeCost rs) (tree rs s)

theorem children_bounded (rs : List ℕ) (hv : BoundedTreeSpec rs)
    (n : ℕ) (x : Fin n → ℂ) (ell d A c r i k R B : ℕ) (s : State)
    (hpc : s.pc = 4) (hh : headers ell s) (hd : s.natReg 0 = d)
    (hA : s.natReg 2 = A) (hc : s.natReg 8 = c)
    (hi : s.natReg 3 = i) (hr : s.natReg 4 = r)
    (hdl : d + (r :: rs).length = ell) (hik : i + k = r)
    (htable : radicesAt (r :: rs) d s) (hpos : Positive (r :: rs))
    (hfit : (A + 1) * (r * rs.prod) ≤ R) (hcount : c + k * rs.prod ≤ R)
    (hB : 30 + 3 * ell + R ≤ B) (hs : WordBound B s) :
    BoundedRuns n x B s (1 + k * (treeCost rs + 21)) (children (tree rs) k s) := by
  have hB30 : 30 ≤ B := by omega
  have hp : Positive rs := by intro q hq; exact hpos q (by simp [hq])
  have hp0 : 0 < rs.prod := positive_product rs hp
  have hr0 : 0 < r := hpos r (by simp)
  have hrR : r ≤ R := by
    have hm : r ≤ r * rs.prod := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left r (show 1 ≤ rs.prod by omega)
    have h1 : r ≤ (A + 1) * (r * rs.prod) := hm.trans (by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (r * rs.prod) (show 1 ≤ A + 1 by omega))
    exact h1.trans hfit
  have hAR : A ≤ R := by
    have hprod : 1 ≤ r * rs.prod := Nat.succ_le_of_lt (Nat.mul_pos hr0 hp0)
    have h1 : A ≤ (A + 1) * (r * rs.prod) := (show A ≤ A + 1 by omega).trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A + 1) hprod)
    exact h1.trans hfit
  induction k generalizing s c i with
  | zero =>
    have hir : i = r := by omega
    simpa [children] using exhausted_bounded n x B s hB30 hs hpc (by rw [hi, hr, hir]; omega)
  | succ k ih =>
    have hde : d < ell := by simp only [List.length_cons] at hdl; omega
    have hir : i < r := by omega
    have childfit : (A * r + i + 1) * rs.prod ≤ R := by
      calc
        _ ≤ ((A + 1) * r) * rs.prod := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (A + 1) * (r * rs.prod) := by ring
        _ ≤ R := hfit
    have childaddr : A * r + i ≤ R := by
      have h1 : A * r + i ≤ (A * r + i + 1) * rs.prod := (show A * r + i ≤ A * r + i + 1 by omega).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A * r + i + 1) (show 1 ≤ rs.prod by omega))
      exact h1.trans childfit
    have cb : ChildBounds s B := by
      simp only [ChildBounds, hd, hA, hi, hr, hh.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1]
      refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
    have hcstep := child_bounded n x B s hB30 hs hpc (by rw [hi, hr]; exact hir) cb
    have cp := child_properties ell s hh
    have cdepth : (child s).natReg 0 = d + 1 := cp.2.2.1.trans (by rw [hd])
    have caddr : (child s).natReg 2 = A * r + i := by rw [cp.2.2.2.1, hA, hr, hi]
    have ccount : (child s).natReg 8 = c := cp.2.2.2.2.1.trans hc
    have ctable : radicesAt rs (d + 1) (child s) := by
      intro j
      have hj := j.isLt
      have hlen : d + (rs.length + 1) = ell := by simpa using hdl
      have htab := htable ⟨j.val + 1, by simp only [List.length_cons]; omega⟩
      have heq : d + 1 + j.val = d + (j.val + 1) := by omega
      rw [heq, child_low ell d s hh hd _ (by omega)]
      simpa [List.get_eq_getElem] using htab
    have hcc : c + rs.prod ≤ R := by
      simp only [Nat.add_mul, Nat.one_mul] at hcount
      omega
    have hvisit := hv n x ell (d + 1) (A * r + i) c R B (child s)
      cp.1 cp.2.1 cdepth caddr ccount (by simp only [List.length_cons] at hdl; omega)
      ctable hp childfit hcc hB hcstep.final_bound
    obtain ⟨_, e⟩ := tree_spec rs n x ell (d + 1) (A * r + i) c (child s)
      cp.1 cp.2.1 cdepth caddr ccount (by simp only [List.length_cons] at hdl; omega) ctable
    have frame := child_frame ell d A i s hh hd hA hi
    have tframe1 : (tree rs (child s)).natHeap (ell + d * 2) = some A :=
      (e.low _ (by omega)).trans frame.1
    have tframe2 : (tree rs (child s)).natHeap (ell + d * 2 + 1) = some (i + 1) :=
      (e.low _ (by omega)).trans frame.2
    have ttable : radicesAt (r :: rs) d (tree rs (child s)) := by
      intro j
      rw [e.low _ (by omega), child_low ell d s hh hd _ (by omega)]
      exact htable j
    have tr : (tree rs (child s)).natHeap d = some r := by
      simpa [List.get_eq_getElem] using ttable ⟨0, by simp⟩
    have pb : PopBounds (tree rs (child s)) B A (i + 1) r := by
      simp only [PopBounds, e.depth, e.header.2.1, e.header.2.2.1,
        e.header.2.2.2.2.1, e.header.2.2.2.2.2.1, Nat.add_sub_cancel]
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
    have hpop := pop_bounded n x B (tree rs (child s)) hB30 hvisit.final_bound
      e.pc e.header.2.2.2.2 (by rw [e.depth]; omega) A (i + 1) r
      (by simpa [e.header.2.2.1, e.depth] using tframe1)
      (by simpa [e.header.2.2.1, e.depth] using tframe2)
      (by simpa [e.header.2.1, e.depth] using tr) pb
    let t := pop (tree rs (child s)) A (i + 1) r
    have pp := pop_properties ell (tree rs (child s)) A (i + 1) r e.header
    have td : t.natReg 0 = d := by simpa [t, e.depth] using pp.2.2.1
    have tc : t.natReg 8 = c + rs.prod := pp.2.2.2.2.2.2.1.trans e.count
    have table : radicesAt (r :: rs) d t := by
      intro j
      rw [show t.natHeap = (tree rs (child s)).natHeap from pp.2.2.2.2.2.2.2]
      exact ttable j
    have nextcount : (c + rs.prod) + k * rs.prod ≤ R := by
      simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount
    have hrest := ih (c + rs.prod) (i + 1) t pp.1 pp.2.1 td pp.2.2.2.1 tc
      pp.2.2.2.2.1 pp.2.2.2.2.2.1 (by omega) table nextcount hpop.final_bound
    have hsteps := hcstep.trans (hvisit.trans (hpop.trans hrest))
    have heq : 11 + (treeCost rs + (10 + (1 + k * (treeCost rs + 21)))) =
        1 + (k + 1) * (treeCost rs + 21) := by ring
    simpa only [children, t, hA, hi, hr, heq] using hsteps

theorem tree_bounded (rs : List ℕ) : BoundedTreeSpec rs := by
  induction rs with
  | nil =>
    intro n x ell d A c R B s hpc hh hd hA hc hdl ht hp hfit hcount hB hs
    have he : d = ell := by simpa using hdl
    have h1 := hh.2.2.2.2.1
    have ho := hh.2.2.2.1
    have hcount' : c + 1 ≤ R := by simpa using hcount
    exact leaf_bounded n x B s (by omega) hs hpc
      (by rw [hd, hh.1, he]; omega) (by rw [ho,hc]; omega) (by rw [hc,h1]; omega)
  | cons r rs ih =>
    intro n x ell d A c R B s hpc hh hd hA hc hdl ht hp hfit hcount hB hs
    have hde : d < ell := by simp only [List.length_cons] at hdl; omega
    have hrad : s.natHeap (s.natReg 5 + s.natReg 0) = some r := by
      simpa [hh.2.1, hd, List.get_eq_getElem] using ht ⟨0, by simp⟩
    have hrB : r ≤ B := (hs.2.2.1 _ _ hrad).2
    have hent := enter_bounded n x B s (by omega) hs hpc (by rw [hd,hh.1]; omega) r hrad
      (by rw [hh.2.1,hd]; omega) hrB
    have ep := enter_properties ell s r hh
    have table : radicesAt (r :: rs) d (enter s r) := by
      intro j
      rw [ep.2.2.2.2.2.2.2]
      exact ht j
    have hloop := children_bounded rs ih n x ell d A c r 0 r R B (enter s r)
      ep.1 ep.2.1 (ep.2.2.1.trans hd) (ep.2.2.2.1.trans hA)
      (ep.2.2.2.2.2.2.1.trans hc) ep.2.2.2.2.1 ep.2.2.2.2.2.1
      hdl (by omega) table hp hfit hcount hB hent.final_bound
    simpa only [tree, treeCost, show 4 + (1 + r * (treeCost rs + 21)) =
        5 + r * (treeCost rs + 21) by omega] using hent.trans hloop

/-- Complete checked execution, with a linear bound on every integer/address.
    The input state's prepared heaps and unrelated registers must already obey it. -/
theorem complete_bounded_execution (rs : List ℕ) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 0) (hh : headers rs.length s)
    (hd : s.natReg 0 = 0) (hA : s.natReg 2 = 0) (hc : s.natReg 8 = 0)
    (ht : radicesAt rs 0 s) (hp : Positive rs)
    (hs : WordBound (30 + 3 * rs.length + rs.prod) s) :
    BoundedExecution program n x (30 + 3 * rs.length + rs.prod) s
      (treeCost rs + 2) (setPC (tree rs s) 29) := by
  have h := tree_bounded rs n x rs.length 0 0 0 rs.prod (30 + 3 * rs.length + rs.prod)
    s hpc hh hd hA hc (by omega) ht hp (by simp) (by simp) (by omega) hs
  obtain ⟨_,e⟩ := tree_spec rs n x rs.length 0 0 0 s hpc hh hd hA hc (by omega) ht
  exact h.finish (halt_bounded n x _ _ (by omega) h.final_bound e.pc e.header.2.2.2.2 e.depth)

theorem complete_leaf_mixed_radix (rs : List ℕ) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 0) (hh : headers rs.length s)
    (hd : s.natReg 0 = 0) (hA : s.natReg 2 = 0) (hc : s.natReg 8 = 0)
    (ht : radicesAt rs 0 s) (j : Fin rs.prod) :
    (setPC (tree rs s) 29).natHeap (3 * rs.length + j.val) =
      some (follow (addressLayers rs) (decode rs j) 0) := by
  rw [follow_address, encode_decode]
  simpa using (complete_execution rs n x s hpc hh hd hA hc ht).2.2 j.val j.isLt

/-- Depth and array width bounded by the problem size give a fixed polynomial
    word/address bound. This does not charge the preparation of the table. -/
theorem polynomial_word_bound (ell R N : ℕ) (h : ell + R ≤ N) :
    30 + 3 * ell + R ≤ (N + 2) ^ 5 := by
  calc
    _ ≤ 30 + 3 * N := by omega
    _ ≤ (N + 2) ^ 5 := by
      nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3), Nat.zero_le (N ^ 4), Nat.zero_le (N ^ 5)]

theorem BoundedExecution.mono {n B C t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : UniformMachine.BoundedExecution program n x B s t u) (hBC : B ≤ C) :
    UniformMachine.BoundedExecution program n x C s t u := by
  have wb : ∀ v, WordBound B v → WordBound C v := by
    intro v hv
    refine ⟨hv.1.trans hBC, fun r => (hv.2.1 r).trans hBC, ?_, ?_, ?_, ?_⟩
    · intro a w hw
      exact ⟨(hv.2.2.1 a w hw).1.trans hBC,(hv.2.2.1 a w hw).2.trans hBC⟩
    · intro a w hw; exact (hv.2.2.2.1 a w hw).trans hBC
    · intro a w hw; exact (hv.2.2.2.2.1 a w hw).trans hBC
    · intro d hd; exact (hv.2.2.2.2.2 d hd).trans hBC
  induction h with
  | halt hv hs => exact .halt (wb _ hv) hs
  | next hv hs _ ih => exact .next (wb _ hv) hs ih

theorem complete_polynomial_execution (rs : List ℕ) (n N : ℕ) (x : Fin n → ℂ) (s : State)
    (hpc : s.pc = 0) (hh : headers rs.length s)
    (hd : s.natReg 0 = 0) (hA : s.natReg 2 = 0) (hc : s.natReg 8 = 0)
    (ht : radicesAt rs 0 s) (hp : Positive rs)
    (hs : WordBound (30 + 3 * rs.length + rs.prod) s) (hN : rs.length + rs.prod ≤ N) :
    UniformMachine.BoundedExecution program n x ((N + 2) ^ 5) s
      (treeCost rs + 2) (setPC (tree rs s) 29) :=
  BoundedExecution.mono (complete_bounded_execution rs n x s hpc hh hd hA hc ht hp hs)
    (polynomial_word_bound _ _ _ hN)

theorem complete_linear_work (rs : List ℕ) (hr : ∀ r ∈ rs, 2 ≤ r) :
    treeCost rs + 2 < 52 * rs.prod + 2 := by
  have h1 := treeCost_bound rs
  have h2 := nodeCount_lt_twice_product rs hr
  omega

def auxiliary (s : State) : (ℕ → Scalar) × (ℕ → Option Scalar) × (ℕ → Option ℂ) × List ℕ :=
  (s.scalarReg,s.scalarHeap,s.outputs,s.rootOrders)

theorem children_auxiliary (v : State → State) (hv : ∀ s, auxiliary (v s) = auxiliary s)
    (k : ℕ) (s : State) : auxiliary (children v k s) = auxiliary s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [children, ih]
    change auxiliary (v (child s)) = auxiliary s
    rw [hv]
    rfl

theorem tree_auxiliary (rs : List ℕ) (s : State) : auxiliary (tree rs s) = auxiliary s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact (children_auxiliary _ ih r (enter s r)).trans rfl

theorem final_auxiliary (rs : List ℕ) (s : State) :
    auxiliary (setPC (tree rs s) 29) = auxiliary s := tree_auxiliary rs s

/-- Canonical prepared layout, useful as a logical specification and fixture.
    It is not itself a charged RAM preparation subroutine. -/
noncomputable def preparedState (rs : List ℕ) : State :=
  {UniformMachine.initial with
    natReg := fun r => if r = 1 then rs.length else if r = 6 then rs.length else
      if r = 7 then 3 * rs.length else if r = 9 then 1 else if r = 10 then 2 else 0
    natHeap := fun a => rs[a]?}

theorem prepared_headers (rs : List ℕ) : headers rs.length (preparedState rs) := by
  simp [preparedState, headers, constants]

theorem prepared_radices (rs : List ℕ) : radicesAt rs 0 (preparedState rs) := by
  intro j
  simp [preparedState, List.get_eq_getElem]

theorem positive_member_le_product (rs : List ℕ) (hp : Positive rs) (r : ℕ) (hr : r ∈ rs) :
    r ≤ rs.prod := by
  induction rs with
  | nil => simp at hr
  | cons q qs ih =>
    have hq : 0 < q := hp q (by simp)
    have ht : Positive qs := by intro a ha; exact hp a (by simp [ha])
    have hprod : 0 < qs.prod := positive_product qs ht
    rcases List.mem_cons.mp hr with h | h
    · subst r
      simpa only [List.prod_cons, Nat.mul_one] using
        Nat.mul_le_mul_left q (show 1 ≤ qs.prod by omega)
    · exact (ih ht h).trans (by
        simpa only [List.prod_cons, Nat.one_mul] using
          Nat.mul_le_mul_right qs.prod (show 1 ≤ q by omega))

theorem prepared_wordBound (rs : List ℕ) (hp : Positive rs) :
    WordBound (30 + 3 * rs.length + rs.prod) (preparedState rs) := by
  refine ⟨by simp [preparedState, initial], ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    simp only [preparedState]
    split_ifs <;> omega
  · intro a v hv
    have hget : rs[a]? = some v := hv
    obtain ⟨ha,_⟩ := List.getElem?_eq_some_iff.mp hget
    exact ⟨by omega,(positive_member_le_product rs hp v (List.mem_of_getElem? hget)).trans (by omega)⟩
  · simp [preparedState, initial]
  · simp [preparedState, initial]
  · simp [preparedState, initial]

theorem prepared_complete_execution (rs : List ℕ) (hp : Positive rs) (n : ℕ) (x : Fin n → ℂ) :
    UniformMachine.BoundedExecution program n x (30 + 3 * rs.length + rs.prod) (preparedState rs)
      (treeCost rs + 2) (setPC (tree rs (preparedState rs)) 29) :=
  complete_bounded_execution rs n x _ rfl (prepared_headers rs)
    (by simp [preparedState]) (by simp [preparedState]) (by simp [preparedState])
    (prepared_radices rs) hp (prepared_wordBound rs hp)

def integerInstruction : Instruction → Bool
  | .natLiteral .. | .length .. | .natBinary .. | .loadNat .. | .storeNat .. |
    .branchLT .. | .jump .. | .halt => true
  | _ => false

theorem program_integer_only : ∀ i ∈ program, integerInstruction i = true := by
  simp [program, integerInstruction]

/-- Executable projection for diagnostics. Its one-step equivalence to the
    actual machine is proved below; it contains no traversal primitive. -/
structure NatState where
  pc : ℕ
  reg : ℕ → ℕ
  heap : ℕ → Option ℕ

def natView (s : State) : NatState := ⟨s.pc,s.natReg,s.natHeap⟩
def NatState.next (s : NatState) : NatState := {s with pc := s.pc + 1}
def NatState.write (s : NatState) (r v : ℕ) : NatState :=
  {s.next with reg := Function.update s.reg r v}

inductive NatResult where
  | running (s : NatState)
  | halted (s : NatState)
  | failed

def natResult : StepResult → NatResult
  | .running s => .running (natView s)
  | .halted s => .halted (natView s)
  | .failed => .failed

def natStep (p : Program) (n : ℕ) (s : NatState) : NatResult :=
  match p[s.pc]? with
  | some .halt => .halted s
  | some (.natLiteral r v) => .running (s.write r v)
  | some (.length r) => .running (s.write r n)
  | some (.natBinary op r a b) => match evalNat op (s.reg a) (s.reg b) with
      | some v => .running (s.write r v)
      | none => .failed
  | some (.loadNat r a) => match s.heap (s.reg a) with
      | some v => .running (s.write r v)
      | none => .failed
  | some (.storeNat a r) => .running
      {s.next with heap := Function.update s.heap (s.reg a) (some (s.reg r))}
  | some (.branchLT a b yes no) => .running {s with pc := if s.reg a < s.reg b then yes else no}
  | some (.jump pc) => .running {s with pc := pc}
  | _ => .failed

theorem natStep_correct (p : Program) (hp : ∀ i ∈ p, integerInstruction i = true)
    (n : ℕ) (x : Fin n → ℂ) (s : State) :
    natResult (step p n x s) = natStep p n (natView s) := by
  cases hf : p[s.pc]? with
  | none => simp [step,natStep,natView,hf,natResult]
  | some i =>
    have hi := hp i (List.mem_of_getElem? hf)
    cases i <;> simp only [integerInstruction, Bool.false_eq_true] at hi
    all_goals simp only [step,natStep,natView,hf]
    all_goals first
      | rfl
      | (split <;> simp_all [natResult,natView,NatState.write,NatState.next,writeNat,next])

/-- Actual diagnostic program execution is sound for arbitrary input arrays,
    since this bytecode does not contain scalar or input-dependent instructions. -/
theorem program_natStep_correct (n : ℕ) (x : Fin n → ℂ) (s : State) :
    natResult (step program n x s) = natStep program n (natView s) :=
  natStep_correct program program_integer_only n x s

def preparedNatState (rs : List ℕ) : NatState :=
  ⟨0,fun r => if r = 1 then rs.length else if r = 6 then rs.length else
    if r = 7 then 3 * rs.length else if r = 9 then 1 else if r = 10 then 2 else 0,
    fun a => rs[a]?⟩

theorem prepared_natView (rs : List ℕ) : natView (preparedState rs) = preparedNatState rs := rfl

/-- The actual ordered block-choice traversal has linear prefix-node work even
    when a local table contains only one block. -/
theorem actual_sector_prefix_work (axes : List UniformSectorPacking.Axis) :
    treeCost (UniformSectorPacking.blockCounts axes) + 2 <
      52 * (UniformSectorPacking.radices axes).prod + 2 := by
  have h := UniformSectorPacking.block_traversal_prefix_bound axes
  rw [run_visits,UniformSectorPacking.blockLayers_radices] at h
  have hc := treeCost_bound (UniformSectorPacking.blockCounts axes)
  omega

end ExactFourierCircuits.UniformDFSProgram
