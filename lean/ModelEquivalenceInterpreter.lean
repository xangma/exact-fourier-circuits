import UniformMachine
import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

/-!
# A charged fresh-tape update, and the naive interpreter's memory obstruction

`update` is actual upstream typed `Code`, with no new atom or handler. It
implements the value of `Tape.set` by constructing a fresh tape. Its charged
work is linear in the tape length, whereas our in-place store takes one step.
This is an obstruction to this particular compiler, not a lower bound for all
possible representations or a proof that the two models are inequivalent.
No whole-machine constant-overhead simulation is asserted here.
-/
namespace ExactFourierCircuits.ModelEquivalenceInterpreter
open OAI.PowerSaving OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev UpdateInput (t : Ty) := p (p (a t) w) t

def oldTape (t : Ty) : Prog false (p (UpdateInput t) w) (a t) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))

def target (t : Ty) : Prog false (p (UpdateInput t) w) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))

def replacement (t : Ty) : Prog false (p (UpdateInput t) w) t :=
  .comp (.atom .fst) (.atom .snd)

def index (t : Ty) : Prog false (p (UpdateInput t) w) w := .atom .snd

/-- A natural-only equality test: both truncated differences sum to zero. -/
def difference (t : Ty) : Prog false (p (UpdateInput t) w) w :=
  .comp (.fork
    (.comp (.fork (target t) (index t)) (.atom (.int .sub)))
    (.comp (.fork (index t) (target t)) (.atom (.int .sub))))
    (.atom (.int .add))

def oldCell (t : Ty) : Prog false (p (UpdateInput t) w) t :=
  .comp (.fork (oldTape t) (index t)) (.atom .look)

def updateCell (t : Ty) : Prog false (p (UpdateInput t) w) t :=
  .ifz (difference t) (replacement t) (oldCell t)

def updateLength (t : Ty) : Prog false (UpdateInput t) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .len))

/-- Rebuild every cell; the input tape remains published and unchanged. -/
def update (t : Ty) : Prog false (UpdateInput t) (a t) :=
  .tab (updateLength t) (updateCell t)

theorem updateLength_run (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    run (updateLength t) ((v,i),x) = ⟨v.len,5,v.len,True⟩ := by
  simp [updateLength, run, Code.run, Atom.run, Bill.pass, Bill.pay, Bill.one, Bill.word]

def distance (i j : ℕ) : ℕ := (i-j)+(j-i)

theorem distance_eq_zero_iff (i j : ℕ) : distance i j = 0 ↔ i = j := by
  unfold distance
  omega

theorem updateCell_run (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) (j : ℕ) :
    run (updateCell t) (((v,i),x),j) =
      ⟨if j = i then x else v.look j t.blank,
        if j = i then 25 else 31, distance i j, True⟩ := by
  by_cases h : j = i
  · subst j
    simp [updateCell, difference, replacement, oldCell, oldTape, target, index,
      run, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word,
      distance]
  · have hn : ¬ (i-j = 0 ∧ j-i = 0) := by omega
    simp [updateCell, difference, replacement, oldCell, oldTape, target, index,
      run, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word,
      distance, hn, h]

/-- The partial builder is used only to calculate the actual `Bill.tab`. -/
def materialize {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) (m : ℕ) : Bill (Tape α) :=
  Bill.steps (Tape.tab n (fun _ => z))
    (fun j v => ((f j).pass (fun y => Bill.one (j,y))).pass
      (fun s => Bill.one (v.set s.1 s.2))) m

theorem materialize_work {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) (m : ℕ) :
    (materialize n z f m).work = 1+3*m+∑ j ∈ Finset.range m, (f j).work := by
  induction m with
  | zero => simp [materialize, Bill.steps, Bill.one]
  | succ m ih =>
    change (materialize n z f m).work + (f m).work + 1 + 1 + 1 = _
    rw [ih, Finset.sum_range_succ]
    omega

theorem materialize_peak {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) (m : ℕ) :
    (materialize n z f m).peak = max m ((Finset.range m).sup (fun j => (f j).peak)) := by
  induction m with
  | zero => simp [materialize, Bill.steps, Bill.one]
  | succ m ih =>
    change max (max (materialize n z f m).peak (max (max (f m).peak 0) 0))
      (m+1) = _
    rw [ih, Finset.range_add_one, Finset.sup_insert]
    simp only [max_zero]
    change max (max (max m ((Finset.range m).sup (fun j => (f j).peak)))
      (f m).peak) (m+1) =
        max (m+1) (max (f m).peak ((Finset.range m).sup (fun j => (f j).peak)))
    omega

theorem materialize_valid {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) (m : ℕ) :
    (materialize n z f m).valid ↔ ∀ j < m, (f j).valid := by
  induction m with
  | zero => simp [materialize, Bill.steps, Bill.one]
  | succ m ih =>
    change ((materialize n z f m).valid ∧ ((f m).valid ∧ True) ∧ True) ↔ _
    rw [ih]
    simp only [and_true]
    constructor
    · rintro ⟨h, hm⟩ j hj
      by_cases he : j = m
      · simpa [he] using hm
      · exact h j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h m (by omega)⟩

theorem materialize_len {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) (m : ℕ) :
    (materialize n z f m).val.len = n := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

theorem materialize_look {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α)
    (m : ℕ) (hm : m ≤ n) (j : ℕ) (hj : j < n) :
    (materialize n z f m).val.look j z = if j < m then (f j).val else z := by
  induction m with
  | zero => simp [materialize, Bill.steps, Bill.one, Tape.look, Tape.tab, hj]
  | succ m ih =>
    have hn := materialize_len n z f m
    change ((materialize n z f m).val.set m (f m).val).look j z = _
    by_cases he : j = m
    · subst j
      simp [Tape.look, Tape.set, hn, hj]
    · have old := ih (by omega)
      have hlt : j < (materialize n z f m).val.len := by omega
      have hs : ((materialize n z f m).val.set m (f m).val).look j z =
          (materialize n z f m).val.look j z := by
        simp only [Tape.look, Tape.set, hlt, he, ↓reduceDIte, ↓reduceIte]
      rw [hs, old]
      have hc : (j < m+1) ↔ j < m := by omega
      simp only [hc]

theorem tab_work {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) :
    (Bill.tab n z f).work = 2+4*n+∑ j ∈ Finset.range n, (f j).work := by
  change (materialize n z f n).work + (1+n) = _
  rw [materialize_work]
  omega

theorem tab_peak {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) :
    (Bill.tab n z f).peak = max n ((Finset.range n).sup (fun j => (f j).peak)) := by
  change max (materialize n z f n).peak n = _
  rw [materialize_peak]
  omega

theorem tab_valid {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) :
    (Bill.tab n z f).valid ↔ ∀ j < n, (f j).valid :=
  materialize_valid n z f n

theorem tab_value {α : Type} (n : ℕ) (z : α) (f : ℕ → Bill α) :
    (Bill.tab n z f).val = Tape.tab n (fun j => (f j).val) := by
  have hn := materialize_len n z f n
  change (materialize n z f n).val = _
  generalize hv : (materialize n z f n).val = v at hn ⊢
  cases v with
  | mk len pos =>
    change len = n at hn
    subst len
    congr 1
    funext j
    have h := materialize_look n z f n (by omega) j.val j.isLt
    rw [hv] at h
    simpa [Tape.look, j.isLt, Tape.tab] using h

theorem update_value (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).val = v.set i x := by
  change (Bill.tab v.len t.blank
    (fun j => run (updateCell t) (((v,i),x),j))).val = _
  rw [tab_value]
  have hf : (fun j => (run (updateCell t) (((v,i),x),j)).val) =
      (fun j => if j = i then x else v.look j t.blank) := by
    funext j
    exact congrArg Bill.val (updateCell_run t v i x j)
  rw [hf]
  cases v with
  | mk len pos =>
    dsimp only [Tape.tab, Tape.set, Tape.len]
    congr 1
    funext j
    simp [Tape.look, j.isLt]

theorem update_valid (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).valid := by
  change ((run (updateLength t) ((v,i),x)).pass (fun n => Bill.tab n t.blank
    (fun j => run (updateCell t) (((v,i),x),j)))).valid
  rw [updateLength_run]
  change True ∧ (Bill.tab v.len t.blank
    (fun j => run (updateCell t) (((v,i),x),j))).valid
  refine ⟨trivial, (tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [updateCell_run]
  trivial

/-- Exact work, including all projections, tests, reads, allocation and loop work. -/
theorem update_work_sum (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).work =
      8+4*v.len+∑ j ∈ Finset.range v.len, if j = i then 25 else 31 := by
  change 5+(Bill.tab v.len t.blank
    (fun j => run (updateCell t) (((v,i),x),j))).work+1 = _
  rw [tab_work]
  have hf : (fun j => (run (updateCell t) (((v,i),x),j)).work) =
      (fun j => if j = i then 25 else 31) := by
    funext j
    exact congrArg Bill.work (updateCell_run t v i x j)
  rw [hf]
  omega

theorem update_work_linear (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).work + (if i < v.len then 6 else 0) =
      35*v.len+8 := by
  rw [update_work_sum]
  have hs : (∑ j ∈ Finset.range v.len, if j = i then 25 else 31) +
      (if i < v.len then 6 else 0) = 31*v.len := by
    have hc : ∑ j ∈ Finset.range v.len,
        ((if j = i then 25 else 31)+(if j = i then 6 else 0)) = 31*v.len := by
      calc
        _ = ∑ _j ∈ Finset.range v.len, 31 := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _ = _ := by simp [Nat.mul_comm]
    simpa [Finset.sum_add_distrib] using hc
  omega

theorem update_work_bounds (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    35*v.len+2 ≤ (run (update t) ((v,i),x)).work ∧
      (run (update t) ((v,i),x)).work ≤ 35*v.len+8 := by
  have h := update_work_linear t v i x
  split_ifs at h <;> omega

theorem update_work_at_zero (t : Ty) (v : Tape t.T) (x : t.T) (hv : 0 < v.len) :
    (run (update t) ((v,0),x)).work = 35*v.len+2 := by
  have h := update_work_linear t v 0 x
  simp only [hv, ↓reduceIte] at h
  omega

/-- Peak integers include allocation length and all natural-only equality tests. -/
theorem update_peak_sup (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).peak =
      max v.len ((Finset.range v.len).sup (distance i)) := by
  change (((run (updateLength t) ((v,i),x)).pass (fun n => Bill.tab n t.blank
    (fun j => run (updateCell t) (((v,i),x),j)))).pay 1 0).peak = _
  rw [updateLength_run]
  change max (max v.len
    (Bill.tab v.len t.blank (fun j => run (updateCell t) (((v,i),x),j))).peak) 0 = _
  rw [tab_peak]
  have hf : (fun j => (run (updateCell t) (((v,i),x),j)).peak) = distance i := by
    funext j
    exact congrArg Bill.peak (updateCell_run t v i x j)
  rw [hf]
  simp

theorem update_peak (t : Ty) (v : Tape t.T) (i : ℕ) (x : t.T) :
    (run (update t) ((v,i),x)).peak = if v.len = 0 then 0 else max v.len i := by
  rw [update_peak_sup]
  by_cases hv : v.len = 0
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    have hu : (Finset.range v.len).sup (distance i) ≤ max v.len i := by
      apply Finset.sup_le
      intro j hj
      have hj' := Finset.mem_range.mp hj
      unfold distance
      omega
    have hl : i ≤ (Finset.range v.len).sup (distance i) := by
      have hz : 0 ∈ Finset.range v.len := Finset.mem_range.mpr (by omega)
      have h := Finset.le_sup (f := distance i) hz
      simpa [distance] using h
    omega

/-- Even a single cell update has no constant work bound for this compiler. -/
theorem update_no_uniform_constant : ¬ ∃ c : ℕ, ∀ n : ℕ,
    (run (update w) ((Tape.tab n (fun _ => 0),0),1)).work ≤ c := by
  rintro ⟨c,h⟩
  have hb := (update_work_bounds w (Tape.tab (c+1) (fun _ => 0)) 0 1).1
  have hc := h (c+1)
  change 35*(c+1)+2 ≤ _ at hb
  omega

/-- A finite natural heap uses a natural presence flag and a natural payload. -/
def decodeNatCell (c : ℕ × ℕ) : Option ℕ := if c.1 = 0 then none else some c.2

def decodeNatHeap (v : Tape (ℕ × ℕ)) (j : ℕ) : Option ℕ :=
  decodeNatCell (v.look j (0,0))

theorem tape_set_look {α : Type} (v : Tape α) (i : ℕ) (x z : α) (j : ℕ) :
    (v.set i x).look j z = if j = i ∧ j < v.len then x else v.look j z := by
  by_cases he : j = i
  · subst j
    by_cases hi : i < v.len <;> simp [Tape.look, Tape.set, hi]
  · by_cases hj : j < v.len <;> simp [Tape.look, Tape.set, hj, he]

/-- This actual upstream code implements the same indexed natural heap write. -/
theorem update_nat_heap (v : Tape (ℕ × ℕ)) (i x : ℕ) (hi : i < v.len) :
    decodeNatHeap (run (update (p w w)) ((v,i),(1,x))).val =
      Function.update (decodeNatHeap v) i (some x) := by
  rw [update_value]
  funext j
  by_cases he : j = i
  · subst j
    simp [decodeNatHeap, tape_set_look, hi, decodeNatCell]
  · simp [decodeNatHeap, tape_set_look, he]

def storeNatState (s : UniformMachine.State) (address src : ℕ) : UniformMachine.State :=
  { UniformMachine.next s with
      natHeap := Function.update s.natHeap (s.natReg address) (some (s.natReg src)) }

/-- Our mutation is one instruction, regardless of the allocated heap size. -/
theorem our_storeNat_step (p : UniformMachine.Program) (n : ℕ) (x : Fin n → ℂ)
    (s : UniformMachine.State) (address src : ℕ)
    (h : p[s.pc]? = some (.storeNat address src)) :
    UniformMachine.step p n x s = .running (storeNatState s address src) := by
  simp [UniformMachine.step, h, storeNatState]

theorem our_storeNat_frame (s : UniformMachine.State) (address src : ℕ) :
    let u := storeNatState s address src
    u.pc = s.pc+1 ∧ u.natReg = s.natReg ∧ u.scalarReg = s.scalarReg ∧
      u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧
      (∀ j, j ≠ s.natReg address → u.natHeap j = s.natHeap j) := by
  dsimp [storeNatState, UniformMachine.next]
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro j hj
  exact Function.update_of_ne hj _ _

theorem our_storeNat_bound (B : ℕ) (s : UniformMachine.State) (address src : ℕ)
    (h : UniformMachine.WordBound B s) (hpc : s.pc+1 ≤ B) :
    UniformMachine.WordBound B (storeNatState s address src) := by
  rcases h with ⟨_,hr,hn,hs,ho,hd⟩
  refine ⟨hpc,hr,?_,hs,ho,hd⟩
  intro j v hv
  change Function.update s.natHeap (s.natReg address) (some (s.natReg src)) j = some v at hv
  by_cases he : j = s.natReg address
  · subst j
    simp only [Function.update_self, Option.some.injEq] at hv
    exact ⟨hr address, hv ▸ hr src⟩
  · rw [Function.update_of_ne he] at hv
    exact hn j v hv

/-- Store followed by halt: two charged instructions with a length-independent frame. -/
theorem our_storeNat_execution (B n : ℕ) (x : Fin n → ℂ) (s : UniformMachine.State)
    (address src : ℕ) (hs : s.pc = 0) (h : UniformMachine.WordBound B s) (hB : 1 ≤ B) :
    UniformMachine.BoundedExecution [.storeNat address src, .halt] n x B s 2
      (storeNatState s address src) := by
  apply UniformMachine.BoundedExecution.next h
  · exact our_storeNat_step [.storeNat address src, .halt] n x s address src (by simp [hs])
  · apply UniformMachine.BoundedExecution.halt (our_storeNat_bound B s address src h (by omega))
    simp [UniformMachine.step, storeNatState, UniformMachine.next, hs]

/-- Finite-heap agreement after the actual store, without a supplied write oracle. -/
theorem storeNat_simulation (s : UniformMachine.State) (address src : ℕ)
    (v : Tape (ℕ × ℕ)) (hv : decodeNatHeap v = s.natHeap)
    (hi : s.natReg address < v.len) :
    decodeNatHeap (run (update (p w w))
      ((v,s.natReg address),(1,s.natReg src))).val =
        (storeNatState s address src).natHeap := by
  rw [update_nat_heap v _ _ hi, hv]
  rfl

/-- There is no constant-factor store simulation bound for this fresh-tape compiler. -/
theorem store_compiler_no_constant_factor : ¬ ∃ c : ℕ, ∀ n : ℕ,
    (run (update (p w w)) ((Tape.tab n (fun _ => (0,0)),0),(1,1))).work ≤ c*1 := by
  rintro ⟨c,h⟩
  have hb := (update_work_bounds (p w w) (Tape.tab (c+1) (fun _ => (0,0))) 0 (1,1)).1
  have hc := h (c+1)
  change 35*(c+1)+2 ≤ _ at hb
  omega

end
end ExactFourierCircuits.ModelEquivalenceInterpreter
