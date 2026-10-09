import UniformGlobalCalendarSelectorCycle

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarSelector
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

def Source (D stride N : ℕ) (records : ℕ → ℕ × ℕ) (heap : ℕ → Option ℕ) : Prop :=
  ∀ j, j < N → heap (D + stride * j) = some (records j).1 ∧
    heap (D + stride * j + 6) = some (records j).2

/-- This scans every ordinal, preserving preparation order and every active entry. -/
def selected (D stride tick : ℕ) (records : ℕ → ℕ × ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | _, 0 => []
  | j, fuel + 1 =>
    if active tick (records j).1 (records j).2 then
      (D + stride * j, tick - (records j).1) :: selected D stride tick records (j + 1) fuel
    else selected D stride tick records (j + 1) fuel

def writeSelections (O : ℕ) : ℕ → List (ℕ × ℕ) → (ℕ → Option ℕ) → (ℕ → Option ℕ)
  | _, [], heap => heap
  | used, q :: qs, heap => writeSelections O (used + 1) qs (storeSelection O used q.1 q.2 heap)

lemma selected_length (D stride tick : ℕ) (records : ℕ → ℕ × ℕ) (j fuel : ℕ) :
    (selected D stride tick records j fuel).length ≤ fuel := by
  induction fuel generalizing j with
  | zero => simp [selected]
  | succ fuel ih =>
    simp only [selected]
    split_ifs
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih (j + 1)) 1
    · exact (ih (j + 1)).trans (by omega)

lemma storeSelection_low (O used address phase : ℕ) (heap : ℕ → Option ℕ)
    (a : ℕ) (ha : a < O) : storeSelection O used address phase heap a = heap a := by
  simp (disch := omega) [storeSelection]

lemma Source.storeSelection {D stride N O used address phase : ℕ}
    {records : ℕ → ℕ × ℕ} {heap : ℕ → Option ℕ}
    (h : Source D stride N records heap) (fresh : D + stride * N + 7 ≤ O) :
    Source D stride N records (storeSelection O used address phase heap) := by
  intro j hj
  have mul := Nat.mul_le_mul_left stride (Nat.le_of_lt hj)
  rw [storeSelection_low _ _ _ _ _ _ (by omega),storeSelection_low _ _ _ _ _ _ (by omega)]
  exact h j hj

/-- The complete actual loop filters all produced entry headers, with bounded
loads/stores/control. The source bank is retained by fresh-output geometry. -/
theorem loop {n D stride N tick O used j fuel B : ℕ} (x : Fin n → ℂ)
    (records : ℕ → ℕ × ℕ) (s : State) (h : Header D stride N tick O used j s)
    (pc : s.pc = 6) (wb : WordBound B s) (code : 30 ≤ B)
    (ending : j + fuel = N) (source : Source D stride N records s.natHeap)
    (sourceFit : D + stride * N + 7 ≤ B) (fresh : D + stride * N + 7 ≤ O)
    (values : ∀ k, k < N → (records k).1 + 28 ≤ B ∧ (records k).2 ≤ B)
    (outputFit : O + 2 * (used + fuel) ≤ B) :
    ∃ (ticks : ℕ) (u : State),
      BoundedRuns program n x B s ticks u ∧ ticks ≤ 21 * fuel + 1 ∧ u.pc = 29 ∧
      Header D stride N tick O (used + (selected D stride tick records j fuel).length) N u ∧
      u.natHeap = writeSelections O used (selected D stride tick records j fuel) s.natHeap := by
  induction fuel generalizing j used s with
  | zero =>
    have eq : j = N := by omega
    have haltBranch : step program n x s = .running (setPC s 29) := by
      simp [step,pc,code_6,h.index,h.count,eq,setPC]
    refine ⟨1,_,control_run program n B 29 x s wb (by omega) haltBranch,by omega,rfl,?_,?_⟩
    · change Header D stride N tick O (used + (selected D stride tick records j 0).length) N (setPC s 29)
      simpa only [selected,List.length_nil,Nat.add_zero,eq] using h.pc 29
    · rfl
  | succ fuel ih =>
    have index : j < N := by omega
    have mul := Nat.mul_le_mul_left stride (Nat.le_of_lt index)
    obtain ⟨ticks,a,run,cost,ap,ah,heap⟩ := cycle x s h pc wb code index (by omega)
      (values j index).1 (values j index).2 (by omega) (source j index).1 (source j index).2
    by_cases enabled : active tick (records j).1 (records j).2
    · simp only [ite_eq_left enabled] at ah heap
      have retained : Source D stride N records a.natHeap := by
        rw [heap]
        exact source.storeSelection fresh
      obtain ⟨more,u,tail,bound,up,uh,out⟩ := ih (used := used + 1) (j := j + 1) a ah ap
        run.final_bound (by omega) retained (by omega)
      refine ⟨ticks + more,u,run.trans tail,by omega,up,?_,?_⟩
      · simpa only [selected,ite_eq_left enabled,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using uh
      · simpa only [selected,ite_eq_left enabled,writeSelections,heap] using out
    · simp only [ite_eq_right enabled] at ah heap
      have retained : Source D stride N records a.natHeap := by rw [heap]; exact source
      obtain ⟨more,u,tail,bound,up,uh,out⟩ := ih (used := used) (j := j + 1) a ah ap
        run.final_bound (by omega) retained (by omega)
      refine ⟨ticks + more,u,run.trans tail,by omega,up,?_,?_⟩
      · simpa only [selected,ite_eq_right enabled] using uh
      · simpa only [selected,ite_eq_right enabled,heap] using out

structure Args (D stride N tick O used : ℕ) (s : State) : Prop where
  directory : s.natReg 6700 = D
  spacing : s.natReg 6701 = stride
  count : s.natReg 6702 = N
  tick : s.natReg 6703 = tick
  output : s.natReg 6704 = O
  used : s.natReg 6705 = used

lemma boot_header {D stride N tick O used : ℕ} {s : State}
    (h : Args D stride N tick O used s) : Header D stride N tick O used 0 (applyBlock boot s) := by
  constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.count,h.tick,h.output,h.used]

/-- Full thirty-instruction selector, including initialization and actual halt. -/
theorem execution {n D stride N tick O used B : ℕ} (x : Fin n → ℂ)
    (records : ℕ → ℕ × ℕ) (s : State) (args : Args D stride N tick O used s)
    (pc : s.pc = 0) (wb : WordBound B s) (code : 30 ≤ B)
    (source : Source D stride N records s.natHeap)
    (sourceFit : D + stride * N + 7 ≤ B) (fresh : D + stride * N + 7 ≤ O)
    (values : ∀ k, k < N → (records k).1 + 28 ≤ B ∧ (records k).2 ≤ B)
    (outputFit : O + 2 * (used + N) ≤ B) :
    ∃ (ticks : ℕ) (u : State), BoundedExecution program n x B s ticks u ∧ ticks ≤ 21 * N + 8 ∧
      Header D stride N tick O (used + (selected D stride tick records 0 N).length) N u ∧
      u.natHeap = writeSelections O used (selected D stride tick records 0 N) s.natHeap := by
  have bootRun := block_runs boot program 0 n B x s boot_code pc wb (by change 6 ≤ B; omega)
    (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
  let a := applyBlock boot s
  have ap : a.pc = 6 := by rw [applyBlock_pc,pc]; rfl
  obtain ⟨ticks,u,run,bound,up,uh,heap⟩ := loop (fuel := N) x records a (boot_header args) ap
    bootRun.final_bound code (by omega) source sourceFit fresh values outputFit
  have haltStep : step program n x u = .halted u := by simp [step,up,code_29]
  refine ⟨6 + ticks + 1,u,(bootRun.trans run).executes (.halt run.final_bound haltStep),by omega,uh,heap⟩

end
end ExactFourierCircuits.UniformGlobalCalendarSelector
