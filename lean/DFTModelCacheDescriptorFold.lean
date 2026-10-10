import DFTModelCacheDescriptorLog

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Charged left fold of a runtime rectangular enumeration. -/
def sumStep {s : Ty} (f : Prog false (p s w) w) : Prog false (p s (p w w)) w :=
  nat .add (.comp (.atom .snd) (.atom .snd))
    (.comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .fst))) f)
def sumProgram {s : Ty} (count : Prog false s w) (f : Prog false (p s w) w) :
    Prog false s w := .loop count (.atom (.lit 0)) (sumStep f)

theorem sumStep_run {s : Ty} (f : Prog false (p s w) w) (x : s.T) (i old : ℕ) :
    run (sumStep f) (x,(i,old))=
      ⟨old+(run f (x,i)).val,(run f (x,i)).work+12,
        max (run f (x,i)).peak (old+(run f (x,i)).val),(run f (x,i)).valid⟩ := by
  simp [sumStep,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,
    Nat.add_comm,Nat.add_left_comm]
  omega

def sumSteps {s : Ty} (f : Prog false (p s w) w) (x : s.T) (j : ℕ) : Bill ℕ :=
  Bill.steps 0 (fun i old=>run (sumStep f) (x,(i,old))) j

theorem sumSteps_value {s : Ty} (f : Prog false (p s w) w) (x : s.T) (j : ℕ) :
    (sumSteps f x j).val=∑i∈Finset.range j,(run f (x,i)).val := by
  induction j with
  | zero => simp [sumSteps,Bill.steps,Bill.one]
  | succ j ih =>
    change (run (sumStep f) (x,(j,(sumSteps f x j).val))).val=_
    rw [sumStep_run,ih,Finset.sum_range_succ]

theorem sumSteps_work {s : Ty} (f : Prog false (p s w) w) (x : s.T) (j : ℕ) :
    (sumSteps f x j).work=13*j+1+∑i∈Finset.range j,(run f (x,i)).work := by
  induction j with
  | zero => simp [sumSteps,Bill.steps,Bill.one]
  | succ j ih =>
    change (sumSteps f x j).work+(run (sumStep f) (x,(j,_))).work+1=_
    rw [sumStep_run,ih,Finset.sum_range_succ]
    dsimp only [Bill.work]
    omega

theorem sumSteps_valid {s : Ty} (f : Prog false (p s w) w) (x : s.T) (j : ℕ) :
    (sumSteps f x j).valid ↔ ∀i,i<j→(run f (x,i)).valid := by
  induction j with
  | zero => simp [sumSteps,Bill.steps,Bill.one]
  | succ j ih =>
    change ((sumSteps f x j).valid ∧ (run (sumStep f) (x,(j,_))).valid)↔_
    rw [sumStep_run,ih]
    dsimp only [Bill.valid]
    constructor
    · rintro ⟨h,hj⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hl|rfl
      · exact h i hl
      · exact hj
    · intro h
      exact ⟨fun i hi=>h i (by omega),h j (by omega)⟩

theorem sumSteps_peak {s : Ty} (f : Prog false (p s w) w) (x : s.T) (j C P : ℕ)
    (hv : ∀i,i<j→(run f (x,i)).val≤C)
    (hp : ∀i,i<j→(run f (x,i)).peak≤P) :
    (sumSteps f x j).peak ≤ max j (max P (j*C)) := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have old:=ih (fun i hi=>hv i (by omega)) (fun i hi=>hp i (by omega))
    have vb : (sumSteps f x j).val≤j*C := by
      rw [sumSteps_value]
      calc
        _ ≤ ∑_i∈Finset.range j,C := Finset.sum_le_sum (fun i hi=>hv i (by have h:=Finset.mem_range.mp hi;omega))
        _ = _ := by simp
    change max (max (sumSteps f x j).peak
      (run (sumStep f) (x,(j,_))).peak) (j+1)≤_
    rw [sumStep_run]
    change max (max (sumSteps f x j).peak
      (max (run f (x,j)).peak ((sumSteps f x j).val+(run f (x,j)).val))) (j+1)≤_
    have hj:=hv j (by omega)
    have hpp:=hp j (by omega)
    have mul : j*C≤(j+1)*C := Nat.mul_le_mul_right C (by omega)
    refine max_le (max_le ?_ (max_le ?_ ?_)) (le_max_left _ _)
    · exact old.trans (max_le_max (Nat.le_succ j) (max_le_max (le_refl P) mul))
    · exact hpp.trans ((le_max_left P ((j+1)*C)).trans (le_max_right _ _))
    · have sum : (sumSteps f x j).val+(run f (x,j)).val≤(j+1)*C := by
        rw [Nat.add_mul,Nat.one_mul]
        exact Nat.add_le_add vb hj
      exact sum.trans ((le_max_right P ((j+1)*C)).trans (le_max_right _ _))

theorem sumProgram_value {s : Ty} (count : Prog false s w)
    (f : Prog false (p s w) w) (x : s.T) :
    (run (sumProgram count f) x).val=
      ∑i∈Finset.range (run count x).val,(run f (x,i)).val := by
  exact sumSteps_value f x (run count x).val

theorem sumProgram_valid {s : Ty} (count : Prog false s w)
    (f : Prog false (p s w) w) (x : s.T)
    (hc : (run count x).valid) (hf : ∀i,i<(run count x).val→(run f (x,i)).valid) :
    (run (sumProgram count f) x).valid := by
  change (run count x).valid ∧ True ∧ (sumSteps f x (run count x).val).valid
  exact ⟨hc,trivial,(sumSteps_valid _ _ _).2 hf⟩

theorem sumProgram_work {s : Ty} (count : Prog false s w)
    (f : Prog false (p s w) w) (x : s.T) :
    (run (sumProgram count f) x).work=(run count x).work+
      13*(run count x).val+3+∑i∈Finset.range (run count x).val,(run f (x,i)).work := by
  change (run count x).work+(1+(sumSteps f x (run count x).val).work)+1=_
  rw [sumSteps_work]
  omega

theorem sumProgram_peak {s : Ty} (count : Prog false s w)
    (f : Prog false (p s w) w) (x : s.T) (C P : ℕ)
    (hv : ∀i,i<(run count x).val→(run f (x,i)).val≤C)
    (hp : ∀i,i<(run count x).val→(run f (x,i)).peak≤P) :
    (run (sumProgram count f) x).peak ≤
      max (run count x).peak (max (run count x).val (max P ((run count x).val*C))) := by
  change max (max (run count x).peak (max 0 (sumSteps f x (run count x).val).peak)) 0≤_
  simp only [zero_max,max_zero]
  exact max_le_max (le_refl _) (sumSteps_peak f x _ C P hv hp)

end
end ExactFourierCircuits.DFTModelCacheDescriptor
