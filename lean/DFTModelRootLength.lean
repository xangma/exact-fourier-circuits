import DFTModelRootSelection

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM Ty
noncomputable section

def twicePlusTwo : Prog false w w :=
  .comp (.fork (.comp (.fork (.atom (.lit 2)) (.atom .id)) (.atom (.int .mul)))
    (.atom (.lit 2))) (.atom (.int .add))
def limit : Prog false w w :=
  .comp (.fork
    (.comp (.fork (.atom (.lit 64))
      (.comp (.fork twicePlusTwo twicePlusTwo) (.atom (.int .mul)))) (.atom (.int .mul)))
    (.atom (.lit 1))) (.atom (.int .add))
def selectionInitial : Prog false w selectionState :=
  .fork (.atom .id) (.fork (.atom (.lit 3)) (.atom (.lit 1)))
def selectionSeed : Prog false w (p w selectionState) := .fork limit selectionInitial
def select : Prog false w w := .comp selectionSeed (.descend selectionBase selectionBody)

theorem limit_run (n : ℕ) :
    run limit n = ⟨UniformWorkingPreparation.candidateLimit n, 29,
      UniformWorkingPreparation.candidateLimit n, True⟩ := by
  have h2 : 2 ≤ 2 * n + 2 := by omega
  have h64 : 64 ≤ 64 * ((2 * n + 2) * (2 * n + 2)) := by nlinarith
  have hsmall : 2 * n + 2 ≤ 64 * ((2 * n + 2) * (2 * n + 2)) := by nlinarith
  simp [limit, twicePlusTwo, Code.run, Atom.run, NOp.run, Bill.word, Bill.one,
    Bill.pass, Bill.pay, UniformWorkingPreparation.candidateLimit, pow_two,
    max_comm]

theorem code_comp {a b c : Ty} (f : Prog false a b) (g : Prog false b c) (x : a.T) :
    run (.comp f g) x = ((run f x).pass (run g)).pay 1 0 := rfl

theorem code_fork {a b c : Ty} (f : Prog false a b) (g : Prog false a c) (x : a.T) :
    run (.fork f g) x = (run f x).pass (fun y => (run g x).pass (fun z => Bill.one (y, z))) := rfl

theorem selectionInitial_run (n : ℕ) : run selectionInitial n = ⟨(n, (3, 1)), 5, 3, True⟩ := by
  simp [selectionInitial, Code.run, Atom.run, Bill.one, Bill.word, Bill.pass]

theorem selectionDescend_run (fuel n p R : ℕ) :
    run (.descend selectionBase selectionBody : Prog false (Ty.p w selectionState) w)
      (fuel, (n, (p, R))) = (selectionAux fuel n p R).pay 1 fuel := rfl

theorem select_run (n : ℕ) : run select n =
    (selectionAux (UniformWorkingPreparation.candidateLimit n) n 3 1).pay 37
      (max 3 (UniformWorkingPreparation.candidateLimit n)) := by
  rw [select, code_comp, selectionSeed, code_fork, limit_run, selectionInitial_run]
  dsimp only [Bill.pass, Bill.one, Bill.pay]
  rw [selectionDescend_run]
  simp [Bill.pay, Nat.add_comm, Nat.add_left_comm, max_assoc, max_comm, max_left_comm]
  omega

def selectionPeak (n : ℕ) : ℕ :=
  2 * n * (3 + UniformWorkingPreparation.candidateLimit n) +
    UniformWorkingPreparation.candidateLimit n + 64

theorem select_spec (n : ℕ) (hn : 0 < n) :
    (run select n).val = UniformWorkingLength.oddProduct n ∧
    (run select n).work ≤ 6 * (UniformWorkingPreparation.selectPrefix n).cost ∧
    (run select n).peak ≤ selectionPeak n ∧ (run select n).valid := by
  have hs := selectionAux_spec n hn 3 0 1 (UniformWorkingPreparation.candidateLimit n)
    (selectionPeak n) (by omega) (by unfold selectionPeak; omega)
    (by unfold selectionPeak; omega) (by unfold selectionPeak; omega)
  obtain ⟨hv, hw, hp, hd⟩ := hs
  have hprefix := (UniformWorkingPreparation.selectPrefix_spec hn).1
  change (UniformWorkingPreparation.selectLoop n 3 0 1
    (UniformWorkingPreparation.candidateLimit n)).value = _ at hprefix
  rw [hprefix] at hv
  rw [select_run]
  dsimp only [Bill.pay, selectedProduct] at hv ⊢
  refine ⟨hv, ?_, ?_, hd⟩
  · change _ ≤ 6 * ((UniformWorkingPreparation.selectLoop n 3 0 1
      (UniformWorkingPreparation.candidateLimit n)).cost + 12)
    omega
  · exact max_le hp (max_le (by unfold selectionPeak; omega) (by unfold selectionPeak; omega))

def twice : Prog false (p w w) w :=
  .comp (.fork (.atom (.lit 2)) (.atom .fst)) (.atom (.int .mul))
def paddingSeed : Prog false (p w w) (p w (p w w)) :=
  .fork (.comp (.fork twice (.atom (.lit 1))) (.atom (.int .add)))
    (.fork twice (.atom .snd))
def padding : Prog false (p w w) w := .comp paddingSeed (.descend base body)

theorem padding_run (n R : ℕ) : run padding (n, R) =
    (aux (2 * n + 1) (2 * n) R).pay 19 (max 2 (2 * n + 1)) := by
  simp [padding, paddingSeed, twice, aux, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, Nat.add_comm, Nat.add_left_comm,
    max_assoc, max_comm, max_left_comm]
  omega

theorem paddingAux_spec (n : ℕ) (hn : 0 < n) (fuel e : ℕ)
    (he : e ≤ UniformWorkingLength.doublingExponent n)
    (hf : UniformWorkingLength.doublingExponent n - e < fuel) :
    (aux fuel (2 * n) (UniformWorkingLength.oddProduct n * 2 ^ e)).val =
      UniformWorkingLength.workingLength n ∧
    (aux fuel (2 * n) (UniformWorkingLength.oddProduct n * 2 ^ e)).work =
      18 * (UniformWorkingLength.doublingExponent n - e) + 9 ∧
    (aux fuel (2 * n) (UniformWorkingLength.oddProduct n * 2 ^ e)).peak ≤ max fuel (4 * n) ∧
    (aux fuel (2 * n) (UniformWorkingLength.oddProduct n * 2 ^ e)).valid := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    by_cases hend : e = UniformWorkingLength.doublingExponent n
    · have hs : ¬UniformWorkingLength.oddProduct n * 2 ^ e < 2 * n := by
        rw [hend]
        exact Nat.not_lt.mpr (UniformWorkingLength.workingLength_lower n)
      rw [aux_stop fuel _ _ hs]
      simp [hend, UniformWorkingLength.workingLength, UniformWorkingLength.binaryFactor]
    · have hel : e < UniformWorkingLength.doublingExponent n := by omega
      have hgo := UniformWorkingLength.doubling_minimal n e hel
      obtain ⟨hv, hw, hp, hd⟩ := ih (e + 1) (by omega) (by omega)
      simp only [pow_succ, ← Nat.mul_assoc] at hv hw hp hd
      rw [aux_go fuel _ _ hgo]
      refine ⟨hv, ?_, ?_, hd⟩
      · dsimp only
        rw [hw]
        omega
      · dsimp only
        have hfactor : UniformWorkingLength.oddProduct n * 2 ^ e * 2 ≤ 4 * n := by
          calc
            _ = UniformWorkingLength.oddProduct n * 2 ^ (e + 1) := by rw [pow_succ, Nat.mul_assoc]
            _ ≤ UniformWorkingLength.workingLength n :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
            _ ≤ 4 * n := (UniformWorkingLength.workingLength_upper hn).le
        exact max_le ((max_le (by omega) hfactor).trans (le_max_right _ _))
          (max_le (hp.trans (max_le_max (by omega) (le_refl _))) (le_max_left _ _))

theorem padding_spec (n : ℕ) (hn : 0 < n) :
    (run padding (n, UniformWorkingLength.oddProduct n)).val = UniformWorkingLength.workingLength n ∧
    (run padding (n, UniformWorkingLength.oddProduct n)).work =
      18 * UniformWorkingLength.doublingExponent n + 28 ∧
    (run padding (n, UniformWorkingLength.oddProduct n)).peak ≤ 4 * n ∧
    (run padding (n, UniformWorkingLength.oddProduct n)).valid := by
  obtain ⟨hv, hw, hp, hd⟩ := paddingAux_spec n hn (2 * n + 1) 0 (Nat.zero_le _)
    (by have := UniformWorkingPreparation.doublingExponent_bound n; omega)
  simp only [pow_zero, Nat.mul_one, Nat.sub_zero] at hv hw hp hd
  rw [padding_run]
  dsimp only [Bill.pay]
  refine ⟨hv, by omega, ?_, hd⟩
  exact max_le (hp.trans (max_le (by omega) le_rfl)) (max_le (by omega) (by omega))

def workingLength : Prog false w w := .comp (.fork (.atom .id) select) padding

theorem workingLength_bill (n : ℕ) : run workingLength n =
    (((run select n).pass (fun R => Bill.one (n, R))).pass (run padding)).pay 2 0 := by
  rw [workingLength, code_comp, code_fork]
  change (((Bill.one n).pass (fun y => (run select n).pass (fun z => Bill.one (y, z)))).pass
    (run padding)).pay 1 0 = _
  simp [Bill.one, Bill.pass, Bill.pay, Nat.add_comm]
  omega

theorem workingLength_spec (n : ℕ) (hn : 0 < n) :
    (run workingLength n).val = UniformWorkingLength.workingLength n ∧
    (run workingLength n).work ≤ 6 * UniformWorkingCompletion.preparationBudget n ∧
    (run workingLength n).peak ≤ max (selectionPeak n) (4 * n) ∧
    (run workingLength n).valid := by
  obtain ⟨sv, sw, sp, sd⟩ := select_spec n hn
  obtain ⟨pv, pw, pp, pd⟩ := padding_spec n hn
  rw [workingLength_bill]
  generalize hs : run select n = sel at *
  generalize hf : run padding = pad at *
  dsimp only [Bill.pass, Bill.one, Bill.pay]
  simp only [Nat.max_zero]
  rw [sv]
  refine ⟨pv, ?_, max_le (sp.trans (le_max_left _ _)) (pp.trans (le_max_right _ _)), ⟨⟨sd, True.intro⟩, pd⟩⟩
  have hp := UniformWorkingPreparation.selectPrefix_cost_polynomial hn
  have hc := UniformWorkingCompletion.completion_cost_bound hn
  rw [pw]
  unfold UniformWorkingCompletion.preparationBudget
  omega

end
end ExactFourierCircuits.DFTModelRoot
