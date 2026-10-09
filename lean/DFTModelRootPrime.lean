import DFTModelRootOrder

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM Ty
noncomputable section

def remainder : Prog false (p w w) w :=
  .comp (.fork (.atom .fst) (.atom .snd)) (.atom (.int .mod))

def increment : Prog false (p w w) (p w w) :=
  .fork (.atom .fst)
    (.comp (.fork (.atom .snd) (.atom (.lit 1))) (.atom (.int .add)))

def trialBase : Prog false (p w w) w := .atom (.lit 1)

def trialBody : Code false (some (p w w, w)) (p w w) w :=
  .ifz (.importClosed remainder) (.atom (.lit 0))
    (.comp (.importClosed increment) .call)

def trialAux (fuel candidate divisor : ℕ) : Bill ℕ :=
  depthRun (trialBase.run ()) (trialBody.run) fuel (candidate, divisor)

theorem trialAux_zero (p d : ℕ) : trialAux 0 p d = ⟨1, 2, 1, True⟩ := rfl

theorem trialAux_stop (fuel p d : ℕ) (h : p % d = 0) :
    trialAux (fuel + 1) p d = ⟨0, 9, fuel + 1, True⟩ := by
  simp [trialAux, depthRun, trialBase, trialBody, remainder, Code.run, Atom.run,
    NOp.run, Bill.word, Bill.one, Bill.pass, Bill.pay, h]

theorem trialAux_go (fuel p d : ℕ) (h : p % d ≠ 0) :
    trialAux (fuel + 1) p d =
      ⟨(trialAux fuel p (d + 1)).val,
       (trialAux fuel p (d + 1)).work + 18,
       max (p % d) (max (d + 1) (max (trialAux fuel p (d + 1)).peak (fuel + 1))),
       (trialAux fuel p (d + 1)).valid⟩ := by
  simp [trialAux, depthRun, trialBase, trialBody, remainder, increment, Code.run,
    Atom.run, NOp.run, Bill.word, Bill.one, Bill.pass, Bill.pay, h,
    Nat.add_comm, Nat.add_left_comm, max_comm, max_left_comm]
  omega

theorem trialAux_spec (p d f P : ℕ) (hd : 2 ≤ d) (hdf : d + f ≤ P) (hp : p ≤ P) :
    (trialAux f p d).val = UniformPrimeMachine.boolCode
      (UniformWorkingPreparation.trialLoop p d f).value ∧
    (trialAux f p d).work ≤ 4 * UniformPrimeMachine.loopCost p d f ∧
    (trialAux f p d).peak ≤ max 2 P ∧ (trialAux f p d).valid := by
  induction f generalizing d with
  | zero =>
    rw [trialAux_zero]
    simp [UniformWorkingPreparation.trialLoop, UniformPrimeMachine.boolCode,
      UniformPrimeMachine.loopCost]
  | succ f ih =>
    by_cases hz : p % d = 0
    · rw [trialAux_stop _ _ _ hz]
      simp only [UniformWorkingPreparation.trialLoop, UniformPrimeMachine.loopCost,
        hz, ite_true, UniformPrimeMachine.boolCode, Bool.false_eq_true, ite_false]
      refine ⟨by trivial, by omega, ?_, True.intro⟩
      exact (show f + 1 ≤ P by omega).trans (le_max_right _ _)
    · obtain ⟨hv, hw, hpeak, hvalid⟩ := ih (d + 1) (by omega) (by omega)
      rw [trialAux_go _ _ _ hz]
      simp only [UniformWorkingPreparation.trialLoop, UniformPrimeMachine.loopCost,
        hz, ite_false]
      refine ⟨hv, by omega, ?_, hvalid⟩
      apply max_le
      · exact (Nat.mod_le _ _).trans (hp.trans (le_max_right _ _))
      · apply max_le
        · exact (show d + 1 ≤ P by omega).trans (le_max_right _ _)
        · exact max_le hpeak ((show f + 1 ≤ P by omega).trans (le_max_right _ _))

def trialSeed : Prog false w (p w (p w w)) :=
  .fork (.comp (.fork (.atom .id) (.atom (.lit 2))) (.atom (.int .sub)))
    (.fork (.atom .id) (.atom (.lit 2)))

def trial : Prog false w w := .comp trialSeed (.descend trialBase trialBody)

def small : Prog false w w :=
  .comp (.fork (.atom .id) (.atom (.lit 2))) (.atom (.int .lt))

/-- Consecutive trial division, with precisely the same stopping test as our RAM. -/
def prime : Prog false w w := .ifz small trial (.atom (.lit 0))

theorem prime_small (p : ℕ) (hp : p < 2) :
    run prime p = ⟨0, 7, 2, True⟩ := by
  simp [prime, small, Code.run, Atom.run, NOp.run, Bill.word, Bill.one,
    Bill.pass, Bill.pay, hp]

theorem prime_large (p : ℕ) (hp : ¬p < 2) :
    run prime p = (trialAux (p - 2) p 2).pay 17 (max 2 (p - 2)) := by
  simp [prime, small, trial, trialSeed, trialAux, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, hp, Nat.add_comm, Nat.add_left_comm,
    max_assoc, max_comm, max_left_comm]
  omega

theorem prime_spec (p : ℕ) :
    (run prime p).val = UniformPrimeMachine.boolCode (UniformWorkingPreparation.trialPrime p).value ∧
    (run prime p).work ≤ 4 * UniformPrimeMachine.totalCost p ∧
    (run prime p).peak ≤ max 2 p ∧ (run prime p).valid := by
  by_cases hp : p < 2
  · rw [prime_small p hp]
    simp [UniformWorkingPreparation.trialPrime, UniformPrimeMachine.boolCode,
      UniformPrimeMachine.totalCost, hp]
  · obtain ⟨hv, hw, hpeak, hvalid⟩ := trialAux_spec p 2 (p - 2) p (by decide) (by omega) le_rfl
    rw [prime_large p hp]
    simp only [Bill.pay, UniformWorkingPreparation.trialPrime, UniformPrimeMachine.totalCost,
      hp, ite_false]
    refine ⟨hv, by omega, ?_, hvalid⟩
    exact max_le hpeak (max_le_max (le_refl _) (Nat.sub_le _ _))

theorem prime_value_one_iff (p : ℕ) : (run prime p).val = 1 ↔ Nat.Prime p := by
  rw [(prime_spec p).1]
  simpa [UniformPrimeMachine.boolCode] using UniformWorkingPreparation.trialPrime_true p

end
end ExactFourierCircuits.DFTModelRoot
