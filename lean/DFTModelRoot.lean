import UniformMasterRootMachine
import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM
open Ty
noncomputable section

def less : Prog false (p w w) w :=
  .comp (.fork (.atom .snd) (.atom .fst)) (.atom (.int .lt))

def double : Prog false (p w w) (p w w) :=
  .fork (.atom .fst)
    (.comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .mul)))

def base : Prog false (p w w) w := .atom .snd

def body : Code false (some (p w w, w)) (p w w) w :=
  .ifz (.importClosed less) (.atom .snd)
    (.comp (.importClosed double) .call)

def aux (fuel target factor : ℕ) : Bill ℕ :=
  depthRun (base.run ()) (body.run) fuel (target, factor)

theorem aux_stop (fuel target factor : ℕ) (h : ¬factor < target) :
    aux (fuel + 1) target factor = ⟨factor, 9, fuel + 1, True⟩ := by
  simp [aux, depthRun, base, body, less, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, h]

theorem aux_go (fuel target factor : ℕ) (h : factor < target) :
    aux (fuel + 1) target factor =
      ⟨(aux fuel target (factor * 2)).val,
       (aux fuel target (factor * 2)).work + 18,
       max (max 2 (factor * 2)) (max (aux fuel target (factor * 2)).peak (fuel + 1)),
       (aux fuel target (factor * 2)).valid⟩ := by
  simp [aux, depthRun, base, body, less, double, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, h, Nat.add_comm,
    Nat.add_left_comm, max_assoc, max_comm, max_left_comm]
  omega


theorem rootBits_le_target (L : ℕ) : UniformBatching.rootBits L ≤ 16 * L :=
  UniformBatching.rootBits_le (Nat.lt_pow_self (by decide : 1 < 2)).le

theorem aux_spec (L : ℕ) (hL : 0 < L) (fuel e : ℕ)
    (he : e ≤ UniformBatching.rootBits L)
    (hf : UniformBatching.rootBits L - e < fuel) :
    (aux fuel (16 * L) (2 ^ e)).val = UniformBatching.rootFactor L ∧
    (aux fuel (16 * L) (2 ^ e)).work = 18 * (UniformBatching.rootBits L - e) + 9 ∧
    (aux fuel (16 * L) (2 ^ e)).peak ≤ max fuel (32 * L) ∧
    (aux fuel (16 * L) (2 ^ e)).valid := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    by_cases hend : e = UniformBatching.rootBits L
    · have hs : ¬ 2 ^ e < 16 * L := by
        rw [hend]
        exact Nat.not_lt.mpr (UniformBatching.rootFactor_lower L)
      rw [aux_stop fuel _ _ hs]
      simp [hend, UniformBatching.rootFactor ]
    · have hel : e < UniformBatching.rootBits L := by omega
      have hgo := UniformMasterRootMachine.rootFactor_minimal L e hel
      obtain ⟨hv, hw, hp, hd⟩ := ih (e + 1) (by omega) (by omega)
      rw [pow_succ] at hv hw hp hd
      rw [aux_go fuel _ _ hgo]
      refine ⟨hv, ?_, ?_, hd⟩
      · dsimp only
        rw [hw]
        omega
      · dsimp only
        have h2 : 2 ≤ 32 * L := by omega
        have hf2 : 2 ^ e * 2 ≤ 32 * L := by
          rw [← pow_succ]
          exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show e + 1 ≤ UniformBatching.rootBits L by omega)).trans
            (UniformBatching.rootFactor_upper hL).le
        apply max_le
        · exact (max_le h2 hf2).trans (le_max_right _ _)
        · apply max_le
          · exact hp.trans (max_le_max (by omega) (le_refl _))
          · exact le_max_left _ _


/-- Fuel is computed by integer addition; it is not a free logarithm. -/
def seed : Prog false w (p w (p w w)) :=
  .fork (.comp (.fork (.atom .id) (.atom (.lit 1))) (.atom (.int .add)))
    (.fork (.atom .id) (.atom (.lit 1)))

def ceiling : Prog false w w := .comp seed (.descend base body)

def target : Prog false w w :=
  .comp (.fork (.atom (.lit 16)) (.atom .id)) (.atom (.int .mul))

def factor : Prog false w w := .comp target ceiling

theorem ceiling_run (t : ℕ) :
    run ceiling t = (aux (t + 1) t 1).pay 11 (t + 1) := by
  simp [ceiling, seed, aux, Code.run, Atom.run, NOp.run, Bill.word,
    Bill.one, Bill.pass, Bill.pay, Nat.add_assoc, max_comm]
  omega

theorem target_run (L : ℕ) : run target L = ⟨16 * L, 5, max 16 (16 * L), True⟩ := by
  simp [target, Code.run, Atom.run, NOp.run, Bill.word, Bill.one, Bill.pass, Bill.pay]

theorem factor_run (L : ℕ) :
    run factor L = ((run target L).pass (run ceiling)).pay 1 0 := rfl

theorem factor_spec (L : ℕ) (hL : 0 < L) :
    (run factor L).val = UniformBatching.rootFactor L ∧
    (run factor L).work = 18 * UniformBatching.rootBits L + 26 ∧
    (run factor L).peak ≤ 32 * L ∧ (run factor L).valid := by
  have ha := aux_spec L hL (16 * L + 1) 0 (Nat.zero_le _)
    (by have := rootBits_le_target L; omega)
  simp only [Nat.sub_zero, pow_zero] at ha
  have hc := ceiling_run (16 * L)
  have ht := target_run L
  rw [factor_run L, ht]
  dsimp only [Bill.pass]
  rw [hc]
  rcases ha with ⟨hv, hw, hp, hd⟩
  dsimp only [Bill.pass, Bill.pay]
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [hw]
    omega
  · have h16 : 16 ≤ 32 * L := by omega
    have htarget : 16 * L ≤ 32 * L := by omega
    have hfuel : 16 * L + 1 ≤ 32 * L := by omega
    have hpeak : (aux (16 * L + 1) (16 * L) 1).peak ≤ 32 * L :=
      hp.trans (max_le hfuel (le_refl _))
    exact max_le (max_le (max_le h16 htarget) (max_le hpeak hfuel)) (Nat.zero_le _)
  · exact ⟨True.intro, hd⟩

end
end ExactFourierCircuits.DFTModelRoot
