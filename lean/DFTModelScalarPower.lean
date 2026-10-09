import ModelEquivalenceInterpreter
import UniformPowerMachine

set_option autoImplicit false

/-!
Charged prepared-scalar binary powering in the unchanged upstream language.
Paper §5.3, root extraction after (5.9): powers of the single supplied master
root are prepared scalars. One halving child is evaluated per nonzero exponent;
there is no table of length equal to the exponent and no new root request.
-/
namespace ExactFourierCircuits.DFTModelScalarPower
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w sc
abbrev RecPort : Port := some (Input, sc)
abbrev Joined := p Input sc

def base {r : Port} : Code false r Input sc := .atom .cone

def halfInput {r : Port} : Code false r Input Input :=
  .fork (.comp (.fork (.atom .fst) (.atom (.lit 2))) (.atom (.int .div)))
    (.atom .snd)

def square {r : Port} : Code false r Joined sc :=
  .comp (.fork (.atom .snd) (.atom .snd)) (.atom (.scale .scalar))

def parity {r : Port} : Code false r Joined w :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom (.lit 2)))
    (.atom (.int .mod))

def factor {r : Port} : Code false r Joined sc :=
  .ifz parity (.atom .cone) (.comp (.atom .fst) (.atom .snd))

def combine {r : Port} : Code false r Joined sc :=
  .comp (.fork square factor) (.atom (.scale .scalar))

def large : Code false RecPort Input sc :=
  .comp (.fork (.atom .id) (.comp halfInput .call)) combine

def step : Code false RecPort Input sc := .ifz (.atom .fst) base large

def program : Prog false Input sc :=
  .comp (.fork (.atom .fst) (.atom .id)) (.descend base step)

theorem halfInput_run {r : Port} (h : Handler r) (e : ℕ) (z : ℂ) :
    halfInput.run h (e,z) = ⟨(e/2,z),7,max 2 (e/2),True⟩ := by
  simp [halfInput, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word]

theorem combine_run {r : Port} (h : Handler r) (e : ℕ) (z v : ℂ) :
    combine.run h ((e,z),v) =
      ⟨v^2 * (if e%2=0 then 1 else z),
       if e%2=0 then 17 else 19,2,True⟩ := by
  by_cases he : e%2=0
  · simp [combine, square, factor, parity, Code.run, Atom.run, NOp.run,
      Bill.pass, Bill.pay, Bill.one, Bill.word, he, pow_two]
  · simp [combine, square, factor, parity, Code.run, Atom.run, NOp.run,
      Bill.pass, Bill.pay, Bill.one, Bill.word, he, pow_two]
    omega

attribute [local irreducible] halfInput combine large

theorem large_run (h : Handler RecPort) (e : ℕ) (z : ℂ) :
    large.run h (e,z) =
      ((h (e/2,z)).pass (fun v => combine.run h ((e,z),v))).pay 12 (max 2 (e/2)) := by
  simp only [large, Code.run, Atom.run]
  rw [halfInput_run]
  simp only [Bill.one, Bill.pass, Bill.pay]
  congr 1 <;> first | omega | simp

theorem step_zero (h : Handler RecPort) (z : ℂ) :
    step.run h (0,z) = ⟨1,3,0,True⟩ := by
  simp [step, base, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay]

theorem step_nonzero (h : Handler RecPort) (e : ℕ) (z : ℂ) (he : e≠0) :
    step.run h (e,z) = (large.run h (e,z)).pay 2 0 := by
  simp [step, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay, he]
  omega

def result (fuel e : ℕ) (z : ℂ) : Bill ℂ :=
  depthRun ((base (r := none)).run ()) step.run fuel (e,z)

theorem result_zero (e : ℕ) (z : ℂ) : result 0 e z = ⟨1,2,0,True⟩ := rfl

theorem result_succ_zero (fuel : ℕ) (z : ℂ) :
    result (fuel+1) 0 z = ⟨1,4,fuel+1,True⟩ := by
  change (step.run (fun x : Input.T => result fuel x.1 x.2) (0,z)).pay 1 (fuel+1) = _
  rw [step_zero]
  rfl

theorem result_succ_nonzero (fuel e : ℕ) (z : ℂ) (he : e≠0) :
    result (fuel+1) e z =
      (((result fuel (e/2) z).pass
        (fun v => (combine (r := RecPort)).run (fun x : Input.T => result fuel x.1 x.2) ((e,z),v))).pay
          14 (max 2 (e/2))).pay 1 (fuel+1) := by
  change (step.run (fun x : Input.T => result fuel x.1 x.2) (e,z)).pay 1 (fuel+1) = _
  rw [step_nonzero _ _ _ he, large_run]
  simp [Bill.pay, max_assoc, Nat.add_assoc]

theorem power_parity (z : ℂ) (e : ℕ) :
    (z^(e/2))^2 * (if e%2=0 then 1 else z) = z^e := by
  have hm : e%2=0 ∨ e%2=1 := by omega
  rcases hm with hm | hm
  · simp only [hm, ↓reduceIte, mul_one]
    rw [← pow_mul]
    congr 1
    omega
  · simp only [show ¬e%2=0 by omega, ↓reduceIte]
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega

theorem result_spec (fuel e : ℕ) (z : ℂ) (he : e≤fuel) :
    (result fuel e z).val = z^e ∧ (result fuel e z).valid ∧
    (result fuel e z).work ≤ 40*UniformPowerMachine.iterations e+4 ∧
    (result fuel e z).peak ≤ max fuel 2 := by
  induction fuel generalizing e with
  | zero =>
    have hz : e=0 := by omega
    subst e
    simp [result_zero, UniformPowerMachine.iterations_zero]
  | succ fuel ih =>
    by_cases hz : e=0
    · subst e
      simp [result_succ_zero, UniformPowerMachine.iterations_zero]
    · have hhalf : e/2≤fuel := by omega
      obtain ⟨hv,hvalid,hw,hp⟩ := ih (e/2) hhalf
      rw [result_succ_nonzero _ _ _ hz]
      simp only [Bill.pass, Bill.pay]
      rw [combine_run (r := RecPort) (fun x : Input.T => result fuel x.1 x.2)
        e z (result fuel (e/2) z).val]
      refine ⟨?_,?_,?_,?_⟩
      · change (result fuel (e/2) z).val ^ 2 * (if e%2=0 then 1 else z) = _
        rw [hv, power_parity]
      · exact ⟨hvalid,trivial⟩
      · change (result fuel (e/2) z).work+(if e%2=0 then 17 else 19)+14+1 ≤ _
        rw [UniformPowerMachine.iterations_step e hz]
        split <;> omega
      · change max (max (max (result fuel (e/2) z).peak 2) (max 2 (e/2))) (fuel+1) ≤ _
        omega

theorem program_run (e : ℕ) (z : ℂ) :
    run program (e,z) = (result e e z).pay 5 e := by
  simp only [program, run, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay, result]
  simp only [zero_max, max_zero, true_and, and_true]
  congr 1
  omega

theorem program_value (e : ℕ) (z : ℂ) : (run program (e,z)).val=z^e := by
  rw [program_run]
  exact (result_spec e e z le_rfl).1

theorem program_valid (e : ℕ) (z : ℂ) : (run program (e,z)).valid := by
  rw [program_run]
  exact (result_spec e e z le_rfl).2.1

theorem program_work (e : ℕ) (z : ℂ) :
    (run program (e,z)).work ≤ 40*(Nat.log2 (e+1)+1)+9 := by
  rw [program_run]
  change (result e e z).work+5 ≤ _
  have h := (result_spec e e z le_rfl).2.2.1
  have log := UniformPowerMachine.iterations_log_succ_bound e
  omega

theorem program_peak (e : ℕ) (z : ℂ) : (run program (e,z)).peak ≤ e+2 := by
  rw [program_run]
  change max (result e e z).peak e ≤ _
  have h := (result_spec e e z le_rfl).2.2.2
  omega

/-- Compare charged work directly with the actual source binary-power loop. -/
theorem iterations_le_sourceCost (e : ℕ) :
    UniformPowerMachine.iterations e ≤ UniformPowerMachine.loopCost e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e=0
    · subst e
      rw [UniformPowerMachine.iterations_zero, UniformPowerMachine.loopCost_zero]
      omega
    · have h := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
      have hr : 1≤UniformPowerMachine.roundCost e := by
        unfold UniformPowerMachine.roundCost
        split <;> omega
      rw [UniformPowerMachine.iterations_step e he, UniformPowerMachine.loopCost_step e he]
      omega

theorem program_work_source (e : ℕ) (z : ℂ) :
    (run program (e,z)).work ≤ 40*UniformPowerMachine.loopCost e+9 := by
  rw [program_run]
  change (result e e z).work+5 ≤ _
  have h := (result_spec e e z le_rfl).2.2.1
  have hs := iterations_le_sourceCost e
  omega

end
end ExactFourierCircuits.DFTModelScalarPower
