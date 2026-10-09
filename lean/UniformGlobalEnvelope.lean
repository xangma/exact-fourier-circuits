import UniformBoundedAssembly
import UniformAllAxisConjugatePreparation

/-!
# Polynomial words and charged scalar preparation

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, §5.4, PDF pp. 23–24
(`thm:main`, `eq:main-bound`). Polynomial envelope enlargement is implementation
bookkeeping for the paper's O(log(n+2))-bit address words; it preserves every
transition and tick. The preparation estimates use the local polynomial
compiler of Proposition 3.1, PDF p. 12, at the small selected radices.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalEnvelope
open UniformMachine UniformAssembly Filter Asymptotics
noncomputable section

/-- A fixed program and its fixed auxiliary multiplicity can be absorbed in a
single polynomial word bound, including for the smallest positive input. -/
theorem polynomial_envelope (C d n : ℕ) (hn : 0<n) :
    C*(n+2)^d+C ≤ (n+2)^(2*C+d) := by
  have hb : 1<n+2 := by omega
  have hpow : 2*C ≤ (n+2)^(2*C) := (Nat.lt_pow_self hb).le
  have hone : 1≤(n+2)^d := Nat.one_le_pow d _ (by omega)
  calc
    C*(n+2)^d+C ≤ (2*C)*(n+2)^d := by nlinarith
    _ ≤ (n+2)^(2*C)*(n+2)^d := Nat.mul_le_mul_right _ hpow
    _ = (n+2)^(2*C+d) := (Nat.pow_add _ _ _).symm

theorem positive_degree (C : ℕ) : 0<2*C+19 := by omega

/- §5.4, PDF p. 24: changing the proof's upper bound changes neither
the actual program nor its execution states. -/
theorem execution_mono {p : Program} {n B B' t : ℕ} {x : Fin n→ℂ}
    {s u : State} (h : BoundedExecution p n x B s t u) (hle : B≤B') :
    BoundedExecution p n x B' s t u := by
  induction h with
  | halt hb hh=>exact .halt (UniformAssembly.wordBound_mono hle hb) hh
  | next hb hh _ ih=>exact .next (UniformAssembly.wordBound_mono hle hb) hh ih

theorem runs_mono {p : Program} {n B B' t : ℕ} {x : Fin n→ℂ}
    {s u : State} (h : BoundedRuns p n x B s t u) (hle : B≤B') :
    BoundedRuns p n x B' s t u := by
  induction h with
  | refl hb=>exact .refl (UniformAssembly.wordBound_mono hle hb)
  | next hb hh _ ih=>exact .next (UniformAssembly.wordBound_mono hle hb) hh ih

/- §5.4, PDF p. 23: the prepared scalars and their schedule compilation
cost only a fixed power of log n, absorbed by the total charged bound. -/
theorem conjugateBudget_isLittleO_input :
    (fun n : ℕ=>(UniformAllAxisConjugatePreparation.preparationBudget n:ℝ)) =o[atTop]
      (fun n : ℕ=>(n:ℝ)) := by
  have hlog : (fun n : ℕ=>Real.log (n:ℝ)^5) =o[atTop] (fun n : ℕ=>(n:ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact UniformAllAxisConjugatePreparation.budget_isBigO_log_five.trans_isLittleO hlog

/-- The executed original and conjugate all-axis preparations, including their
halts, have linear total overhead. -/
theorem fullPreparationBudget_isBigO_input :
    (fun n : ℕ=>(UniformAllAxisConjugatePreparation.fullBudget n:ℝ)) =O[atTop]
      (fun n : ℕ=>(n:ℝ)) := by
  have hc : (fun _n : ℕ=>(1:ℝ)) =O[atTop] (fun n : ℕ=>(n:ℝ)) :=
    ((isLittleO_const_id_atTop (1:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [UniformAllAxisConjugatePreparation.fullBudget,Nat.cast_add,Nat.cast_one] using
    (UniformAllAxisSeedCost.fullBudget_isBigO_input.add conjugateBudget_isLittleO_input.isBigO).add hc

end
end ExactFourierCircuits.UniformGlobalEnvelope
