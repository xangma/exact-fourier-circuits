import UniformFinalClockCost
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStatementBridge
open UniformMachine Filter Asymptotics
noncomputable section

lemma paper_eventually_nonneg(theta:ℝ):
 ∀ᶠn:ℕ in atTop,0 ≤ asymptoticCost theta n:=by
 have logs:Tendsto (fun n:ℕ=>Real.log (n:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
 have doubleLogs:Tendsto (fun n:ℕ=>Real.log (Real.log (n:ℝ))) atTop atTop:=
  Real.tendsto_log_atTop.comp logs
 filter_upwards[logs.eventually (eventually_ge_atTop (0:ℝ)),
  doubleLogs.eventually (eventually_ge_atTop (0:ℝ))] with n h1 h2
 unfold asymptoticCost
 exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg h1 _)) (Real.rpow_nonneg h2 _)

/-- Convert the proved asymptotic estimate to the positive constant and
threshold required by the machine statement. -/
theorem eventual_runtime_bound(theta:ℝ)(budget:ℕ→ℝ)
 (bound:budget =O[atTop] asymptoticCost theta):
 ∃K:ℝ,0<K∧∃N:ℕ,3 ≤ N∧∀n,N ≤ n→budget n ≤ K*asymptoticCost theta n:=by
 obtain ⟨c,hc⟩:=bound.bound
 let K:=|c|+1
 have positive:0<K:=by dsimp[K];positivity
 have large:∀ᶠn:ℕ in atTop,budget n ≤ K*asymptoticCost theta n:=by
  filter_upwards[hc,paper_eventually_nonneg theta] with n hn hp
  have compare:c ≤ K:=by dsimp[K];linarith[le_abs_self c]
  rw[Real.norm_of_nonneg hp] at hn
  exact (le_abs_self (budget n)).trans (hn.trans (mul_le_mul_of_nonneg_right compare hp))
 obtain ⟨N,hN⟩:=eventually_atTop.mp large
 exact ⟨K,positive,max N 3,le_max_right _ _,fun n hn=>hN n ((le_max_left _ _).trans hn)⟩

/-- The actual common fixed-program envelope is absorbed without changing
any run or its charged instruction count. -/
lemma execution_polynomial{p:Program}{n t C:ℕ}{x:Fin n→ℂ}{s u:State}(hn:0<n)
 (run:BoundedExecution p n x (C*(n+2)^19+C) s t u):
 BoundedExecution p n x ((n+2)^(2*C+19)) s t u:=
 UniformGlobalEnvelope.execution_mono run (UniformGlobalEnvelope.polynomial_envelope C 19 n hn)

/-- Final logical adapter, deliberately conditional on the real initial-state
execution and its proved charged majorant. The root order is fixed before the
input array is quantified. This does not assert that the assembled algorithm
has already supplied those operational facts. -/
theorem of_majorized_execution(p:Program)(C:ℕ)(order:ℕ→ℕ)(budget:ℕ→ℝ)
 (orders:∀n,0<n→0<order n∧order n<1024*n^3)
 (execution:∀n,0<n→∀x:Fin n→ℂ,∃t:ℕ,∃s:State,
  BoundedExecution p n x (C*(n+2)^19+C) initial t s∧
  ComputesDFT n x s∧s.rootOrders=[order n]∧(t:ℝ) ≤ budget n)
 (cost:budget =O[atTop] asymptoticCost UniformExponent.theta):
 UniformDFTStatement UniformExponent.theta:=by
 obtain ⟨K,hK,N,hN,large⟩:=eventual_runtime_bound UniformExponent.theta budget cost
 refine ⟨p,K,hK,N,2*C+19,hN,UniformGlobalEnvelope.positive_degree C,?_⟩
 intro n hn
 refine ⟨order n,(orders n hn).1,(orders n hn).2,?_⟩
 intro x
 obtain ⟨t,s,run,answer,roots,cheap⟩:=execution n hn x
 exact ⟨t,s,execution_polynomial hn run,answer,roots,
  fun h=>cheap.trans (large n h)⟩

end
end ExactFourierCircuits.UniformFinalStatementBridge
