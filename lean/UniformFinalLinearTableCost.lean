import UniformFinalActualClockCost
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalLinearTableCost
open UniformMachine UniformAllAxisSeedPreparation UniformFinalOuterCost UniformFinalClockCost
open UniformJointAllocation Filter Asymptotics
noncomputable section

/-- The certified amortized table allowance; axisCount includes the binary
axis, unlike the saved odd-prime count in register102. -/
def tableBudget(n:ℕ):ℕ:=60*(UniformInitialPreparation.len n+axisCount n+1)
lemma tableBudget_bound(n:ℕ)(hn:0<n):tableBudget n ≤ 480*n:=by
 have count:UniformInitialPreparation.ell n ≤ 2*n:=by
  have h:=UniformWorkingLength.firstExceed_bound n
  unfold UniformInitialPreparation.ell UniformWorkingLength.axisCount
  omega
 have length:=UniformWorkingLength.workingLength_upper hn
 change UniformInitialPreparation.len n < 4*n at length
 unfold tableBudget axisCount
 omega
lemma tableBudget_isBigO_input:
 (fun n:ℕ=>(tableBudget n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=by
 apply IsBigO.of_bound 480
 filter_upwards[eventually_ge_atTop (1:ℕ)] with n hn
 have b:(tableBudget n:ℝ) ≤ 480*(n:ℝ):=by exact_mod_cast tableBudget_bound n (show 0<n by omega)
 simpa only[Real.norm_of_nonneg (Nat.cast_nonneg _)] using b

/-- Closed arithmetic majorant for the actual20 stages, using the amortized
printer and the proved complete-clock envelope. -/
def finalBudget(c:Constants)(W n:ℕ):ℝ:=
 (overhead c W n:ℝ)+3*clockEnvelope W n+(tableBudget n:ℝ)+20
lemma finalBudget_isBigO_paper(c:Constants)(W:ℕ):
 finalBudget c W =O[atTop] asymptoticCost UniformExponent.theta:=by
 have header:(fun _n:ℕ=>(20:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=
  ((isLittleO_const_id_atTop (20:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
 exact total_with_clockEnvelope_isBigO_paper c W (fun _=>20) tableBudget header tableBudget_isBigO_input

lemma totalBudget_le_finalBudget(c:Constants)(W n:ℕ)(table clock:ℕ→ℕ)
 (tables:table n ≤ tableBudget n)(clocks:(clock n:ℝ) ≤ clockEnvelope W n):
 (totalBudget c W (fun _=>20) table clock n:ℝ) ≤ finalBudget c W n:=by
 rw[totalBudget_split]
 have table:(table n:ℝ) ≤ (tableBudget n:ℝ):=by exact_mod_cast tables
 unfold finalBudget
 push_cast
 linarith only[table,clocks]

/-- The final machine-statement adapter has no supplied asymptotic estimate:
only the concrete fixed algorithm's real initial-state execution remains to
be supplied. Its word envelope and one-root order bounds stay explicit. -/
theorem of_execution(c:Constants)(W C:ℕ)(p:Program)(order:ℕ→ℕ)
 (orders:∀n,0<n→0<order n∧order n<1024*n^3)
 (execution:∀n,0<n→∀x:Fin n→ℂ,∃t:ℕ,∃s:State,
  BoundedExecution p n x (C*(n+2)^19+C) initial t s∧
  ComputesDFT n x s∧s.rootOrders=[order n]∧(t:ℝ) ≤ finalBudget c W n):
 UniformDFTStatement UniformExponent.theta:=
 UniformFinalStatementBridge.of_majorized_execution p C order (finalBudget c W) orders execution
  (finalBudget_isBigO_paper c W)

end
end ExactFourierCircuits.UniformFinalLinearTableCost
