import UniformFinalClockOverhead
import UniformFinalOuterCost
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockCost
open UniformMachine UniformAllAxisSeedPreparation UniformFinalClockOverhead
open UniformJointAllocation UniformJointConditionalKernelContext Filter Asymptotics
noncomputable section

/-- The extra actual147 diagonal, its copy, and the charged continuation. -/
def diagonalBudget (W n:ℕ):ℕ:=
 (130*W+100)*UniformInitialPreparation.len n*UniformFourierClockBounds.horizon n
lemma diagonalBudget_bound (W n:ℕ)(hn:0<n):
 (diagonalBudget W n:ℝ) ≤ ((130*W+100:ℕ):ℝ)*UniformActualCalendarLogBounds.horizonUnit*
 UniformAsymptotics.workingCost UniformExponent.theta n:=by
 have clocks:=UniformActualCalendarLogBounds.horizon_bound hn
 have one:=UniformNetworkCost.exponentFactor_one_le (UniformWorkingLength.axisCount n)
 have log:0 ≤ UniformNetworkCost.logFactor n^4:=
  pow_nonneg (le_trans zero_le_one (UniformNetworkCost.logFactor_one_le n)) 4
 have length:0 ≤ (UniformWorkingLength.workingLength n:ℝ):=Nat.cast_nonneg _
 have scalar:0 ≤ ((130*W+100:ℕ):ℝ):=Nat.cast_nonneg _
 have scale:=mul_le_mul_of_nonneg_left clocks
  (mul_nonneg scalar length)
 have grow:=mul_le_mul_of_nonneg_right one
  (mul_nonneg (mul_nonneg scalar (Nat.cast_nonneg UniformActualCalendarLogBounds.horizonUnit))
   (mul_nonneg length log))
 unfold diagonalBudget UniformAsymptotics.workingCost
 change (((130*W+100)*UniformWorkingLength.workingLength n*UniformFourierClockBounds.horizon n:ℕ):ℝ) ≤ _
 push_cast at scale grow ⊢
 unfold UniformNetworkCost.logFactor at scale grow
 push_cast at scale grow
 nlinarith only[scale,grow]

lemma diagonalBudget_isBigO_paper(W:ℕ):
 (fun n:ℕ=>(diagonalBudget W n:ℝ)) =O[atTop] asymptoticCost UniformExponent.theta:=by
 have h:(fun n:ℕ=>(diagonalBudget W n:ℝ)) =O[atTop]
  UniformAsymptotics.workingCost UniformExponent.theta:=by
  apply IsBigO.of_bound (((130*W+100:ℕ):ℝ)*UniformActualCalendarLogBounds.horizonUnit)
  filter_upwards[eventually_ge_atTop (1:ℕ)] with n hn
  rw[Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (UniformNetworkCost.workingCost_nonneg n)]
  exact diagonalBudget_bound W n (by omega)
 exact h.trans UniformAsymptotics.workingCost_isBigO_paper

/-- Complete-clock majorant: actual recursive kernel envelope plus proved
linear diagonal cost and the real axis-scan allowance. -/
def clockEnvelope(W n:ℕ):ℝ:=(clockScanBudget n:ℝ)+
 UniformActualCalendarAsymptotics.kernelEnvelope W n+(diagonalBudget W n:ℝ)
lemma clockEnvelope_nonneg(W n:ℕ):0 ≤ clockEnvelope W n:=by
 unfold clockEnvelope
 exact add_nonneg (add_nonneg (Nat.cast_nonneg _)
  (UniformActualCalendarAsymptotics.kernelEnvelope_nonneg W n)) (Nat.cast_nonneg _)
theorem clockEnvelope_isBigO_paper(W:ℕ):
 clockEnvelope W =O[atTop] asymptoticCost UniformExponent.theta:=
 (((clockScanBudget_isLittleO_input.isBigO).trans UniformFinalOuterCost.input_isBigO_paper).add
  (UniformActualCalendarAsymptotics.kernelEnvelope_isBigO_paper W)).add
  (diagonalBudget_isBigO_paper W)

/-- The exact finite-loop cost shape supplied by the actual clock induction.
The function arguments here denote charged counts, not execution callbacks. -/
def loopBudget(n:ℕ)
 (prep selected:Fin (UniformFourierClockBounds.horizon n)→Fin (axisCount n)→ℕ)
 (kernel:Fin (UniformFourierClockBounds.horizon n)→ℕ):ℕ:=
 7+Finset.univ.sum (fun t :Fin (UniformFourierClockBounds.horizon n)=>
  8+Finset.univ.sum (fun j :Fin (axisCount n)=>
   prep t j+66*radix n j+233+selected t j*(9*radix n j+48))+kernel t)

lemma loopBudget_bound(n:ℕ)
 (prep selected:Fin (UniformFourierClockBounds.horizon n)→Fin (axisCount n)→ℕ)
 (kernel:Fin (UniformFourierClockBounds.horizon n)→ℕ)
 (axis:∀t j,prep t j+66*radix n j+233+selected t j*(9*radix n j+48) ≤ axisScanBudget (radix n j)):
 loopBudget n prep selected kernel ≤ clockScanBudget n+∑t,kernel t:=by
 have each(t:Fin (UniformFourierClockBounds.horizon n)):
  8+Finset.univ.sum (fun j :Fin (axisCount n)=>
   prep t j+66*radix n j+233+selected t j*(9*radix n j+48))+kernel t ≤
  8+axesScanBudget n+kernel t:=by
  have bound:=Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>axis t j)
  exact Nat.add_le_add_right (Nat.add_le_add_left bound 8) (kernel t)
 have bound:=Finset.sum_le_sum (fun t (_:t∈Finset.univ)=>each t)
 have arranged:=bound.trans_eq (show Finset.univ.sum (fun t :Fin (UniformFourierClockBounds.horizon n)=>
  8+axesScanBudget n+kernel t)=
  UniformFourierClockBounds.horizon n*(8+axesScanBudget n)+(∑ t,kernel t) by
   rw[Finset.sum_add_distrib]
   simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul])
 simpa only[loopBudget,clockScanBudget,Nat.add_assoc] using Nat.add_le_add_left arranged 7

/-- Real selected geometry instantiates the frozen actual recursive-kernel
bound. Only the independently measured axis and diagonal allowances remain
as hypotheses; no desired asymptotic estimate is assumed. -/
theorem actual_loop_bound(c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles)
 (physical:Fin (UniformFourierClockBounds.horizon n)→List UniformSectorPackingMachine.PhysicalAxis)
 (shape:∀t,PhysicalGeometry c n (physical t))
 (prep selected:Fin (UniformFourierClockBounds.horizon n)→Fin (axisCount n)→ℕ)
 (kernel:Fin (UniformFourierClockBounds.horizon n)→ℕ)
 (axis:∀t j,prep t j+66*radix n j+233+selected t j*(9*radix n j+48) ≤ axisScanBudget (radix n j))
 (diagonal:∀t,kernel t ≤
  UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles (physical t) (shape t))+
  (130*c.roles+100)*UniformInitialPreparation.len n):
 (loopBudget n prep selected kernel:ℝ) ≤ clockEnvelope c.roles n:=by
 have small:=loopBudget_bound n prep selected kernel axis
 have sum:=Finset.sum_le_sum (fun t (_:t∈Finset.univ)=>diagonal t)
 simp only[Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sum
 have numeric:(loopBudget n prep selected kernel:ℝ) ≤ (clockScanBudget n:ℝ)+
  ((∑t,UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles (physical t) (shape t))):ℝ)+
  (diagonalBudget c.roles n:ℝ):=by
  exact_mod_cast (small.trans (Nat.add_le_add_left sum (clockScanBudget n))).trans_eq
   (by unfold diagonalBudget;ring)
 have kernels:=UniformActualSelectedKernelCost.all_clocks c hn roles _ physical shape
 have envelope:((∑t,UniformActualKernelCost.kernelTicks
  (actualReserveContext c n hn roles (physical t) (shape t))):ℝ) ≤
  UniformActualCalendarAsymptotics.kernelEnvelope c.roles n:=
  kernels.trans_eq (by unfold UniformActualCalendarAsymptotics.kernelEnvelope;ring)
 unfold clockEnvelope
 linarith only[numeric,envelope]

/-- Once the actual amortized table printer supplies its linear bound, the
final twenty-stage majorant has the paper cost. The clock estimate is proved
above rather than passed in as a desired final Big-O premise. -/
theorem total_with_clockEnvelope_isBigO_paper(c:Constants)(W:ℕ)
 (tableHeader table:ℕ→ℕ)
 (headers:(fun n:ℕ=>(tableHeader n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)))
 (tables:(fun n:ℕ=>(table n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ))):
 (fun n:ℕ=>(UniformFinalOuterCost.overhead c W n:ℝ)+3*clockEnvelope W n+
  (table n:ℝ)+(tableHeader n:ℝ)) =O[atTop] asymptoticCost UniformExponent.theta:=by
 exact ((((UniformFinalOuterCost.overhead_isBigO_input c W).trans
  UniformFinalOuterCost.input_isBigO_paper).add ((clockEnvelope_isBigO_paper W).const_mul_left 3)).add
  (tables.trans UniformFinalOuterCost.input_isBigO_paper)).add
  (headers.trans UniformFinalOuterCost.input_isBigO_paper)

end
end ExactFourierCircuits.UniformFinalClockCost
