import UniformRecursiveActualRuntime
import UniformConditionalKernelLayout

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualSectorCost
open UniformSectorPacking UniformNetworkCost
noncomputable section

def actualCost : ℕ→ℕ:=UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
noncomputable def densityConstant : ℝ:=UniformRecursiveActualRuntime.criticalConstant*UniformBatching.width
lemma critical_nonneg : 0 ≤ UniformRecursiveActualRuntime.criticalConstant:=by
 unfold UniformRecursiveActualRuntime.criticalConstant
 exact mul_nonneg (add_nonneg
  (div_nonneg (Nat.cast_nonneg _) (by linarith [UniformExponent.one_lt_lambda]))
  (Nat.cast_nonneg _)) UniformExponent.lambda_pos.le
lemma density_nonneg : 0 ≤ densityConstant:=mul_nonneg critical_nonneg (Nat.cast_nonneg _)

lemma point_bound (k : ℕ) :
 (actualCost k:ℝ) ≤ densityConstant*(k+1:ℝ)^UniformExponent.theta*(2^k:ℕ):=by
 have bound:=UniformRecursiveActualRuntime.actual_critical_bound k
 exact bound.trans_eq (by simp only [volume,Nat.cast_mul,densityConstant];ring)

lemma list_bound (ks : List ℕ) (ell : ℕ) (axes : ∀k∈ks,k ≤ ell) :
 ((ks.map actualCost).sum:ℝ) ≤ densityConstant*(ell+1:ℝ)^UniformExponent.theta*
 ((ks.map (fun k=>(2^k:ℕ))).sum:ℝ):=by
 induction ks with
 | nil=>simp
 | cons k ks ih=>
   have head:=axes k (by simp)
   have tail:=ih (fun q h=>axes q (by simp [h]))
   have power : (k+1:ℝ)^UniformExponent.theta ≤ (ell+1:ℝ)^UniformExponent.theta:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ k+1)
    (by exact_mod_cast Nat.add_le_add_right head 1) UniformExponent.theta_pos.le
   have cap: (actualCost k:ℝ) ≤ densityConstant*(ell+1:ℝ)^UniformExponent.theta*(2^k:ℕ):=
    (point_bound k).trans (mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left power density_nonneg) (Nat.cast_nonneg _))
   simp only [List.map_cons,List.sum_cons,Nat.cast_add]
   nlinarith only [cap,tail]

lemma power_count (ks : List ℕ) : ks.length ≤ (ks.map (fun k=>2^k)).sum:=by
 induction ks with
 | nil=>rfl
 | cons k ks ih=>
   have positive:1 ≤ 2^k:=Nat.two_pow_pos k
   simp only [List.length_cons,List.map_cons,List.sum_cons];omega

lemma states_pairs (axes : List Axis) : (sectorStates axes).map BlockState.pairs=pairCounts axes:=by
 simp only [sectorStates,pairCounts,List.map_ofFn,Function.comp_def,expectedBlockState]
lemma states_count (axes : List Axis) : (sectorStates axes).length ≤ (radices axes).prod:=by
 have bound:=power_count (pairCounts axes)
 rw [pairCounts_sum_widths,←states_pairs,List.length_map] at bound
 exact bound
lemma volume_one (axes : List Axis) : 1 ≤ (radices axes).prod:=by
 induction axes with
 | nil=>rfl
 | cons a axes ih=>
   change 1 ≤ a.widths.sum*(radices axes).prod
   simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1 ≤ a.widths.sum by have:=a.radix_two;omega) ih

lemma budget_value (cost : ℕ→ℕ) (xs : List BlockState) :
 UniformConditionalSectorLoop.budget cost xs=((xs.map BlockState.pairs).map cost).sum+12*xs.length+2:=by
 induction xs with
 | nil=>rfl
 | cons st xs ih=>
   rw [UniformConditionalSectorLoop.budget_cons,ih]
   simp only [List.map_cons,List.sum_cons,List.length_cons];omega

/-- Actual same-program child charges over the genuine canonical sector list.
The12-step per-sector setup/return overhead and final two steps are included. -/
theorem sector_budget (axes : List Axis) :
 (UniformConditionalSectorLoop.budget actualCost (sectorStates axes):ℝ) ≤
 (densityConstant*(axes.length+1:ℝ)^UniformExponent.theta+14)*(radices axes).prod:=by
 have calls:=list_bound (pairCounts axes) axes.length (pairCounts_axes_bound axes)
 rw [pairCounts_sum_widths] at calls
 have count:=states_count axes
 have positive:=volume_one axes
 rw [budget_value,states_pairs]
 have c:((sectorStates axes).length:ℝ) ≤ (radices axes).prod:=by exact_mod_cast count
 have p:(1:ℝ) ≤ (radices axes).prod:=by exact_mod_cast positive
 push_cast at calls c p ⊢
 nlinarith only [calls,c,p]

end
end ExactFourierCircuits.UniformActualSectorCost
