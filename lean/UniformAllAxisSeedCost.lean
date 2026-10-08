import UniformInitialTraversalPreparation
import UniformWorkingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisSeedCost
open Filter Asymptotics
open UniformInitialPreparation (ell len)
open UniformAllAxisSeedPreparation (axisCount radix preparationBudget preparationRuntime)
noncomputable section

/-- Bound the actual RAM preparation budget using the selected radices,
rather than the much larger working transform length. -/
theorem budget_axis_power {n : ℕ} (hn:0<n) :
    preparationBudget n≤9000009*(ell n+2)^5 := by
  let t:=ell n+2
  have ht:2≤t:=by dsimp [t];omega
  have h24:t^2≤t^4:=by
    have h1:1≤t^2:=by nlinarith
    rw [show t^4=(t^2)^2 by ring]
    nlinarith
  have hterm (j : Fin (axisCount n)) :
      494*(radix n j)^2+40*radix n j+113≤9000000*t^4 := by
    have hr:radix n j≤128*t^2:=UniformSelectedCRT.radix_quadratic hn j
    have hs:=Nat.pow_le_pow_left hr 2
    rw [show (128*t^2)^2=16384*t^4 by ring] at hs
    nlinarith
  have hsum:(∑j:Fin (axisCount n),(494*(radix n j)^2+40*radix n j+113))
      ≤axisCount n*(9000000*t^4):=by
    calc _≤∑_j:Fin (axisCount n),9000000*t^4:=Finset.sum_le_sum (fun j _=>hterm j)
         _=_:=by simp
  have hcount:axisCount n≤t:=by dsimp [axisCount,t];omega
  have hmul:=Nat.mul_le_mul_right (9000000*t^4) hcount
  have h5:1≤t^5:=by have h:0<t^5:=pow_pos (by omega) 5;omega
  have he:t*(9000000*t^4)=9000000*t^5:=by ring
  rw [he] at hmul
  unfold preparationBudget
  change 9+_≤9000009*t^5
  omega

theorem budget_isBigO_axis_five :
    (fun n : ℕ=>(preparationBudget n:ℝ)) =O[atTop]
      (fun n : ℕ=>((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5) := by
  apply IsBigO.of_bound 9000009
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have h:(preparationBudget n:ℝ)≤9000009*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5:=by
    exact_mod_cast budget_axis_power (show 0<n by omega)
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity :0≤((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5)] using h

theorem budget_isBigO_log_five :
    (fun n : ℕ=>(preparationBudget n:ℝ)) =O[atTop]
      (fun n : ℕ=>Real.log (n:ℝ)^5) :=
  budget_isBigO_axis_five.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 5)

/-- This is the charged literal469 loop, not an unexecuted functional reserve. -/
theorem budget_isLittleO_input :
    (fun n : ℕ=>(preparationBudget n:ℝ)) =o[atTop] (fun n : ℕ=>(n:ℝ)) := by
  have hlog:(fun n : ℕ=>Real.log (n:ℝ)^5) =o[atTop] (fun n : ℕ=>(n:ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact budget_isBigO_log_five.trans_isLittleO hlog

theorem runtime_isLittleO_input :
    (fun n : ℕ=>(preparationRuntime n:ℝ)) =o[atTop] (fun n : ℕ=>(n:ℝ)) := by
  have h:(fun n : ℕ=>(preparationRuntime n:ℝ)) =O[atTop]
      (fun n : ℕ=>(preparationBudget n:ℝ)):=by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul] using
      (show (preparationRuntime n:ℝ)≤(preparationBudget n:ℝ) by
        exact_mod_cast UniformAllAxisSeedPreparation.runtime_bound n)
  exact h.trans_isLittleO budget_isLittleO_input

theorem fullBudget_isBigO_input :
    (fun n : ℕ=>(UniformAllAxisSeedPreparation.fullBudget n:ℝ)) =O[atTop]
      (fun n : ℕ=>(n:ℝ)) := by
  have hc:(fun _n : ℕ=>(1:ℝ)) =O[atTop] (fun n : ℕ=>(n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (1:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [UniformAllAxisSeedPreparation.fullBudget,Nat.cast_add,Nat.cast_one] using
    (UniformPermutationInversePreparation.preparationBudget_isBigO_input.add
      budget_isLittleO_input.isBigO).add hc

theorem workingLength_isBigO_input :
    (fun n : ℕ=>(len n:ℝ)) =O[atTop] (fun n : ℕ=>(n:ℝ)) := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have h:(len n:ℝ)≤4*(n:ℝ):=by
    exact_mod_cast (UniformWorkingLength.workingLength_upper (show 0<n by omega)).le
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using h

/-- The complete empty-state989 preparation plus real DFS costs O(n). This
leaves the global scalar transform and its saving-network execution open. -/
theorem initialTraversalBudget_isBigO_input :
    (fun n : ℕ=>(UniformInitialTraversalPreparation.preparationBudget n:ℝ)) =O[atTop]
      (fun n : ℕ=>(n:ℝ)) := by
  have hl:(fun n : ℕ=>(84:ℝ)*(len n:ℝ)) =O[atTop] (fun n : ℕ=>(n:ℝ)):=
    workingLength_isBigO_input.const_mul_left 84
  have hc:(fun _n : ℕ=>(7:ℝ)) =O[atTop] (fun n : ℕ=>(n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (7:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [UniformInitialTraversalPreparation.preparationBudget,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat] using (fullBudget_isBigO_input.add hl).add hc
end
end ExactFourierCircuits.UniformAllAxisSeedCost
