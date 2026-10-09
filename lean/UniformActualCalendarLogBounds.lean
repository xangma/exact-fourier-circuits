import UniformFourierClockBounds

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarLogBounds
open UniformNetworkCost UniformCalendarClockBounds UniformFourierClockBounds
noncomputable section

lemma quadratic_clog (a : ℕ) (ha : 2 ≤ a) :
 ((Nat.clog 2 (128*a^2)+1:ℕ):ℝ) ≤ 10*(1+Real.log (a:ℝ)):=by
 let q:ℕ:=128*a^2
 have ha2:(2:ℝ) ≤ a:=by exact_mod_cast ha
 have ha0:(0:ℝ) < a:=by linarith
 have logNonneg:0 ≤ Real.log (a:ℝ):=Real.log_nonneg (by linarith)
 have qOne:1 ≤ q:=by dsimp [q];nlinarith
 have qPos:(0:ℝ) < q:=by exact_mod_cast (show 0<q by omega)
 have qBound:(q:ℝ) ≤ 128*(a:ℝ)^2:=by dsimp [q];push_cast;exact le_rfl
 have logBound:=Real.log_le_log qPos qBound
 rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at logBound
 have log128:Real.log 128=7*Real.log 2:=by rw [show(128:ℝ)=2^7 by norm_num,Real.log_pow];norm_num
 rw [log128] at logBound
 norm_num only [Nat.cast_ofNat] at logBound
 have positiveLog:0 < Real.log 2:=Real.log_pos (by norm_num)
 have logbBound:Real.logb 2 (q:ℝ) ≤ 7+4*Real.log (a:ℝ):=by
  rw [Real.logb,div_le_iff₀ positiveLog]
  have lower:=mul_le_mul_of_nonneg_left UniformWorkingLength.log_two_lower
   (show 0 ≤ 4*Real.log (a:ℝ) by positivity)
  nlinarith only [logBound,lower]
 have logbNonneg:0 ≤ Real.logb 2 (q:ℝ):=Real.logb_nonneg (by norm_num) (by exact_mod_cast qOne)
 have ceilBound:=(Nat.ceil_lt_add_one logbNonneg).le
 have ceiling:⌈Real.logb 2 (q:ℝ)⌉₊=Nat.clog 2 q:=by
  simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 q
 rw [ceiling] at ceilBound
 norm_num only [Nat.cast_add,Nat.cast_one]
 change (Nat.clog 2 q:ℝ)+1 ≤ 10*(1+Real.log (a:ℝ))
 linarith

lemma radix_clog (n : ℕ) : ((Nat.clog 2 (radixCap n)+1:ℕ):ℝ) ≤ 10*logFactor n:=
 quadratic_clog (UniformWorkingLength.axisCount n+2) (by omega)

def horizonUnit : ℕ:=2*UniformBalancedToeplitz.depthUnit*10^4+5

/-- The genuine maximum full Fourier horizon, including both epochs and five
boundary clocks, has a fixed fourth-logarithm bound. -/
theorem horizon_cap (n : ℕ) : (horizonCap n:ℝ) ≤ horizonUnit*logFactor n^4:=by
 have clock:=radix_clog n
 have power:=pow_le_pow_left₀ (Nat.cast_nonneg _) clock 4
 have one:=one_le_pow₀ (logFactor_one_le n) (n:=4)
 have scaled:=mul_le_mul_of_nonneg_left power
  (show (0:ℝ) ≤ 2*UniformBalancedToeplitz.depthUnit by positivity)
 rw [mul_pow] at scaled
 unfold horizonCap clockCap horizonUnit
 push_cast at scaled ⊢
 nlinarith only [scaled,one]

lemma horizon_bound {n : ℕ} (hn : 0<n) : (horizon n:ℝ) ≤ horizonUnit*logFactor n^4:=by
 have bound:(horizon n:ℝ) ≤ horizonCap n:=by exact_mod_cast UniformFourierClockBounds.bound hn
 exact bound.trans (horizon_cap n)

end
end ExactFourierCircuits.UniformActualCalendarLogBounds
