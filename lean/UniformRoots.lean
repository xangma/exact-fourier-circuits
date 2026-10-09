import OAI.Computability.FourierCircuit.Core

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3, paragraph after (5.9), PDF p.23 (`eq:root-size`).

Algebraic extraction of the specified canonical roots by integer powers.
The exponential definition fixes the phase; runtime extraction is separately
charged by the root and power machines.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRoots
open OAI.ExactFourier
noncomputable section

theorem specifiedRoot_ne_zero (d : ℕ) : zeta d ≠ 0 := Complex.exp_ne_zero _

/-- Extract the specified root, including its phase convention, not just a primitive root. -/
theorem specifiedRoot_mul_power (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    zeta (d * e) ^ e = zeta d := by
  change Complex.exp (2 * Real.pi * Complex.I / ((d * e : ℕ) : ℂ)) ^ e =
    Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have he' : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  field_simp

theorem specifiedRoot_divisor_power (D d : ℕ) (hD : 0 < D) (hd : 0 < d)
    (hdiv : d ∣ D) : zeta D ^ (D / d) = zeta d := by
  have heq : d * (D / d) = D := Nat.mul_div_cancel' hdiv
  have he : 0 < D / d := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hzero : D = 0 := by rw [← heq, hz, mul_zero]
    exact hD.ne' hzero
  calc
    zeta D ^ (D / d) = zeta (d * (D / d)) ^ (D / d) :=
      congrArg (fun q => zeta q ^ (D / d)) heq.symm
    _ = zeta d := specifiedRoot_mul_power d (D / d) hd he

end
end ExactFourierCircuits.UniformRoots
