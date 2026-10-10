import UniformSelectedCRT
import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBudgetAbsorption
open scoped BigOperators
open UniformWorkingLength

def exponentialFactor (d : ℕ) : ℕ := d.factorial*2^(d+1)

/-- A direct factorial/binomial estimate, with no eventual-size hypothesis. -/
theorem polynomial_exponential (d ell : ℕ) :
 (ell+2)^d≤exponentialFactor d*3^ell := by
 calc
  (ell+2)^d≤(ell+2).ascFactorial d := Nat.pow_succ_le_ascFactorial _ _
  _=d.factorial*(ell+1+d).choose d := Nat.ascFactorial_eq_factorial_mul_choose _ _
  _≤d.factorial*2^(ell+1+d) :=
   Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
  _=exponentialFactor d*2^ell := by
   rw [show ell+1+d=(d+1)+ell by omega,pow_add]
   unfold exponentialFactor
   ring
  _≤exponentialFactor d*3^ell :=
   Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)

theorem polynomial_exponential_exists (d : ℕ) :
 ∃C:ℕ,∀ell:ℕ,(ell+2)^d≤C*3^ell :=
 ⟨exponentialFactor d,polynomial_exponential d⟩

theorem selected_volume_lower (n : ℕ) : 3^(axisCount n)≤workingLength n := by
 have h:=primeProduct_lower (axisCount n)
 have hp:1≤binaryFactor n := by
  unfold binaryFactor
  exact Nat.succ_le_of_lt (Nat.pow_pos (by decide))
 exact h.trans (Nat.le_mul_of_pos_right _ hp)

def selectedFactor (d : ℕ) : ℕ := 129^d*exponentialFactor (2*d+1)

/-- Every fixed local radix polynomial is absorbed by the actual selected
working volume. The constant depends only on the fixed degree. -/
theorem selected_sum {n : ℕ} (hn : 0<n) (d : ℕ) :
 (∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^d)≤
 selectedFactor d*workingLength n := by
 have cell (i:Fin (axisCount n+1)) :
  (UniformSelectedCRT.radices n i+1)^d≤129^d*(axisCount n+2)^(2*d) := by
  have hr:=UniformSelectedCRT.radix_quadratic hn i
  have hp:1≤(axisCount n+2)^2 :=
   Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  have h:UniformSelectedCRT.radices n i+1≤129*(axisCount n+2)^2 := by omega
  calc
   (UniformSelectedCRT.radices n i+1)^d≤(129*(axisCount n+2)^2)^d :=
    Nat.pow_le_pow_left h _
   _=129^d*(axisCount n+2)^(2*d) := by rw [mul_pow,pow_mul]
 calc
  (∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^d)≤
   ∑_i:Fin (axisCount n+1),129^d*(axisCount n+2)^(2*d) :=
    Finset.sum_le_sum (fun i _=>cell i)
  _=(axisCount n+1)*(129^d*(axisCount n+2)^(2*d)) := by simp
  _≤(axisCount n+2)*(129^d*(axisCount n+2)^(2*d)) :=
    Nat.mul_le_mul_right _ (by omega)
  _=129^d*(axisCount n+2)^(2*d+1) := by rw [pow_succ];ring
  _≤129^d*(exponentialFactor (2*d+1)*3^(axisCount n)) :=
    Nat.mul_le_mul_left _ (polynomial_exponential _ _)
  _ ≤ selectedFactor d*workingLength n := by
    unfold selectedFactor
    rw [←mul_assoc]
    exact Nat.mul_le_mul_left _ (selected_volume_lower n)

theorem selected_sum_exists (d : ℕ) :
 ∃C:ℕ,∀n:ℕ,0<n→
  (∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^d)≤C*workingLength n :=
 ⟨selectedFactor d,fun _ hn=>selected_sum hn d⟩

end ExactFourierCircuits.DFTModelCacheBudgetAbsorption
