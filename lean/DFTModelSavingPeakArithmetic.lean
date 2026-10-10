import DFTModelSavingPeakLocal

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak

lemma scalar_local_bound (R V S : ℕ) (one : 1 ≤ S) (volume : V ≤ S) :
    R*V+7 ≤ (R+7)*S := by
  nlinarith [Nat.mul_le_mul_left R volume]

lemma y_local_bound (R size V S : ℕ) (one : 1 ≤ S) (volume : V ≤ S) (square : V*V=S) :
    4*(R*V+size+V*V)+2 ≤ (4*(R+size+1)+5)*S := by
  rw [square]
  nlinarith [Nat.mul_le_mul_left R volume,Nat.mul_le_mul_left size one]

lemma exchange_local_bound (R size V S : ℕ) (one : 1 ≤ S) (volume : V ≤ S) :
    R*V+size ≤ (R+size+4)*S := by
  nlinarith [Nat.mul_le_mul_left R volume,Nat.mul_le_mul_left size one]

lemma const_mul_bound (a b S : ℕ) (one : 1 ≤ S) : a ≤ (a+b)*S := by
  nlinarith

lemma scalar_const_bound (R S : ℕ) (one : 1 ≤ S) : 1 ≤ (R+7)*S := by nlinarith
lemma y_const_bound (R size S : ℕ) (one : 1 ≤ S) :
    3 ≤ (4*(R+size+1)+5)*S := by nlinarith
lemma exchange_const_bound (R size S : ℕ) (one : 1 ≤ S) :
    4 ≤ (R+size+4)*S := by nlinarith
lemma padding_const_bound (A S : ℕ) (one : 1 ≤ S) : 5 ≤ (A+5)*S := by nlinarith

end ExactFourierCircuits.DFTModelSavingPeak
