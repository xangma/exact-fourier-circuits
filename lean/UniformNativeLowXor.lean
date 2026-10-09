import UniformPhysicalBinaryInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeLowXor

/-- XOR of a low-q-bit mask preserves every higher gathered group/role bit. -/
theorem low_xor (q a t b : ℕ) (ht : t<2^q) (hb : b<2^q) :
 (a*2^q+t)^^^b=a*2^q+(t^^^b) := by
 have div : ((a*2^q+t)^^^b)/2^q=a := by
  rw [Nat.xor_div_two_pow,Nat.div_eq_of_lt hb,Nat.xor_zero,Nat.mul_comm a (2^q),
   Nat.add_comm,Nat.add_mul_div_left _ _ (Nat.two_pow_pos q),Nat.div_eq_of_lt ht,Nat.zero_add]
 have mod : ((a*2^q+t)^^^b)%2^q=t^^^b := by
  rw [Nat.xor_mod_two_pow,Nat.add_mod,Nat.mul_mod]
  simp [Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hb]
 have split := Nat.mod_add_div ((a*2^q+t)^^^b) (2^q)
 rw [div,mod,Nat.mul_comm (2^q) a,Nat.add_comm] at split
 exact split.symm

theorem low_mask (q a t : ℕ) (ht : t<2^q) :
 (a*2^q+t)^^^(2^q-1)=a*2^q+(t^^^(2^q-1)) :=
 low_xor q a t (2^q-1) ht (by have hp:=Nat.two_pow_pos q;omega)

/-- Exact flattening used by complete W-role gathered batches. -/
theorem gathered_low_mask (q W g i t : ℕ) (ht : t<2^q) :
 (g*(W*2^q)+i*2^q+t)^^^(2^q-1)=g*(W*2^q)+i*2^q+(t^^^(2^q-1)) := by
 have eq : g*(W*2^q)+i*2^q=(g*W+i)*2^q := by ring
 rw [eq]
 exact low_mask q (g*W+i) t ht

end ExactFourierCircuits.UniformNativeLowXor
