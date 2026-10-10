import DFTModelSavingBinaryPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] DFTModelRecursiveBinary.program DFTModelRecursiveBinary.body

theorem volume_half (R k : ℕ) (hk : 0<k) : (R*2^k)/2=R*2^(k-1) := by
  have h : R*2^k=R*2^(k-1)*2 := by
    rw [Nat.mul_assoc,←Nat.pow_succ,show (k-1).succ=k by omega]
  rw [h,Nat.mul_div_cancel _ (by omega)]

theorem volume_even (R k : ℕ) (hk : 0<k) : 2*((R*2^k)/2)=R*2^k := by
  rw [volume_half R k hk]
  have h : R*2^k=R*2^(k-1)*2 := by
    rw [Nat.mul_assoc,←Nat.pow_succ,show (k-1).succ=k by omega]
  rw [h,Nat.mul_comm]

theorem program_work_zero {R : ℕ} (f f0 : Fin R → Fin (2^0) → Scalar) :
    (run DFTModelRecursiveBinary.program ((0,Complex.I),paired f f0)).work=10 := by
  rw [DFTModelRecursiveBinary.program,comp_run,DFTModelRecursiveBinary.loop_run]
  rfl

theorem program_work_positive {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar) (hk : 0<k) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).work=
      10+k*(420*(R*2^(k-1))+117) := by
  rw [DFTModelRecursiveBinary.program_work k Complex.I (paired f f0) (volume_even R k hk)]
  change 10+k*(420*((R*2^k)/2)+117)=_
  rw [volume_half R k hk]

theorem program_native_work {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar) (roles : 0<R) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).work≤
      32*(R*UniformBinaryBatchCMachine.arrayCost k+5) := by
  by_cases hk : k=0
  · subst k
    rw [program_work_zero]
    simp only [UniformBinaryBatchCMachine.arrayCost,Nat.zero_mul,Nat.zero_add]
    omega
  · have kp : 0<k := by omega
    rw [program_work_positive f f0 kp]
    unfold UniformBinaryBatchCMachine.arrayCost
    have h1 : 420*(k*(R*2^(k-1)))≤800*(k*(R*2^(k-1))) := by omega
    have h2 : 117*k≤352*R*k :=
      Nat.mul_le_mul_right k (by omega : 117≤352*R)
    nlinarith

theorem base_work_bound {R k threshold : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (small : k<threshold) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).work≤
      (537*threshold+10)*(R*2^k+1) := by
  by_cases hk : k=0
  · subst k
    rw [program_work_zero]
    nlinarith
  · exact DFTModelRecursiveBinary.base_work_bound k threshold Complex.I (paired f f0)
      (volume_even R k (by omega)) small

end
end ExactFourierCircuits.DFTModelSavingBinary
