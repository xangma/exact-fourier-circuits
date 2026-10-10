import DFTModelSavingResidualBilledLoop
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine OAI.PowerSaving OAI.PowerSaving.RAM DFTModelAffine
noncomputable section

/-- At the real loop entry, the suffix bill is exactly the finite child sum. -/
theorem remainingWork_zero {groups : ℕ} (q : ℕ) (I : ℂ)
  (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) :
  remainingWork q I h input input0 0=
    ∑g : Fin groups,(h ((q,I),DFTModelRecursiveScalarSource.paired (input g) (input0 g))).work := by
  simpa only [remainingWork,List.drop_zero,List.finRange,List.map_ofFn,Function.comp_def] using
    Fin.sum_ofFn (fun g : Fin groups=>
      (h ((q,I),DFTModelRecursiveScalarSource.paired (input g) (input0 g))).work)

/-- A per-child additive bill is absorbed by real wrapper instructions, without
multiplying the recursive work coefficient. -/
theorem billed_work_le_ticks {K allowance remaining childTicks ticks work : ℕ}
  (elapsed : ticks=169*remaining+childTicks+1)
  (bill : work ≤ K*childTicks+allowance*remaining)
  (allowance_fits : allowance ≤ 169*K) : work ≤ K*ticks := by
  have extra : allowance*remaining ≤ K*(169*remaining) := by
    calc
      _ ≤ (169*K)*remaining := Nat.mul_le_mul_right remaining allowance_fits
      _ = K*(169*remaining) := by ring
  rw [elapsed]
  calc
    _ ≤ K*childTicks+allowance*remaining := bill
    _ ≤ K*childTicks+K*(169*remaining) := Nat.add_le_add_left extra _
    _ ≤ K*(169*remaining+childTicks+1) := by
      simp only [Nat.mul_add,Nat.mul_one]
      omega

theorem billed_work_le_ticks_self {K remaining childTicks ticks work : ℕ}
  (elapsed : ticks=169*remaining+childTicks+1)
  (bill : work ≤ K*childTicks+K*remaining) : work ≤ K*ticks :=
  billed_work_le_ticks elapsed bill (by omega)

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup
