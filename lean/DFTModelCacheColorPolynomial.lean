import DFTModelCacheColorClosed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMatchingAxisTableMachine (InRange)
noncomputable section

private theorem geometry (r M : ℕ) :
    H r M≤913*(r+M+1) ∧ UniformGreedyColorMachine.runtimeBudget M≤200*(r+M+1)^2 := by
  unfold H B U UniformGreedyColorMachine.runtimeBudget
  constructor
  · omega
  · exact Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by omega) 2)

/-- Dense finite-state interpretation is billed honestly. This is a local
polynomial cache bound, not a constant-work-per-native-tick assertion. -/
theorem polynomial_work (r M : ℕ) : workBound r M≤50000000*(r+M+1)^3 := by
  let extent:=r+M+1
  have hs:1≤extent := by dsimp [extent];omega
  have square:extent≤extent^2 := by nlinarith [Nat.mul_le_mul_left extent hs]
  have cube:extent^2≤extent^3 := by nlinarith [Nat.mul_le_mul_left (extent^2) hs]
  have size:H r M≤913*extent := (geometry r M).1
  have time:UniformGreedyColorMachine.runtimeBudget M≤200*extent^2 := (geometry r M).2
  have coeff:35*(824+H r M)+411≤100000*extent := by omega
  have product:=Nat.mul_le_mul time coeff
  have hM:M≤extent := by dsimp [extent];omega
  change workBound r M≤50000000*extent^3
  unfold workBound compiledWork
  nlinarith

theorem polynomial_peak (r M : ℕ) : peakBound r M≤10000*(r+M+1)^2 := by
  let extent:=r+M+1
  have hs:1≤extent := by dsimp [extent];omega
  have square:extent≤extent^2 := by nlinarith [Nat.mul_le_mul_left extent hs]
  have size:H r M≤913*extent := (geometry r M).1
  have time:UniformGreedyColorMachine.runtimeBudget M≤200*extent^2 := (geometry r M).2
  have hM:M≤extent := by dsimp [extent];omega
  change peakBound r M≤10000*extent^2
  unfold peakBound compiledPeak C
  repeat' apply max_le
  all_goals nlinarith

/-- Polynomial bounds apply to the exact raw-row producer whose colors were
proved equal to native51 output, preserving all coefficient words. -/
theorem execution_polynomial {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hr : InRange r E) :
    (run program (r,z)).valid ∧
    (run program (r,z)).work≤50000000*(r+z.len+1)^3 ∧
    (run program (r,z)).peak≤10000*(r+z.len+1)^2 := by
  obtain ⟨_,_,_,_,_,valid,_,_,_,_,_,work,peak⟩:=execution r n x z E rows hr
  exact ⟨valid,work.trans (polynomial_work r z.len),peak.trans (polynomial_peak r z.len)⟩

end
end ExactFourierCircuits.DFTModelCacheColor
