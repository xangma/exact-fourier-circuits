import DFTModelSavingBinarySource
import DFTModelSavingBinarySuffixSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinaryEndpoints
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
open DFTModelRecursiveScalarSource (paired)
open UniformBinaryTensorCoordinates
noncomputable section
attribute [local irreducible] DFTModelSavingBinary.base DFTModelSavingBinarySuffix.program

theorem base_zero {R : ℕ} (f f0 : Fin R → Fin (2^0) → Scalar) :
    (run DFTModelSavingBinary.base ((0,Complex.I),paired f f0)).val=
      ((0,Complex.I),paired f f0) := by
  rw [DFTModelSavingBinary.base_paired]
  rfl

theorem suffix_complete {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar) :
    (run DFTModelSavingBinarySuffix.program (k,((k,Complex.I),paired f f0))).val=
      ((k,Complex.I),paired f f0) := by
  rw [DFTModelSavingBinarySuffix.program_paired f f0 k (le_refl _)]
  rw [show (List.finRange k).drop k=[] from List.drop_eq_nil_iff.mpr (by simp)]
  rfl

/-- The charged spectator program completes an actually computed low-bit
prefix, preserving both exact channels and all dependency flags. -/
theorem prefix_suffix {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) :
    (run DFTModelSavingBinarySuffix.program (b,((k,Complex.I),
      paired (fun r=>applyAxes k ((List.finRange k).take b) (f r))
        (fun r=>applyAxes k ((List.finRange k).take b) (f0 r))))).val=
      (run DFTModelSavingBinary.base ((k,Complex.I),paired f f0)).val := by
  rw [DFTModelSavingBinarySuffix.program_paired _ _ b cap,DFTModelSavingBinary.base_paired]
  congr 2 <;> funext r <;> exact UniformBinarySpectatorCMachine.prefix_suffix k b _

end
end ExactFourierCircuits.DFTModelSavingBinaryEndpoints
