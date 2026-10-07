import TensorWords
import OAI.Computability.FourierCircuit.TensorCostAlgebra

set_option autoImplicit false
namespace ExactFourierCircuits.TensorFusion
open OAI.ExactFourier
open scoped Kronecker
noncomputable section

def coordinates (k : ℕ) : TensorAxis.Space (Fin 2) k ≃ Fin (2 ^ k) :=
  (TensorAxis.funCoordinates k).trans (tensorCoordinates 2 k).symm

def split (r n : ℕ) : Fin (2 ^ (r + n)) ≃ (Fin (2 ^ r) × Fin (2 ^ n)) :=
  (coordinates (r + n)).symm.trans
    ((TensorAxis.appendCoordinates r n).trans ((coordinates r).prodCongr (coordinates n)))

def fusion (r n : ℕ) : (Fin (2 ^ r) × Fin (2 ^ n)) ≃ Fin (2 ^ (r + n)) :=
  (split r n).symm

theorem split_tensor (r n : ℕ) :
    Matrix.reindex (split r n) (split r n) (tensorPower C (r + n)) =
      tensorPower C r ⊗ₖ tensorPower C n := by
  rw [← TensorAxis.source_power_reindex C (r + n)]
  change Matrix.reindex (split r n) (split r n)
    (Matrix.reindex (coordinates (r + n)) (coordinates (r + n))
      (TensorAxis.power C (r + n))) = _
  rw [reindex_comp]
  have hc : (coordinates (r + n)).trans (split r n) =
      (TensorAxis.appendCoordinates r n).trans ((coordinates r).prodCongr (coordinates n)) := by
    ext x <;> simp [split]
  rw [hc, ← reindex_comp, TensorAxis.power_append]
  change Matrix.reindex ((coordinates r).prodCongr (coordinates n))
    ((coordinates r).prodCongr (coordinates n))
    (Matrix.kronecker (TensorAxis.power C r) (TensorAxis.power C n)) = _
  rw [reindex_tensor]
  exact congrArg₂ Matrix.kronecker (TensorAxis.source_power_reindex C r)
    (TensorAxis.source_power_reindex C n)

theorem fusion_tensor (r n : ℕ) :
    Matrix.reindex (fusion r n) (fusion r n)
      (tensorPower C r ⊗ₖ tensorPower C n) = tensorPower C (r + n) := by
  rw [← split_tensor, reindex_comp]
  simp [fusion]

end
end ExactFourierCircuits.TensorFusion
