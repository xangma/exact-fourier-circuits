import FrameSpectrum

/- Common address frames commute with the actual linear scalar-role maps.
   Support compatibility is essential when the role frames differ. -/
namespace ExactFourierCircuits.FrameCommutation
open scoped BigOperators
noncomputable section
variable {ρ τ : Type*} [Fintype ρ]

def pointwiseMatrix (M : Matrix ρ ρ ℂ) (f : ρ → τ → ℂ) : ρ → τ → ℂ :=
  fun i x => ∑ j, M i j * f j x

def roleOperators (T : ρ → (τ → ℂ) →ₗ[ℂ] (τ → ℂ))
    (f : ρ → τ → ℂ) : ρ → τ → ℂ := fun i => T i (f i)

theorem pointwiseMatrix_as_sum (M : Matrix ρ ρ ℂ) (f : ρ → τ → ℂ) (i : ρ) :
    pointwiseMatrix M f i = ∑ j, M i j • f j := by
  ext x
  simp [pointwiseMatrix]

/-- The stated support condition precisely expresses a common frame on every
    scalar gate block; untouched roles impose no condition. -/
theorem compatible_operators_commute (M : Matrix ρ ρ ℂ)
    (T : ρ → (τ → ℂ) →ₗ[ℂ] (τ → ℂ))
    (h : ∀ i j, M i j ≠ 0 → T i = T j) (f : ρ → τ → ℂ) :
    roleOperators T (pointwiseMatrix M f) = pointwiseMatrix M (roleOperators T f) := by
  funext i
  rw [roleOperators, pointwiseMatrix_as_sum, map_sum]
  rw [pointwiseMatrix_as_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  by_cases hm : M i j = 0
  · simp [hm]
  · rw [h i j hm]
    rfl

theorem common_operator_commutes (M : Matrix ρ ρ ℂ)
    (T : (τ → ℂ) →ₗ[ℂ] (τ → ℂ)) (f : ρ → τ → ℂ) :
    roleOperators (fun _ => T) (pointwiseMatrix M f) =
      pointwiseMatrix M (roleOperators (fun _ => T) f) :=
  compatible_operators_commute M (fun _ => T) (fun _ _ _ => rfl) f

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whole-array Walsh frames, not merely address pullbacks, commute with each
    pointwise scalar gate whose nonzero entries join equal labels. -/
theorem compatible_frames_commute (M : Matrix ρ ρ ℂ)
    (q : ρ → BinaryFrames.Vec ι → ZMod 4)
    (h : ∀ i j, M i j ≠ 0 → q i = q j)
    (f : ρ → BinaryFrames.Vec ι → ℂ) :
    roleOperators (fun i => FrameSpectrum.frameMap (q i)) (pointwiseMatrix M f) =
      pointwiseMatrix M (roleOperators (fun i => FrameSpectrum.frameMap (q i)) f) := by
  apply compatible_operators_commute
  intro i j hij
  rw [h i j hij]

end
end ExactFourierCircuits.FrameCommutation
