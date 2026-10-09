import UniformCRT
import UniformWorkingLength

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.1 (5.3)-(5.4), PDF p.21, and §5.2 (5.5), PDF p.22
(`eq:working-length`, `eq:working-bounds`, `eq:crt-fourier`).

Instantiates CRT with the selected odd primes and the binary fill, retaining
a harmless width-one factor. The factor bounds apply to every positive length.
-/
set_option autoImplicit false

namespace ExactFourierCircuits.UniformSelectedCRT
open scoped BigOperators
open UniformWorkingLength

/-- The harmless width-one binary factor is retained when no binary fill is needed. -/
/- Paper stage: §5.1 (5.3)-(5.4), PDF p.21 and §5.2 (5.5), PDF p.22: specialize the abstract coprime CRT factors to the actual selected length. -/
def radices (n : ℕ) : Fin (axisCount n + 1) → ℕ :=
  Fin.snoc (fun i => oddPrime i.val) (binaryFactor n)

theorem radix_pos (n : ℕ) : ∀ i, 0 < radices n i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [radices, binaryFactor]
  · simpa [radices] using (oddPrime_prime j.val).pos

theorem radix_coprime_binary (n j : ℕ) : Nat.Coprime (oddPrime j) (binaryFactor n) :=
  (Nat.coprime_two_right.mpr (oddPrime_odd j)).pow_right _

theorem radices_pairwise (n : ℕ) : Pairwise (fun i j => Nat.Coprime (radices n i) (radices n j)) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact (h rfl).elim
    · intro _; simpa [radices] using (radix_coprime_binary n j.val).symm
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; simpa [radices] using radix_coprime_binary n i.val
    · intro h
      have hij : i.val ≠ j.val := by
        intro he
        exact h (congrArg Fin.castSucc (Fin.ext he))
      simpa [radices] using oddPrime_coprime hij

theorem radices_product (n : ℕ) : (∏ i, radices n i) = workingLength n := by
  rw [Fin.prod_univ_castSucc]
  simp only [radices, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fin.prod_univ_eq_prod_range, ← primeProduct_eq_prod]
  rfl

theorem radix_quadratic {n : ℕ} (hn : 0 < n) (i : Fin (axisCount n + 1)) :
    radices n i ≤ 128 * (axisCount n + 2) ^ 2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [radices] using (binaryFactor_quadratic hn).le
  · simp only [radices, Fin.snoc_castSucc]
    calc
      oddPrime j.val ≤ 64 * (j.val + 2) ^ 2 := oddPrime_upper _
      _ ≤ 64 * (axisCount n + 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

def permutation (n : ℕ) : (∀ i, Fin (radices n i)) ≃ Fin (workingLength n) :=
  (UniformCRT.permutation (radices n) (radix_pos n) (radices_pairwise n)).trans
    (finCongr (radices_product n))

theorem permutation_address (n : ℕ) (j : ∀ i, Fin (radices n i)) :
    (permutation n j).val = UniformCRT.address (radices n) j := rfl

noncomputable section

/- Paper stage: §5.2 (5.5), PDF p.22: exact matrix result with selected local phases. Physical all-axis correction is proved in UniformSelectedPhysicalCRT. -/
theorem matrix_factorization (n : ℕ) :
    Matrix.reindex (permutation n).symm (permutation n).symm
      (OAI.ExactFourier.fourierMatrix (workingLength n)) =
        OAI.ExactFourier.PiTensor.matrix (fun i => OAI.ExactFourier.RadixTwo.dft
          (radices n i) (OAI.ExactFourier.zeta (radices n i) ^ UniformCRT.inverseDigit (radices n) i)) := by
  ext j k
  change OAI.ExactFourier.zeta (workingLength n) ^
    (UniformCRT.address (radices n) j * UniformCRT.address (radices n) k) = _
  rw [← radices_product]
  exact congrFun (congrFun (UniformCRT.matrix_factorization (radices n)
    (radix_pos n) (radices_pairwise n)) j) k

end
end ExactFourierCircuits.UniformSelectedCRT
