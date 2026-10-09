import UniformChirp
import OAI.Computability.FourierCircuit.ToeplitzCross
import Mathlib.Analysis.Fourier.ZMod

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 inverse formula after (5.6), PDF p.22, and §5.3
(5.7) and three-transform reduction, PDF pp.22-23 (`eq:working-transform`, `eq:chirp`).

Connects Mathlib's opposite-sign DFT to the paper's positive convention,
proves disjoint signed support, cyclic convolution and Bluestein reconstruction.
These semantic identities do not by themselves supply machine executions.
-/
/-! Positive-exponent standard-root cyclic Fourier semantics.  Mathlib's `dft`
uses the opposite sign, so the sign change is made explicit before connecting to
the OAI finite-index matrix.  These are semantic components, not a RAM compiler. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCyclic
noncomputable section
open scoped BigOperators
open OAI.ExactFourier

variable {N : ℕ} [NeZero N]

/- Paper stage: §5.2 inverse identity after (5.6), PDF p.22: explicitly change Mathlib sign and certify inverse normalization. -/
def positiveDFT (f : ZMod N → ℂ) (k : ZMod N) : ℂ := ZMod.dft f (-k)
def inversePositiveDFT (f : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft f k

theorem inversePositiveDFT_apply (f : ZMod N → ℂ) (k : ZMod N) :
    inversePositiveDFT f k = (N : ℂ)⁻¹ * positiveDFT f (-k) := by
  simp [inversePositiveDFT, positiveDFT]

theorem positiveDFT_apply (f : ZMod N → ℂ) (k : ZMod N) :
    positiveDFT f k = ∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j := by
  simp [positiveDFT, ZMod.dft_apply, smul_eq_mul]

theorem inversePositiveDFT_positiveDFT (f : ZMod N → ℂ) :
    inversePositiveDFT (positiveDFT f) = f := by
  funext k
  change (N : ℂ)⁻¹ * ZMod.dft (fun j => ZMod.dft f (-j)) k = f k
  rw [ZMod.dft_comp_neg, ZMod.dft_dft]
  simp [NeZero.ne (N : ℂ)]

theorem positiveDFT_inversePositiveDFT (f : ZMod N → ℂ) :
    positiveDFT (inversePositiveDFT f) = f := by
  funext k
  change ZMod.dft (fun j => (N : ℂ)⁻¹ * ZMod.dft f j) (-k) = f k
  rw [ZMod.dft_const_mul, ZMod.dft_dft]
  simp [NeZero.ne (N : ℂ)]

/- Paper stage: §5.3, three-transform convolution argument, PDF pp.22-23: exact cyclic convolution and Fourier multiplication identity. -/
def convolution (f g : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j : ZMod N, f j * g (k - j)

theorem positiveDFT_convolution (f g : ZMod N → ℂ) (k : ZMod N) :
    positiveDFT (convolution f g) k = positiveDFT f k * positiveDFT g k := by
  rw [positiveDFT_apply, positiveDFT_apply, positiveDFT_apply]
  conv_lhs =>
    simp only [convolution, Finset.mul_sum]
    rw [Finset.sum_comm]
  calc
    (∑ j : ZMod N, ∑ t : ZMod N,
        ZMod.stdAddChar (t * k) * (f j * g (t - j))) =
      ∑ j : ZMod N, ∑ l : ZMod N,
        ZMod.stdAddChar ((j + l) * k) * (f j * g l) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Equiv.sum_comp (Equiv.addLeft j)
        (fun t : ZMod N => ZMod.stdAddChar (t * k) * (f j * g (t - j)))]
      simp
    _ = (∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j) *
        ∑ l : ZMod N, ZMod.stdAddChar (l * k) * g l := by
      rw [Finset.sum_mul]
      simp only [add_mul, AddChar.map_add_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem convolution_via_fourier (f g : ZMod N → ℂ) :
    inversePositiveDFT (fun k => positiveDFT f k * positiveDFT g k) =
      convolution f g := by
  rw [show (fun k => positiveDFT f k * positiveDFT g k) =
    positiveDFT (convolution f g) from
      funext (fun k => (positiveDFT_convolution f g k).symm)]
  exact inversePositiveDFT_positiveDFT _

def toZMod (x : Fin N → ℂ) (j : ZMod N) : ℂ := x ((FourierCRT.finZMod N).symm j)

def fromZMod (f : ZMod N → ℂ) (j : Fin N) : ℂ := f (FourierCRT.finZMod N j)

theorem positiveDFT_fin (x : Fin N → ℂ) (i : Fin N) :
    positiveDFT (toZMod x) (FourierCRT.finZMod N i) = (fourierMatrix N).mulVec x i := by
  rw [positiveDFT_apply,
    ← (FourierCRT.finZMod N).sum_comp
      (fun j => ZMod.stdAddChar (j * FourierCRT.finZMod N i) * toZMod x j)]
  simp only [toZMod, Equiv.symm_apply_apply]
  change (∑ j : Fin N, ZMod.stdAddChar ((j.val : ZMod N) * (i.val : ZMod N)) * x j) =
    ∑ j : Fin N, zeta N ^ (i.val * j.val) * x j
  simp only [← Nat.cast_mul, FourierCRT.char_nat, FourierCRT.standard_root, Nat.mul_comm]

theorem fromZMod_positiveDFT (x : Fin N → ℂ) :
    fromZMod (positiveDFT (toZMod x)) = (fourierMatrix N).mulVec x := by
  funext i
  exact positiveDFT_fin x i

section Padding
variable {n L : ℕ} [NeZero L]

/-- Positive support is printed at the start; negative support is at the end. -/
/- Paper stage: §5.3, signed fixed operand after (5.7), PDF p.22: 2n<=L makes -(n-1),...,n-1 distinct and the two supports disjoint. -/
def signedRepresentative (n : ℕ) (z : ZMod L) : ℤ :=
  if z.val < n then z.val else (z.val : ℤ) - L

theorem signed_embedding (hL : 2 * n ≤ L) (u : ℤ)
    (hu : -(n : ℤ) < u ∧ u < n) :
    signedRepresentative n (u : ZMod L) = u ∧
      ((u : ZMod L).val < n ∨ L - (u : ZMod L).val < n) := by
  by_cases hpos : 0 ≤ u
  · have hm : u % (L : ℤ) = u := Int.emod_eq_of_lt hpos (by omega)
    have hv : (((u : ZMod L).val : ℕ) : ℤ) = u := by rw [ZMod.val_intCast, hm]
    have hs : (u : ZMod L).val < n := by omega
    exact ⟨by simpa [signedRepresentative, hs] using hv, Or.inl hs⟩
  · have hz : ((u + (L : ℤ) : ℤ) : ZMod L) = (u : ZMod L) := by simp
    have hm : (u + (L : ℤ)) % L = u + L :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hv : (((u : ZMod L).val : ℕ) : ℤ) = u + L := by
      rw [← hz, ZMod.val_intCast, hm]
    have hs : ¬(u : ZMod L).val < n := by omega
    have ht : L - (u : ZMod L).val < n := by omega
    exact ⟨by simp only [signedRepresentative, ite_eq_right hs]; omega, Or.inr ht⟩

theorem signed_interval_injective (hL : 2 * n ≤ L) (u v : ℤ)
    (hu : -(n : ℤ) < u ∧ u < n) (hv : -(n : ℤ) < v ∧ v < n)
    (he : (u : ZMod L) = (v : ZMod L)) : u = v := by
  rw [← (signed_embedding hL u hu).1, ← (signed_embedding hL v hv).1, he]

theorem support_disjoint (hL : 2 * n ≤ L) (z : ZMod L) :
    ¬(z.val < n ∧ L - z.val < n) := by
  have hz := ZMod.val_lt z
  omega

def chirpKernel (eta : ℂ) (n : ℕ) (z : ZMod L) : ℂ :=
  if z.val < n ∨ L - z.val < n then eta ^ (-(signedRepresentative n z) ^ 2) else 0

theorem chirpKernel_signed (eta : ℂ) (hL : 2 * n ≤ L) (u : ℤ)
    (hu : -(n : ℤ) < u ∧ u < n) :
    chirpKernel eta n (u : ZMod L) = eta ^ (-u ^ 2) := by
  rcases signed_embedding hL u hu with ⟨hr, hs⟩
  rw [chirpKernel, ite_eq_left hs, hr]

theorem chirpKernel_difference (eta : ℂ) (hL : 2 * n ≤ L) (j k : Fin n) :
    chirpKernel eta n ((k.val : ZMod L) - (j.val : ZMod L)) =
      eta ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2) := by
  have hj := j.isLt
  have hk := k.isLt
  have hu : -(n : ℤ) < (k.val : ℤ) - j.val ∧ (k.val : ℤ) - j.val < n := by omega
  simpa only [Int.cast_sub, Int.cast_natCast] using
    chirpKernel_signed eta hL ((k.val : ℤ) - j.val) hu

/-- Padding uses only an integer address test and literal zero. -/
def pad (x : Fin n → ℂ) (z : ZMod L) : ℂ :=
  if h : z.val < n then x ⟨z.val, h⟩ else 0

theorem convolution_pad (hnL : n ≤ L) (x : Fin n → ℂ) (g : ZMod L → ℂ)
    (k : ZMod L) :
    convolution (pad x) g k = ∑ j : Fin n, x j * g (k - (j.val : ZMod L)) := by
  let F : ℕ → ℂ := fun j => if h : j < n then x ⟨j, h⟩ * g (k - (j : ZMod L)) else 0
  rw [convolution,
    ← (FourierCRT.finZMod L).sum_comp (fun j => pad x j * g (k - j))]
  calc
    (∑ j : Fin L, pad x (FourierCRT.finZMod L j) * g (k - FourierCRT.finZMod L j)) =
        ∑ j : Fin L, F j.val := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < n <;>
        simp [pad, F, FourierCRT.finZMod, Nat.mod_eq_of_lt j.isLt, hj]
    _ = ∑ j ∈ Finset.range n, F j := by
      rw [Fin.sum_univ_eq_sum_range F L]
      symm
      apply Finset.sum_subset (Finset.range_mono hnL)
      intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [F, show ¬j < n by omega]
    _ = ∑ j : Fin n, x j * g (k - (j.val : ZMod L)) := by
      rw [← Fin.sum_univ_eq_sum_range F n]
      apply Finset.sum_congr rfl
      intro j _
      simp [F, j.isLt]

def paddedChirp (eta : ℂ) (x : Fin n → ℂ) : ZMod L → ℂ :=
  pad (fun j => eta ^ ((j.val : ℤ) ^ 2) * x j)

/- Paper stage: §5.3 (5.7), PDF p.22: signed support and zero padding instantiate the exact chirp convolution. -/
theorem bluestein_convolution (hn : 0 < n) (hL : 2 * n ≤ L)
    (x : Fin n → ℂ) (k : Fin n) :
    (fourierMatrix n).mulVec x k =
      zeta (2 * n) ^ ((k.val : ℤ) ^ 2) *
        convolution (paddedChirp (zeta (2 * n)) x)
          (chirpKernel (zeta (2 * n)) n) (k.val : ZMod L) := by
  rw [UniformChirp.fourier_chirp_sum n hn x k]
  simp only [paddedChirp]
  rw [convolution_pad (by omega)]
  simp_rw [chirpKernel_difference _ hL]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Two positive transforms and one normalized inverse produce every DFT output.
The second forward transform is of the fixed chirp operand and is not free. -/
theorem bluestein_three_transforms (hn : 0 < n) (hL : 2 * n ≤ L)
    (x : Fin n → ℂ) (k : Fin n) :
    (fourierMatrix n).mulVec x k =
      zeta (2 * n) ^ ((k.val : ℤ) ^ 2) *
        inversePositiveDFT (fun t =>
          positiveDFT (paddedChirp (zeta (2 * n)) x) t *
            positiveDFT (chirpKernel (zeta (2 * n)) n) t) (k.val : ZMod L) := by
  rw [convolution_via_fourier]
  exact bluestein_convolution hn hL x k

/- Paper stage: §5.2 inverse formula, PDF p.22 and §5.3 three transforms, PDF p.23: execute the inverse as a positive transform followed by negation and 1/L. -/
theorem bluestein_positive_transforms (hn : 0 < n) (hL : 2 * n ≤ L)
    (x : Fin n → ℂ) (k : Fin n) :
    (fourierMatrix n).mulVec x k =
      zeta (2 * n) ^ ((k.val : ℤ) ^ 2) * (L : ℂ)⁻¹ *
        positiveDFT (fun t =>
          positiveDFT (paddedChirp (zeta (2 * n)) x) t *
            positiveDFT (chirpKernel (zeta (2 * n)) n) t) (-(k.val : ZMod L)) := by
  rw [bluestein_three_transforms hn hL x k, inversePositiveDFT_apply, mul_assoc]

end Padding

end
end ExactFourierCircuits.UniformCyclic
