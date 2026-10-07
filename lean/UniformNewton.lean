import UniformScalarPreparation
import OAI.Computability.FourierCircuit.ToeplitzCross

/-! Explicit local Newton coefficients and factorization.  No `Layered` theorem
or chosen complex scalar enters these identities. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNewton
noncomputable section
open scoped BigOperators
open OAI.ExactFourier
open NewtonFourier CoefficientTime

def diagonalValue (omega : ℂ) (j : ℕ) : ℂ := NewtonFourier.H omega j * scale omega j

theorem Hvalue_ne_zero {n : ℕ} {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (j : Fin n) : NewtonFourier.H omega j.val ≠ 0 := H_ne_zero hroot j.isLt

theorem scaleValue_ne_zero {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) (j : Fin n) : scale omega j.val ≠ 0 :=
  scale_ne_zero (hroot.ne_zero (Nat.ne_of_gt hn)) _

theorem diagonalValue_ne_zero {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) (j : Fin n) : diagonalValue omega j.val ≠ 0 :=
  mul_ne_zero (Hvalue_ne_zero hroot j) (scaleValue_ne_zero hn hroot j)

theorem N_diagonal (n : ℕ) (omega : ℂ) (j : Fin n) :
    N n omega j j = diagonalValue omega j.val := by
  have h := eval_factor omega j.val j.val (le_refl _)
  simpa [N, diagonalValue, mul_comm] using h

theorem P_diagonal (n : ℕ) (omega : ℂ) (j : Fin n) : P n omega j j = 1 := by
  simpa only [P, newton_natDegree] using (newton_monic omega j.val).coeff_natDegree

theorem N_unit {n : ℕ} (hn : 0 < n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    IsUnit (N n omega) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isLowerTriangular _ (N_lower n omega)]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [N_diagonal]
  exact diagonalValue_ne_zero hn hroot j

theorem triangular_middle (n : ℕ) (omega : ℂ) :
    (P n omega).transpose * N n omega =
      Matrix.diagonal (fun j : Fin n => diagonalValue omega j.val) := by
  let Q := (P n omega).transpose * N n omega
  have hlow : Q.IsLowerTriangular := (P_upper n omega).transpose.mul (N_lower n omega)
  have hsym : Q.transpose = Q := by
    dsimp [Q]
    rw [Matrix.transpose_mul, ← dft_mul_P n omega, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    have hs : (RadixTwo.dft n omega).transpose = RadixTwo.dft n omega := by
      ext i j
      simp [RadixTwo.dft, Nat.mul_comm]
    rw [hs]
    exact Matrix.mul_assoc _ _ _
  have hdiag : ∀ j, Q j j = N n omega j j := by
    intro j
    dsimp [Q]
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [Matrix.transpose_apply, P_diagonal]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · rw [N_lower n omega hlt, mul_zero]
      · rw [Matrix.transpose_apply, P_upper n omega hgt, zero_mul]
    · simp
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq] using (hdiag i).trans (N_diagonal n omega i)
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hlow hlt
    · have h := hlow hgt
      exact (congrFun (congrFun hsym i) j).symm.trans h

theorem fourier_factorization {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    RadixTwo.dft n omega = N n omega *
      (Matrix.diagonal (fun j : Fin n => diagonalValue omega j.val))⁻¹ *
        (N n omega).transpose := by
  have hN := N_unit hn hroot
  have hP := P_unit n omega
  have hPT := (Matrix.isUnit_transpose _).mpr hP
  have hNt : (N n omega).transpose = (P n omega).transpose * RadixTwo.dft n omega := by
    rw [← dft_mul_P n omega, Matrix.transpose_mul]
    congr 1
    ext i j
    simp [RadixTwo.dft, Nat.mul_comm]
  symm
  rw [hNt, ← triangular_middle n omega, Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc (N n omega) (N n omega)⁻¹,
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hN)]
  simp only [Matrix.one_mul, ← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hPT), Matrix.one_mul]

theorem N_toeplitz_factorization {n : ℕ} {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    N n omega = Matrix.diagonal (fun j : Fin n => NewtonFourier.H omega j.val) *
      truncMatrix n (invH omega) * Matrix.diagonal (fun j : Fin n => scale omega j.val) :=
  N_toeplitz hroot

theorem specified_fourier_factorization (n : ℕ) (hn : 0 < n) :
    fourierMatrix n = N n (zeta n) *
      (Matrix.diagonal (fun j : Fin n => diagonalValue (zeta n) j.val))⁻¹ *
        (N n (zeta n)).transpose :=
  fourier_factorization hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))

end

namespace Preparation
open OAI.ExactFourier NewtonFourier CoefficientTime
open UniformScalarPreparation (Instruction)
abbrev ScalarProgram := UniformScalarPreparation.Program

@[simp] theorem eval_step {r k : ℕ} (p : ScalarProgram r k)
    (i : Instruction r k) (rootValues : Fin r → ℂ) :
    (UniformScalarPreparation.Program.step p i).eval rootValues =
      Fin.snoc (p.eval rootValues) (i.eval rootValues (p.eval rootValues)) := rfl

@[simp] theorem admissible_step {r k : ℕ} (p : ScalarProgram r k)
    (i : Instruction r k) (rootValues : Fin r → ℂ) :
    (UniformScalarPreparation.Program.step p i).Admissible rootValues ↔
      p.Admissible rootValues ∧ i.Admissible (p.eval rootValues) := Iff.rfl

def roots (omega : ℂ) : Fin 1 → ℂ := fun _ => omega

@[reducible] def productCount : ℕ → ℕ
  | 0 => 3
  | j + 1 => productCount j + 5

theorem productCount_formula (j : ℕ) : productCount j = 5 * j + 3 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [productCount, ih]; omega

theorem productCount_lower (j : ℕ) : 3 ≤ productCount j := by
  rw [productCount_formula]
  omega

def rootRef (j : ℕ) : Fin (productCount j) := ⟨0, by have := productCount_lower j; omega⟩
def oneRef (j : ℕ) : Fin (productCount j) := ⟨1, by have := productCount_lower j; omega⟩
def minusRef (j : ℕ) : Fin (productCount j) := ⟨2, by have := productCount_lower j; omega⟩

def powerRef : (j : ℕ) → Fin (productCount j)
  | 0 => oneRef 0
  | j + 1 => (Fin.last (productCount j)).castSucc.castSucc.castSucc.castSucc

def HRef : (j : ℕ) → Fin (productCount j)
  | 0 => oneRef 0
  | j + 1 => (Fin.last (productCount j + 2)).castSucc.castSucc

def scaleRef : (j : ℕ) → Fin (productCount j)
  | 0 => oneRef 0
  | j + 1 => Fin.last (productCount j + 4)

theorem rootRef_succ (j : ℕ) : rootRef (j + 1) =
    (rootRef j).castSucc.castSucc.castSucc.castSucc.castSucc := rfl
theorem oneRef_succ (j : ℕ) : oneRef (j + 1) =
    (oneRef j).castSucc.castSucc.castSucc.castSucc.castSucc := rfl
theorem minusRef_succ (j : ℕ) : minusRef (j + 1) =
    (minusRef j).castSucc.castSucc.castSucc.castSucc.castSucc := rfl

theorem powerRef_succ (j : ℕ) : powerRef (j + 1) =
    (Fin.last (productCount j)).castSucc.castSucc.castSucc.castSucc := rfl
theorem HRef_succ (j : ℕ) : HRef (j + 1) =
    (Fin.last (productCount j + 2)).castSucc.castSucc := rfl
theorem scaleRef_succ (j : ℕ) : scaleRef (j + 1) =
    Fin.last (productCount j + 4) := rfl

/-- One supplied root and two rational literals; five shared-register operations
per step prepare the next power, H product, and signed Newton scale. -/
def productProgram : (j : ℕ) → ScalarProgram 1 (productCount j)
  | 0 => .step (.step (.step .nil (.root 0)) (.rational 1)) (.rational (-1))
  | j + 1 =>
      let p1 := UniformScalarPreparation.Program.step (productProgram j) (.mul (powerRef j) (rootRef j))
      let p2 := UniformScalarPreparation.Program.step p1
        (.sub (oneRef j).castSucc (Fin.last (productCount j)))
      let p3 := UniformScalarPreparation.Program.step p2
        (.mul (HRef j).castSucc.castSucc (Fin.last (productCount j + 1)))
      let p4 := UniformScalarPreparation.Program.step p3
        (.mul (scaleRef j).castSucc.castSucc.castSucc
          (powerRef j).castSucc.castSucc.castSucc)
      UniformScalarPreparation.Program.step p4
        (.mul (minusRef j).castSucc.castSucc.castSucc.castSucc
          (Fin.last (productCount j + 3)))

theorem productProgram_values (omega : ℂ) (j : ℕ) :
    (productProgram j).eval (roots omega) (rootRef j) = omega ∧
    (productProgram j).eval (roots omega) (oneRef j) = 1 ∧
    (productProgram j).eval (roots omega) (minusRef j) = -1 ∧
    (productProgram j).eval (roots omega) (powerRef j) = omega ^ j ∧
    (productProgram j).eval (roots omega) (HRef j) = NewtonFourier.H omega j ∧
    (productProgram j).eval (roots omega) (scaleRef j) = scale omega j := by
  induction j with
  | zero =>
      norm_num [productProgram, UniformScalarPreparation.Program.eval,
        eval_step, Instruction.eval, productCount, roots, rootRef, oneRef, minusRef,
        powerRef, HRef, scaleRef, Fin.snoc, Fin.lastCases]
  | succ j ih =>
      rcases ih with ⟨hr, h1, hm, hp, hH, hs⟩
      simp only [productProgram, rootRef_succ, oneRef_succ, minusRef_succ,
        powerRef_succ, HRef_succ, scaleRef_succ, eval_step,
        Fin.snoc_castSucc, Fin.snoc_last, Instruction.eval, hr, h1, hm, hp, hH, hs]
      simp only [pow_succ, H_succ, scale_succ]
      constructor
      · trivial
      constructor
      · trivial
      constructor
      · trivial
      constructor
      · trivial
      constructor
      · trivial
      · ring

theorem productProgram_admissible (omega : ℂ) (j : ℕ) :
    (productProgram j).Admissible (roots omega) := by
  induction j with
  | zero => simp [productProgram, admissible_step,
      UniformScalarPreparation.Program.Admissible, Instruction.Admissible]
  | succ j ih =>
      simpa only [productProgram, admissible_step,
        Instruction.Admissible, and_true] using ih

theorem productCount_mono {j k : ℕ} (h : j ≤ k) : productCount j ≤ productCount k := by
  rw [productCount_formula, productCount_formula]
  omega

def productLift {j k : ℕ} (h : j ≤ k) (i : Fin (productCount j)) :
    Fin (productCount k) := Fin.castLE (productCount_mono h) i

theorem productLift_succ (j : ℕ) (i : Fin (productCount j)) :
    productLift (Nat.le_succ j) i = i.castSucc.castSucc.castSucc.castSucc.castSucc := rfl

theorem productProgram_old (omega : ℂ) (j : ℕ) (i : Fin (productCount j)) :
    (productProgram (j + 1)).eval (roots omega) (productLift (Nat.le_succ j) i) =
      (productProgram j).eval (roots omega) i := by
  simp only [productLift_succ, productProgram, eval_step, Fin.snoc_castSucc]

theorem productProgram_preserves (omega : ℂ) {j k : ℕ} (h : j ≤ k)
    (i : Fin (productCount j)) :
    (productProgram k).eval (roots omega) (productLift h i) =
      (productProgram j).eval (roots omega) i := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
      have heq : productLift (Nat.le_succ_of_le h) i =
          productLift (Nat.le_succ k) (productLift h i) := rfl
      rw [heq, productProgram_old, ih]

/-- The complete product table shares all earlier power/H/scale registers. -/
theorem productProgram_table (omega : ℂ) (n : ℕ) (j : Fin n) :
    (productProgram n).eval (roots omega) (productLift (Nat.le_of_lt j.isLt) (powerRef j)) =
        omega ^ j.val ∧
    (productProgram n).eval (roots omega) (productLift (Nat.le_of_lt j.isLt) (HRef j)) =
        NewtonFourier.H omega j.val ∧
    (productProgram n).eval (roots omega) (productLift (Nat.le_of_lt j.isLt) (scaleRef j)) =
        scale omega j.val := by
  simp only [productProgram_preserves]
  exact ⟨(productProgram_values omega j).2.2.2.1,
    (productProgram_values omega j).2.2.2.2.1,
    (productProgram_values omega j).2.2.2.2.2⟩

@[reducible] def inverseCount (n : ℕ) : ℕ → ℕ
  | 0 => productCount n
  | j + 1 => inverseCount n j + 3

theorem inverseCount_formula (n j : ℕ) : inverseCount n j = 5 * n + 3 * j + 3 := by
  induction j with
  | zero => exact productCount_formula n
  | succ j ih => simp only [inverseCount, ih]; omega

theorem inverseCount_base (n j : ℕ) : productCount n ≤ inverseCount n j := by
  rw [productCount_formula, inverseCount_formula]
  omega

def baseLift (n j : ℕ) (i : Fin (productCount n)) : Fin (inverseCount n j) :=
  Fin.castLE (inverseCount_base n j) i

def tableRef (n j : ℕ) (index : Fin n) (ref : Fin (productCount index.val)) :
    Fin (inverseCount n j) := baseLift n j (productLift (Nat.le_of_lt index.isLt) ref)

def inverseOne (n j : ℕ) : Fin (inverseCount n j) := baseLift n j (oneRef n)
def inverseH (n j : ℕ) (index : Fin n) : Fin (inverseCount n j) :=
  tableRef n j index (HRef index)
def inverseScale (n j : ℕ) (index : Fin n) : Fin (inverseCount n j) :=
  tableRef n j index (scaleRef index)

theorem baseLift_succ (n j : ℕ) (i : Fin (productCount n)) :
    baseLift n (j+1) i = (baseLift n j i).castSucc.castSucc.castSucc := rfl

/-- Three further registers per coefficient: inverse H, D, inverse D.  The
construction tests only its natural loop bound; roots/coefficients are never tested. -/
def inverseProgram (n : ℕ) : (j : ℕ) → j ≤ n → ScalarProgram 1 (inverseCount n j)
  | 0, _ => productProgram n
  | j + 1, h =>
      let index : Fin n := ⟨j, by omega⟩
      let p1 := UniformScalarPreparation.Program.step (inverseProgram n j (by omega))
        (.divide (inverseOne n j) (inverseH n j index))
      let p2 := UniformScalarPreparation.Program.step p1
        (.mul (inverseH n j index).castSucc (inverseScale n j index).castSucc)
      UniformScalarPreparation.Program.step p2
        (.divide (inverseOne n j).castSucc.castSucc (Fin.last (inverseCount n j + 1)))

theorem inverseProgram_old (omega : ℂ) (n j : ℕ) (h : j+1 ≤ n)
    (i : Fin (inverseCount n j)) :
    (inverseProgram n (j+1) h).eval (roots omega) i.castSucc.castSucc.castSucc =
      (inverseProgram n j (by omega)).eval (roots omega) i := by
  simp only [inverseProgram, eval_step, Fin.snoc_castSucc]

theorem inverseProgram_base (omega : ℂ) (n j : ℕ) (h : j ≤ n)
    (i : Fin (productCount n)) :
    (inverseProgram n j h).eval (roots omega) (baseLift n j i) =
      (productProgram n).eval (roots omega) i := by
  induction j with
  | zero => rfl
  | succ j ih => rw [baseLift_succ, inverseProgram_old, ih]

theorem inverseProgram_inputs (omega : ℂ) (n j : ℕ) (h : j ≤ n) (index : Fin n) :
    (inverseProgram n j h).eval (roots omega) (inverseOne n j) = 1 ∧
    (inverseProgram n j h).eval (roots omega) (inverseH n j index) =
        NewtonFourier.H omega index.val ∧
    (inverseProgram n j h).eval (roots omega) (inverseScale n j index) =
        scale omega index.val := by
  simp only [inverseOne, inverseH, inverseScale, tableRef, inverseProgram_base,
    productProgram_preserves]
  exact ⟨(productProgram_values omega n).2.1,
    (productProgram_values omega index).2.2.2.2.1,
    (productProgram_values omega index).2.2.2.2.2⟩


theorem inverseProgram_admissible {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) (j : ℕ) (h : j ≤ n) :
    (inverseProgram n j h).Admissible (roots omega) := by
  induction j with
  | zero => exact productProgram_admissible omega n
  | succ j ih =>
      let index : Fin n := ⟨j, by omega⟩
      have valid := ih (by omega)
      rcases inverseProgram_inputs omega n j (by omega) index with ⟨h1, hH, hs⟩
      simp only [inverseProgram, admissible_step, Instruction.Admissible, eval_step,
        Fin.snoc_castSucc, Fin.snoc_last, Instruction.eval, and_true]
      change ((inverseProgram n j _).Admissible (roots omega) ∧
        (inverseProgram n j _).eval (roots omega) (inverseH n j index) ≠ 0) ∧
        (inverseProgram n j _).eval (roots omega) (inverseH n j index) *
          (inverseProgram n j _).eval (roots omega) (inverseScale n j index) ≠ 0
      rw [hH, hs]
      exact ⟨⟨valid, Hvalue_ne_zero hroot index⟩,
        diagonalValue_ne_zero hn hroot index⟩

theorem inverseCount_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) :
    inverseCount n j ≤ inverseCount n k := by
  rw [inverseCount_formula, inverseCount_formula]
  omega

def inverseLift (n : ℕ) {j k : ℕ} (h : j ≤ k) (i : Fin (inverseCount n j)) :
    Fin (inverseCount n k) := Fin.castLE (inverseCount_mono n h) i

theorem inverseLift_succ (n j : ℕ) (i : Fin (inverseCount n j)) :
    inverseLift n (Nat.le_succ j) i = i.castSucc.castSucc.castSucc := rfl

theorem inverseProgram_preserves (omega : ℂ) (n : ℕ) {j k : ℕ}
    (h : j ≤ k) (hk : k ≤ n) (i : Fin (inverseCount n j)) :
    (inverseProgram n k hk).eval (roots omega) (inverseLift n h i) =
      (inverseProgram n j (h.trans hk)).eval (roots omega) i := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
      have heq : inverseLift n (Nat.le_succ_of_le h) i =
          inverseLift n (Nat.le_succ k) (inverseLift n h i) := rfl
      rw [heq, inverseLift_succ, inverseProgram_old, ih]

theorem inverseProgram_new (omega : ℂ) (n : ℕ) (j : Fin n) :
    (inverseProgram n (j.val+1) (Nat.succ_le_of_lt j.isLt)).eval (roots omega)
        (Fin.last (inverseCount n j.val)).castSucc.castSucc =
      (NewtonFourier.H omega j.val)⁻¹ ∧
    (inverseProgram n (j.val+1) (Nat.succ_le_of_lt j.isLt)).eval (roots omega)
        (Fin.last (inverseCount n j.val+1)).castSucc =
      diagonalValue omega j.val ∧
    (inverseProgram n (j.val+1) (Nat.succ_le_of_lt j.isLt)).eval (roots omega)
        (Fin.last (inverseCount n j.val+2)) = (diagonalValue omega j.val)⁻¹ := by
  rcases inverseProgram_inputs omega n j.val (Nat.le_of_lt j.isLt) j with ⟨h1,hH,hs⟩
  simpa only [inverseProgram, eval_step, Fin.snoc_castSucc, Fin.snoc_last,
    Instruction.eval, h1,hH,hs, one_div, diagonalValue] using
      (show True ∧ True ∧ True from ⟨True.intro,True.intro,True.intro⟩)

def finalProgram (n : ℕ) : ScalarProgram 1 (inverseCount n n) :=
  inverseProgram n n (le_refl n)

def finalH (n : ℕ) (j : Fin n) : Fin (inverseCount n n) := inverseH n n j
def finalScale (n : ℕ) (j : Fin n) : Fin (inverseCount n n) := inverseScale n n j

def finalInvH (n : ℕ) (j : Fin n) : Fin (inverseCount n n) :=
  inverseLift n (Nat.succ_le_of_lt j.isLt)
    (Fin.last (inverseCount n j.val)).castSucc.castSucc

def finalDiagonal (n : ℕ) (j : Fin n) : Fin (inverseCount n n) :=
  inverseLift n (Nat.succ_le_of_lt j.isLt)
    (Fin.last (inverseCount n j.val+1)).castSucc

def finalInvDiagonal (n : ℕ) (j : Fin n) : Fin (inverseCount n n) :=
  inverseLift n (Nat.succ_le_of_lt j.isLt) (Fin.last (inverseCount n j.val+2))

theorem finalProgram_values (omega : ℂ) (n : ℕ) (j : Fin n) :
    (finalProgram n).eval (roots omega) (finalH n j) = NewtonFourier.H omega j.val ∧
    (finalProgram n).eval (roots omega) (finalScale n j) = scale omega j.val ∧
    (finalProgram n).eval (roots omega) (finalInvH n j) = (NewtonFourier.H omega j.val)⁻¹ ∧
    (finalProgram n).eval (roots omega) (finalDiagonal n j) = diagonalValue omega j.val ∧
    (finalProgram n).eval (roots omega) (finalInvDiagonal n j) = (diagonalValue omega j.val)⁻¹ := by
  rcases inverseProgram_inputs omega n n (le_refl n) j with ⟨_,hH,hs⟩
  rcases inverseProgram_new omega n j with ⟨hiH,hD,hiD⟩
  simpa only [finalProgram, finalH, finalScale, finalInvH, finalDiagonal,
    finalInvDiagonal, inverseProgram_preserves] using ⟨hH,hs,hiH,hD,hiD⟩

/-- Shared output table: (H_j, scale_j, H_j⁻¹, D_j, D_j⁻¹), in row-major order. -/
def table (n : ℕ) : UniformScalarPreparation.DAG 1 (n*5) where
  length := inverseCount n n
  program := finalProgram n
  output i :=
    let jq := finProdFinEquiv.symm i
    if jq.2.val = 0 then finalH n jq.1
    else if jq.2.val = 1 then finalScale n jq.1
    else if jq.2.val = 2 then finalInvH n jq.1
    else if jq.2.val = 3 then finalDiagonal n jq.1
    else finalInvDiagonal n jq.1

theorem table_length (n : ℕ) : (table n).length = 8*n+3 := by
  dsimp [table]
  rw [inverseCount_formula]
  omega

theorem table_admissible {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) : (table n).Admissible (roots omega) :=
  inverseProgram_admissible hn hroot n (le_refl n)

noncomputable def expected (omega : ℂ) (j : ℕ) (q : Fin 5) : ℂ :=
  if q.val = 0 then NewtonFourier.H omega j
  else if q.val = 1 then scale omega j
  else if q.val = 2 then (NewtonFourier.H omega j)⁻¹
  else if q.val = 3 then diagonalValue omega j
  else (diagonalValue omega j)⁻¹

theorem table_run {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) (j : Fin n) (q : Fin 5) :
    (table n).run (roots omega) (table_admissible hn hroot) (finProdFinEquiv (j,q)) =
      expected omega j.val q := by
  rcases finalProgram_values omega n j with ⟨hH,hs,hiH,hD,hiD⟩
  fin_cases q <;>
    simp [UniformScalarPreparation.DAG.run, UniformScalarPreparation.Program.run,
      table, expected, hH,hs,hiH,hD,hiD]

/-- Factorization using the actually prepared diagonal outputs. -/
theorem fourier_factorization_prepared {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    RadixTwo.dft n omega = N n omega *
      (Matrix.diagonal (fun j : Fin n =>
        (table n).run (roots omega) (table_admissible hn hroot)
          (finProdFinEquiv (j, (3 : Fin 5)))))⁻¹ * (N n omega).transpose := by
  have heq : (fun j : Fin n =>
      (table n).run (roots omega) (table_admissible hn hroot)
        (finProdFinEquiv (j, (3 : Fin 5)))) =
      fun j : Fin n => diagonalValue omega j.val := by
    funext j
    exact (table_run hn hroot j (3 : Fin 5)).trans (by rfl)
  rw [heq]
  exact fourier_factorization hn hroot


noncomputable def preparedToeplitz {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if j.val ≤ i.val then
    (table n).run (roots omega) (table_admissible hn hroot)
      (finProdFinEquiv (⟨i.val-j.val, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,
        (2 : Fin 5)))
  else 0

theorem preparedToeplitz_eq {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    preparedToeplitz hn hroot = truncMatrix n (invH omega) := by
  ext i j
  unfold preparedToeplitz truncMatrix
  split_ifs with hij
  · exact (table_run hn hroot _ (2 : Fin 5)).trans (by
      simp [expected, invH, PowerSeries.coeff_mk])
  · rfl

/-- The actual shared table supplies every diagonal and Toeplitz entry. -/
theorem N_toeplitz_prepared {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    N n omega =
      Matrix.diagonal (fun j : Fin n =>
        (table n).run (roots omega) (table_admissible hn hroot)
          (finProdFinEquiv (j, (0 : Fin 5)))) * preparedToeplitz hn hroot *
      Matrix.diagonal (fun j : Fin n =>
        (table n).run (roots omega) (table_admissible hn hroot)
          (finProdFinEquiv (j, (1 : Fin 5)))) := by
  have hH : (fun j : Fin n => (table n).run (roots omega) (table_admissible hn hroot)
      (finProdFinEquiv (j, (0 : Fin 5)))) = fun j => NewtonFourier.H omega j.val := by
    funext j
    exact (table_run hn hroot j (0 : Fin 5)).trans (by rfl)
  have hs : (fun j : Fin n => (table n).run (roots omega) (table_admissible hn hroot)
      (finProdFinEquiv (j, (1 : Fin 5)))) = fun j => scale omega j.val := by
    funext j
    exact (table_run hn hroot j (1 : Fin 5)).trans (by rfl)
  rw [hH,hs,preparedToeplitz_eq]
  exact N_toeplitz_factorization hroot

theorem diagonal_inverse {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    (Matrix.diagonal (fun j : Fin n => diagonalValue omega j.val))⁻¹ =
      Matrix.diagonal (fun j : Fin n => (diagonalValue omega j.val)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have heq : (fun j : Fin n => (diagonalValue omega j.val)⁻¹ * diagonalValue omega j.val) =
      fun _ : Fin n => (1 : ℂ) := by
    funext j
    exact inv_mul_cancel₀ (diagonalValue_ne_zero hn hroot j)
  rw [heq]
  exact Matrix.diagonal_one

/-- Diagonal inversion itself is already prepared by the root/rational DAG. -/
theorem fourier_factorization_prepared_reciprocal {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) :
    RadixTwo.dft n omega = N n omega *
      Matrix.diagonal (fun j : Fin n =>
        (table n).run (roots omega) (table_admissible hn hroot)
          (finProdFinEquiv (j, (4 : Fin 5)))) * (N n omega).transpose := by
  have heq : (fun j : Fin n =>
      (table n).run (roots omega) (table_admissible hn hroot)
        (finProdFinEquiv (j, (4 : Fin 5)))) =
      fun j : Fin n => (diagonalValue omega j.val)⁻¹ := by
    funext j
    exact (table_run hn hroot j (4 : Fin 5)).trans (by rfl)
  rw [heq, ← diagonal_inverse hn hroot]
  exact fourier_factorization hn hroot

/-- Canonical positive-exponent Fourier matrix with computably selected tables. -/
theorem specified_factorization_prepared (n : ℕ) (hn : 0 < n) :
    fourierMatrix n = N n (zeta n) *
      Matrix.diagonal (fun j : Fin n =>
        (table n).run (roots (zeta n))
          (table_admissible hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)))
            (finProdFinEquiv (j, (4 : Fin 5)))) * (N n (zeta n)).transpose :=
  fourier_factorization_prepared_reciprocal hn
    (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))


end Preparation

end ExactFourierCircuits.UniformNewton
