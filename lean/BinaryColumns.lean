import BinaryTensor
import FrameSpectrum

set_option autoImplicit false

namespace ExactFourierCircuits.BinaryColumns
open BinaryFrames BinaryTensor FrameSpectrum
open scoped BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] {f : ℕ}

/-- One column of the concrete global binary address. -/
def column (ξ : Vec (Fin f × ι)) (c : Fin f) : Vec ι := fun i => ξ (c, i)

/-- The copied frame vector for column c, with right coordinate inside. -/
def columnFamily (z : κ → Vec ι) : Fin f × κ → Vec (Fin f × ι) :=
  fun ck => tensor (unit ck.1) (z ck.2)

section Frames
variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] in
lemma columnFamily_orthonormal (z : κ → Vec ι)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) (p q : Fin f × κ) :
    dot (columnFamily z p) (columnFamily z q) = if p = q then 1 else 0 :=
  tensor_orthonormal unit z dot_units hz p q

lemma weight_unit (c : Fin f) : weight (unit c) = 1 := by
  simp only [weight, unit, apply_ite, bit_one, bit_zero]
  simp

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma columnFamily_weight (z : κ → Vec ι) (c : Fin f) (k : κ) :
    weight (columnFamily z (c, k)) = weight (z k) := by
  rw [columnFamily, weight_tensor, weight_unit, one_mul]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma columnFamily_weightModFour (z : κ → Vec ι) (c : Fin f) (k : κ) :
    weightModFour (columnFamily z (c, k)) = weightModFour (z k) := by
  rw [weightModFour, columnFamily_weight]
  rfl

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma dot_columnFamily (z : κ → Vec ι) (ξ : Vec (Fin f × ι)) (c : Fin f) (k : κ) :
    dot (columnFamily z (c, k)) ξ = dot (z k) (column ξ c) := by
  simp only [dot, columnFamily, tensor, Fintype.sum_prod_type]
  calc
    _ = ∑ d : Fin f, unit c d * (∑ i, z k i * ξ (d, i)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [unit, column]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Copied projections act separately in every actual address column. -/
lemma columnFamily_projection_block (z : κ → Vec ι) (ξ : Vec (Fin f × ι))
    (c : Fin f) (i : ι) :
    frameProjection (columnFamily z) ξ (c, i) = frameProjection z (column ξ c) i := by
  simp only [frameProjection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  simp_rw [dot_columnFamily]
  simp only [columnFamily, tensor]
  rw [Finset.sum_eq_single c]
  · simp [unit]
  · intro d hd hdc
    simp [unit, Ne.symm hdc]
  · simp

omit [DecidableEq ι] [DecidableEq κ] in
lemma columnFamily_projection (z : κ → Vec ι) (ξ : Vec (Fin f × ι)) :
    frameProjection (columnFamily z) ξ =
      fun ci => frameProjection z (column ξ ci.1) ci.2 := by
  ext ci
  exact columnFamily_projection_block z ξ ci.1 ci.2

omit [DecidableEq ι] in
lemma weight_columns (ξ : Vec (Fin f × ι)) : weight ξ = ∑ c, weight (column ξ c) := by
  simp only [weight, Fintype.sum_prod_type, column]

omit [DecidableEq ι] in
lemma weightModFour_columns (ξ : Vec (Fin f × ι)) :
    weightModFour ξ = ∑ c, weightModFour (column ξ c) := by
  simp only [weightModFour, weight_columns, Nat.cast_sum]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The copied frame's total spectral exponent is the sum of the per-column exponents. -/
lemma columnFamily_projection_weightModFour (z : κ → Vec ι) (ξ : Vec (Fin f × ι)) :
    weightModFour (frameProjection (columnFamily z) ξ) =
      ∑ c, weightModFour (frameProjection z (column ξ c)) := by
  rw [weightModFour_columns]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  ext i
  exact columnFamily_projection_block z ξ c i

omit [DecidableEq ι] [DecidableEq κ] in
lemma columnFamily_projection_phase (z : κ → Vec ι) (ξ : Vec (Fin f × ι)) :
    phase (weightModFour (frameProjection (columnFamily z) ξ)) =
      ∏ c, phase (weightModFour (frameProjection z (column ξ c))) := by
  rw [columnFamily_projection_weightModFour, phase_finset_sum]

/-- The copied directional word acts on the whole array with the column-summed frame exponent. -/
lemma columnFamily_signedWord (z : κ → Vec ι) (decreasing : Bool)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) :
    signedWord (columnFamily (f := f) z) decreasing Finset.univ.toList =
      frameMap (fun ξ => edgeSign decreasing *
        ∑ c, weightModFour (frameProjection z (column ξ c))) := by
  have hunit (p : Fin f × κ) : dot (columnFamily z p) (columnFamily z p) = 1 := by
    simpa using columnFamily_orthonormal z hz p p
  have horth (p q : Fin f × κ) (hpq : p ≠ q) : dot (columnFamily z p) (columnFamily z q) = 0 := by
    simpa [hpq] using columnFamily_orthonormal z hz p q
  rw [signedWord_frame _ decreasing hunit horth]
  congr 1
  funext ξ
  rw [columnFamily_projection_weightModFour]

end Frames

/-- The translation direction repeats u in every column. -/
def globalDirection (u : Vec ι) : Vec (Fin f × ι) := fun ci => u ci.2

def columnLineExponent (u : Vec ι) (ξ : Vec (Fin f × ι)) : ZMod 4 :=
  ∑ c, lineExponent u (column ξ c)

def columnPerpExponent (u : Vec ι) (ξ : Vec (Fin f × ι)) : ZMod 4 :=
  ∑ c, perpExponent u (column ξ c)

omit [DecidableEq ι] in
lemma dot_globalDirection (u : Vec ι) (ξ : Vec (Fin f × ι)) :
    dot (globalDirection u) ξ = ∑ c, dot u (column ξ c) := by
  simp only [dot, globalDirection, column, Fintype.sum_prod_type]

lemma binarySign_finset_sum {ν : Type*} (s : Finset ν) (a : ν → F2) :
    binarySign (∑ i ∈ s, a i) = ∏ i ∈ s, binarySign (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, binarySign_add, ih]

omit [DecidableEq ι] in
/-- Exceptional terminal ratio, with all column phases and translation signs combined exactly. -/
lemma column_terminal_phase (u : Vec ι) (ξ : Vec (Fin f × ι)) (hu : dot u u = 1) :
    phase (columnPerpExponent u ξ - columnLineExponent u ξ) =
      phase (weightModFour ξ) * binarySign (dot (globalDirection u) ξ) := by
  rw [columnPerpExponent, columnLineExponent, ← Finset.sum_sub_distrib, phase_finset_sum]
  simp_rw [terminal_weight_ratio u _ hu, phase_add, ← binarySign_phase]
  rw [Finset.prod_mul_distrib, ← phase_finset_sum, ← binarySign_finset_sum,
    ← weightModFour_columns, ← dot_globalDirection]

/-- Whole-array terminal identity. No positivity assumption on the column count is needed. -/
theorem column_terminal_frame_ratio (u : Vec ι) (hu : dot u u = 1) :
    (frameMap (columnPerpExponent (f := f) u)).comp
      (frameMap (fun ξ => -columnLineExponent u ξ)) =
      (translateMap (globalDirection u)).comp (frameMap weightModFour) := by
  apply operator_eq_of_characters
  intro ξ
  simp only [LinearMap.comp_apply, frameMap_character, map_smul,
    translate_character, smul_smul]
  congr 1
  calc
    _ = phase (columnPerpExponent u ξ - columnLineExponent u ξ) := by
      rw [← phase_add, add_comm, sub_eq_add_neg]
    _ = _ := column_terminal_phase u ξ hu


omit [DecidableEq ι] in
/-- Zero copied columns have zero projection, even with a nonempty source frame. -/
lemma zero_columns_projection [Fintype κ] (z : κ → Vec ι) (ξ : Vec (Fin 0 × ι)) :
    frameProjection (columnFamily z) ξ = 0 := by
  simp [frameProjection]

omit [DecidableEq ι] in
/-- A zero-dimensional source frame has zero copied projection for every column count. -/
lemma empty_frame_projection (z : Empty → Vec ι) (ξ : Vec (Fin f × ι)) :
    frameProjection (columnFamily z) ξ = 0 := by
  simp [frameProjection]

/-- The empty global address has identity terminal frame ratio, without a norm hypothesis. -/
lemma zero_columns_terminal_ratio (u : Vec ι) :
    (frameMap (columnPerpExponent (f := 0) u)).comp
      (frameMap (fun ξ => -columnLineExponent u ξ)) = LinearMap.id := by
  have hP : columnPerpExponent (f := 0) u = fun _ => 0 := by
    funext ξ
    simp [columnPerpExponent]
  have hL : (fun ξ => -columnLineExponent (f := 0) u ξ) = fun _ => 0 := by
    funext ξ
    simp [columnLineExponent]
  rw [hP, hL, frameMap_zero]
  simp

end
end ExactFourierCircuits.BinaryColumns
