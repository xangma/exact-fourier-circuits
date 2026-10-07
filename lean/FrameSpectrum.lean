import BinaryTensor
import KernelIdentities
import ProjectionIdentities

set_option autoImplicit false

namespace ExactFourierCircuits.FrameSpectrum
open scoped BigOperators
open BinaryFrames BinaryTensor
noncomputable section

def phase (q : ZMod 4) : ℂ := Complex.I ^ q.val

theorem I_pow_four : (Complex.I : ℂ) ^ 4 = 1 := by
  calc
    _ = (Complex.I ^ 2) ^ 2 := by ring
    _ = 1 := by rw [Complex.I_sq]; norm_num

theorem I_pow_mod_four (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4]
  rw [pow_add, pow_mul, I_pow_four, one_pow, mul_one]

theorem phase_natCast (n : ℕ) : phase (n : ZMod 4) = Complex.I ^ n := by
  simp only [phase, ZMod.val_natCast]
  exact I_pow_mod_four n

@[simp] theorem phase_zero : phase 0 = 1 := by
  change Complex.I ^ 0 = 1
  simp

@[simp] theorem phase_one : phase 1 = Complex.I := by
  change Complex.I ^ 1 = Complex.I
  simp

@[simp] theorem phase_neg_one : phase (-1) = -Complex.I := by
  change Complex.I ^ 3 = -Complex.I
  simp [pow_succ]

theorem phase_add (q r : ZMod 4) : phase (q + r) = phase q * phase r := by
  calc
    _ = phase ((q.val + r.val : ℕ) : ZMod 4) := by
      simp [Nat.cast_add]
    _ = Complex.I ^ (q.val + r.val) := phase_natCast _
    _ = _ := by rw [pow_add]; rfl

theorem phase_ne_zero (q : ZMod 4) : phase q ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

theorem phase_neg (q : ZMod 4) : phase (-q) = (phase q)⁻¹ := by
  apply mul_right_cancel₀ (phase_ne_zero q)
  rw [← phase_add, neg_add_cancel, phase_zero, inv_mul_cancel₀ (phase_ne_zero q)]

theorem phase_finset_sum {κ : Type*} (s : Finset κ) (q : κ → ZMod 4) :
    phase (∑ i ∈ s, q i) = ∏ i ∈ s, phase (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, phase_add, ih]

theorem binary_cases (c : F2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

def binarySign (c : F2) : ℂ := (-1) ^ bit c

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_add (c d : F2) : binarySign (c + d) = binarySign c * binarySign d := by
  rcases binary_cases c with rfl | rfl <;> rcases binary_cases d with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

theorem binarySign_phase (c : F2) : binarySign c = phase (2 * (bit c : ZMod 4)) := by
  rcases binary_cases c with rfl | rfl
  · simp
  · simp only [bit_one, Nat.cast_one, mul_one, binarySign_one]
    change (-1 : ℂ) = Complex.I ^ 2
    exact Complex.I_sq.symm

theorem kernel_phase (c : F2) : a + b * binarySign c = phase (bit c : ZMod 4) := by
  rcases binary_cases c with rfl | rfl <;> simp [a, b] <;> ring

theorem inverse_kernel_phase (c : F2) : b + a * binarySign c = phase (-(bit c : ZMod 4)) := by
  rcases binary_cases c with rfl | rfl <;> simp [a, b] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Array := Vec ι → ℂ
abbrev Operator := Array (ι := ι) →ₗ[ℂ] Array (ι := ι)

def character (ξ : Vec ι) : Array (ι := ι) := fun x => binarySign (dot ξ x)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem vec_add_self (x : Vec ι) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

omit [DecidableEq ι] in
theorem character_comm (x y : Vec ι) : character x y = character y x := by
  simp only [character, dot_comm]

omit [DecidableEq ι] in
theorem character_add (ξ x y : Vec ι) :
    character ξ (x + y) = character ξ x * character ξ y := by
  change binarySign (dot ξ (x + y)) = binarySign (dot ξ x) * binarySign (dot ξ y)
  rw [dot_add_right, binarySign_add]

omit [DecidableEq ι] in
@[simp] theorem character_zero (x : Vec ι) : character 0 x = 1 := by
  simp [character, dot]

omit [DecidableEq ι] in
@[simp] theorem character_at_zero (ξ : Vec ι) : character ξ 0 = 1 := by
  rw [character_comm, character_zero]

def translateMap (z : Vec ι) : Operator (ι := ι) where
  toFun := Projection.translate z
  map_add' f g := by ext x; simp [Projection.translate]
  map_smul' c f := by ext x; simp [Projection.translate]

def directionalMap (z : Vec ι) : Operator (ι := ι) where
  toFun := Projection.directionalC z
  map_add' f g := by ext x; simp only [Projection.directionalC, Pi.add_apply]; ring
  map_smul' c f := by
    ext x
    simp only [Projection.directionalC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def inverseDirectionalMap (z : Vec ι) : Operator (ι := ι) where
  toFun := Projection.inverseDirectionalC z
  map_add' f g := by ext x; simp only [Projection.inverseDirectionalC, Pi.add_apply]; ring
  map_smul' c f := by
    ext x
    simp only [Projection.inverseDirectionalC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [DecidableEq ι] in
theorem translate_character (z ξ : Vec ι) :
    translateMap z (character ξ) = binarySign (dot z ξ) • character ξ := by
  ext x
  change character ξ (x + z) = binarySign (dot z ξ) * character ξ x
  rw [character_add]
  simp only [character, dot_comm ξ z]
  ring

omit [DecidableEq ι] in
theorem directional_character (z ξ : Vec ι) :
    directionalMap z (character ξ) = phase (bit (dot z ξ) : ZMod 4) • character ξ := by
  ext x
  change a * character ξ x + b * character ξ (x + z) =
    phase (bit (dot z ξ) : ZMod 4) * character ξ x
  rw [character_add]
  change a * character ξ x + b * (character ξ x * binarySign (dot ξ z)) = _
  rw [dot_comm ξ z]
  calc
    _ = (a + b * binarySign (dot z ξ)) * character ξ x := by ring
    _ = _ := by rw [kernel_phase]

omit [DecidableEq ι] in
theorem inverse_directional_character (z ξ : Vec ι) :
    inverseDirectionalMap z (character ξ) =
      phase (-(bit (dot z ξ) : ZMod 4)) • character ξ := by
  ext x
  change b * character ξ x + a * character ξ (x + z) =
    phase (-(bit (dot z ξ) : ZMod 4)) * character ξ x
  rw [character_add]
  change b * character ξ x + a * (character ξ x * binarySign (dot ξ z)) = _
  rw [dot_comm ξ z]
  calc
    _ = (b + a * binarySign (dot z ξ)) * character ξ x := by ring
    _ = _ := by rw [inverse_kernel_phase]

omit [Fintype ι] [DecidableEq ι] in
theorem inverse_directional_translation (z : Vec ι) :
    inverseDirectionalMap z = (translateMap z).comp (directionalMap z) := by
  apply LinearMap.ext
  intro f
  ext x
  change b * f x + a * f (x + z) = a * f (x + z) + b * f ((x + z) + z)
  rw [add_assoc, vec_add_self, add_zero]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem directional_square (z : Vec ι) :
    (directionalMap z).comp (directionalMap z) = translateMap z := by
  apply LinearMap.ext
  intro f
  ext x
  change a * (a * f x + b * f (x + z)) +
    b * (a * f (x + z) + b * f ((x + z) + z)) = f (x + z)
  rw [add_assoc, vec_add_self, add_zero]
  unfold a b
  ring_nf
  simp [Complex.I_sq]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem directional_inverse (z : Vec ι) :
    (directionalMap z).comp (inverseDirectionalMap z) = LinearMap.id ∧
      (inverseDirectionalMap z).comp (directionalMap z) = LinearMap.id := by
  constructor
  · apply LinearMap.ext
    intro f
    exact (Projection.directionalC_inverse z (vec_add_self z) f).1
  · apply LinearMap.ext
    intro f
    exact (Projection.directionalC_inverse z (vec_add_self z) f).2

theorem character_sum_nonzero (z : Vec ι) (hz : z ≠ 0) :
    (∑ x : Vec ι, character z x) = 0 := by
  classical
  have hex : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    ext i
    exact h i
  obtain ⟨p, hp⟩ := hex
  have hp1 : z p = 1 := (binary_cases (z p)).resolve_left hp
  have hshift (x : Vec ι) : character z (x + unit p) = -character z x := by
    rw [character_add]
    simp only [character, dot_unit_right, hp1, binarySign_one, mul_neg_one]
  have h : (∑ x : Vec ι, character z x) = -(∑ x : Vec ι, character z x) := by
    calc
      _ = ∑ x : Vec ι, character z (x + unit p) :=
        (Equiv.sum_comp (Equiv.addRight (unit p)) (character z)).symm
      _ = _ := by simp only [hshift, Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) * (∑ x : Vec ι, character z x) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem character_sum (z : Vec ι) :
    (∑ x : Vec ι, character z x) = if z = 0 then (Fintype.card (Vec ι) : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · subst z; simp
  · simp [hz, character_sum_nonzero z hz]

theorem character_pair_sum (x y : Vec ι) :
    (∑ ξ : Vec ι, character ξ x * character ξ y) =
      if x = y then (Fintype.card (Vec ι) : ℂ) else 0 := by
  classical
  simp_rw [← character_add, character_comm _ (x + y)]
  rw [character_sum]
  by_cases hxy : x = y
  · subst y; simp
  · have hne : x + y ≠ 0 := by
      intro h
      have h' := congrArg (fun v : Vec ι => v + y) h
      simp only [add_assoc, vec_add_self, add_zero, zero_add] at h'
      exact hxy h'
    simp [hxy, hne]

def walsh (f : Array (ι := ι)) : Array (ι := ι) := fun ξ => ∑ x, character ξ x * f x

def walshMap : Operator (ι := ι) where
  toFun := walsh
  map_add' f g := by ext ξ; simp [walsh, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext ξ
    simp [walsh, Finset.mul_sum, mul_left_comm]

theorem walsh_square (f : Array (ι := ι)) :
    walsh (walsh f) = (Fintype.card (Vec ι) : ℂ) • f := by
  ext x
  simp only [walsh, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y, (∑ ξ, character ξ x * character ξ y) * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [character_comm x ξ]
      ring
    _ = _ := by simp [character_pair_sum]

theorem walsh_character (ξ η : Vec ι) :
    walsh (character ξ) η = if η = ξ then (Fintype.card (Vec ι) : ℂ) else 0 := by
  simp only [walsh]
  simp_rw [character_comm η _, character_comm ξ _]
  exact character_pair_sum η ξ

theorem cardinal_ne_zero : (Fintype.card (Vec ι) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero (α := Vec ι)

/-- Complete finite Walsh expansion; this upgrades character identities to operator identities. -/
theorem character_expansion (f : Array (ι := ι)) :
    (Fintype.card (Vec ι) : ℂ)⁻¹ • (∑ ξ, walsh f ξ • character ξ) = f := by
  have h : (∑ ξ, walsh f ξ • character ξ) = (Fintype.card (Vec ι) : ℂ) • f := by
    ext x
    have hw := congrFun (walsh_square f) x
    simpa only [walsh, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      character_comm x _, mul_comm] using hw
  rw [h, smul_smul, inv_mul_cancel₀ cardinal_ne_zero, one_smul]

theorem operator_eq_of_characters (T U : Operator (ι := ι))
    (h : ∀ ξ, T (character ξ) = U (character ξ)) : T = U := by
  apply LinearMap.ext
  intro f
  rw [← character_expansion f]
  simp only [map_smul, map_sum, h]

def phaseMap (q : Vec ι → ZMod 4) : Operator (ι := ι) where
  toFun f := fun ξ => phase (q ξ) * f ξ
  map_add' f g := by ext ξ; simp [mul_add]
  map_smul' c f := by ext ξ; simp [mul_left_comm]

/-- Unnormalized Walsh conjugation, with the inverse cardinality supplied exactly. -/
def frameMap (q : Vec ι → ZMod 4) : Operator (ι := ι) :=
  (Fintype.card (Vec ι) : ℂ)⁻¹ •
    (walshMap.comp ((phaseMap q).comp walshMap))

theorem frameMap_character (q : Vec ι → ZMod 4) (ξ : Vec ι) :
    frameMap q (character ξ) = phase (q ξ) • character ξ := by
  have hd : phaseMap q (walshMap (character ξ)) =
      phase (q ξ) • walshMap (character ξ) := by
    ext η
    change phase (q η) * walsh (character ξ) η =
      phase (q ξ) * walsh (character ξ) η
    by_cases hη : η = ξ <;> simp [walsh_character, hη]
  change (Fintype.card (Vec ι) : ℂ)⁻¹ •
    walshMap (phaseMap q (walshMap (character ξ))) = _
  rw [hd, map_smul]
  change (Fintype.card (Vec ι) : ℂ)⁻¹ •
    (phase (q ξ) • walsh (walsh (character ξ))) = _
  rw [walsh_square, smul_smul, smul_smul]
  congr 1
  field_simp [cardinal_ne_zero]

theorem frameMap_zero : frameMap (fun _ : Vec ι => 0) = LinearMap.id := by
  apply operator_eq_of_characters
  intro ξ
  simp [frameMap_character]

theorem frameMap_comp (q r : Vec ι → ZMod 4) :
    (frameMap q).comp (frameMap r) = frameMap (fun ξ => q ξ + r ξ) := by
  apply operator_eq_of_characters
  intro ξ
  simp only [LinearMap.comp_apply, frameMap_character, map_smul, smul_smul, phase_add]
  rw [mul_comm]

theorem frameMap_inverse (q : Vec ι → ZMod 4) :
    (frameMap q).comp (frameMap (fun ξ => -q ξ)) = LinearMap.id ∧
      (frameMap (fun ξ => -q ξ)).comp (frameMap q) = LinearMap.id := by
  constructor <;> rw [frameMap_comp] <;> simp only [add_neg_cancel, neg_add_cancel]
  all_goals exact frameMap_zero

omit [DecidableEq ι] in
theorem norm_one_weightModFour (z : Vec ι) (hz : dot z z = 1) :
    weightModFour z = 1 ∨ weightModFour z = -1 := by
  have hw : weightModFour z = ((weight z % 4 : ℕ) : ZMod 4) :=
    (ZMod.natCast_mod (weight z) 4).symm
  rcases norm_one_weight_mod_four z hz with h | h
  · left; rw [hw, h]; rfl
  · right; rw [hw, h]; rfl

def edgeSign (decreasing : Bool) : ZMod 4 := if decreasing then -1 else 1

/-- Increasing: weight 1 uses C and weight 3 uses C inverse. Decreasing reverses both. -/
def signedMap (z : Vec ι) (decreasing : Bool) : Operator (ι := ι) :=
  if weightModFour z = 1 then
    if decreasing then inverseDirectionalMap z else directionalMap z
  else if decreasing then directionalMap z else inverseDirectionalMap z

omit [DecidableEq ι] in
theorem signedMap_character (z ξ : Vec ι) (decreasing : Bool) (hz : dot z z = 1) :
    signedMap z decreasing (character ξ) =
      phase (edgeSign decreasing * weightModFour z * (bit (dot z ξ) : ZMod 4)) •
        character ξ := by
  rcases norm_one_weightModFour z hz with h | h
  · cases decreasing <;>
      simp [signedMap, h, edgeSign, directional_character, inverse_directional_character]
  · have hnegone : (-1 : ZMod 4) ≠ 1 := by decide
    cases decreasing <;>
      simp [signedMap, h, hnegone, edgeSign, directional_character, inverse_directional_character]

variable {κ : Type*}

/-- A finite chronological composition of the actual signed directional kernels. -/
def signedWord (z : κ → Vec ι) (decreasing : Bool) : List κ → Operator (ι := ι)
  | [] => LinearMap.id
  | i :: is => (signedWord z decreasing is).comp (signedMap (z i) decreasing)

omit [DecidableEq ι] in
theorem signedWord_character (z : κ → Vec ι) (decreasing : Bool)
    (hunit : ∀ i, dot (z i) (z i) = 1) (is : List κ) (ξ : Vec ι) :
    signedWord z decreasing is (character ξ) =
      phase ((is.map (fun i => edgeSign decreasing * weightModFour (z i) *
        (bit (dot (z i) ξ) : ZMod 4))).sum) • character ξ := by
  induction is with
  | nil => simp [signedWord]
  | cons i is ih =>
    simp only [signedWord, LinearMap.comp_apply, signedMap_character _ _ _ (hunit i),
      map_smul, ih, smul_smul, List.map_cons, List.sum_cons, phase_add]

omit [DecidableEq ι] in
/-- The signed product phase is the phase of the binary orthogonal projection. -/
theorem signed_projection_phase [Fintype κ] (z : κ → Vec ι) (ξ : Vec ι)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    phase (weightModFour (frameProjection z ξ)) =
      ∏ i, phase (weightModFour (z i) * (bit (dot (z i) ξ) : ZMod 4)) := by
  rw [frameProjection_weightModFour z ξ horth, phase_finset_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [mul_comm]

/-- Whole-array identity, using Walsh completeness, for any orthonormal finite frame. -/
theorem signedWord_frame [Fintype κ] (z : κ → Vec ι) (decreasing : Bool)
    (hunit : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    signedWord z decreasing Finset.univ.toList =
      frameMap (fun ξ => edgeSign decreasing * weightModFour (frameProjection z ξ)) := by
  classical
  apply operator_eq_of_characters
  intro ξ
  rw [signedWord_character z decreasing hunit, frameMap_character, Finset.sum_map_toList]
  congr 2
  rw [frameProjection_weightModFour z ξ horth, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Different orthonormal frame descriptions give the same operator when their
    binary projection maps agree. Equality of spans can discharge this hypothesis. -/
theorem signedWords_same_projection [Fintype κ] {ν : Type*} [Fintype ν]
    (z : κ → Vec ι) (w : ν → Vec ι) (decreasing : Bool)
    (hzunit : ∀ i, dot (z i) (z i) = 1)
    (hzorth : ∀ i j, i ≠ j → dot (z i) (z j) = 0)
    (hwunit : ∀ i, dot (w i) (w i) = 1)
    (hworth : ∀ i j, i ≠ j → dot (w i) (w j) = 0)
    (hprojection : ∀ ξ, frameProjection z ξ = frameProjection w ξ) :
    signedWord z decreasing Finset.univ.toList = signedWord w decreasing Finset.univ.toList := by
  rw [signedWord_frame z decreasing hzunit hzorth, signedWord_frame w decreasing hwunit hworth]
  congr 1
  funext ξ
  rw [hprojection ξ]

/-- Frames are genuine equivalences, with negated phases as their inverse. -/
def frameEquiv (q : Vec ι → ZMod 4) : Array (ι := ι) ≃ₗ[ℂ] Array (ι := ι) where
  toFun := frameMap q
  invFun := frameMap (fun ξ => -q ξ)
  left_inv f := congrArg (fun T : Operator (ι := ι) => T f) (frameMap_inverse q).2
  right_inv f := congrArg (fun T : Operator (ι := ι) => T f) (frameMap_inverse q).1
  map_add' := (frameMap q).map_add
  map_smul' := (frameMap q).map_smul

/-- A spectral residual identity suffices to compile the corresponding frame edge. -/
theorem frame_ratio_signedWord [Fintype κ] (qU qV : Vec ι → ZMod 4)
    (z : κ → Vec ι) (decreasing : Bool)
    (hunit : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0)
    (hresidual : ∀ ξ, qV ξ - qU ξ =
      edgeSign decreasing * weightModFour (frameProjection z ξ)) :
    (frameMap qV).comp (frameMap (fun ξ => -qU ξ)) =
      signedWord z decreasing Finset.univ.toList := by
  rw [frameMap_comp, signedWord_frame z decreasing hunit horth]
  congr 1
  funext ξ
  simpa only [sub_eq_add_neg] using hresidual ξ

theorem weightModFour_unit (p : ι) : weightModFour (unit p) = 1 := by
  simp only [weightModFour, weight, unit, apply_ite, bit_one, bit_zero]
  simp

theorem signedMap_unit (p : ι) : signedMap (unit p) false = directionalMap (unit p) := by
  simp [signedMap, weightModFour_unit]

theorem unit_frameProjection (ξ : Vec ι) : frameProjection (unit : ι → Vec ι) ξ = ξ := by
  simp only [frameProjection, dot_unit_left]
  exact unit_decomposition ξ

/-- The ordinary frame is the product of the coordinate C layers. -/
theorem coordinate_word_standard :
    signedWord (unit : ι → Vec ι) false Finset.univ.toList = frameMap weightModFour := by
  have hunit : ∀ i : ι, dot (unit i) (unit i) = 1 := by
    intro i
    rw [dot_units]
    simp
  have horth : ∀ i j : ι, i ≠ j → dot (unit i) (unit j) = 0 := by
    intro i j hij
    rw [dot_units]
    simp [hij]
  have h := signedWord_frame (unit : ι → Vec ι) false hunit horth
  simpa only [edgeSign, Bool.false_eq_true, ↓reduceIte, one_mul, unit_frameProjection] using h

def lineExponent (u : Vec ι) (ξ : Vec ι) : ZMod 4 := weightModFour (dot u ξ • u)
def perpExponent (u : Vec ι) (ξ : Vec ι) : ZMod 4 := weightModFour (ξ + dot u ξ • u)

omit [DecidableEq ι] in
/-- The exceptional line-to-complement route adds precisely one translation character. -/
theorem terminal_weight_ratio (u ξ : Vec ι) (hu : dot u u = 1) :
    perpExponent u ξ - lineExponent u ξ =
      weightModFour ξ + 2 * (bit (dot u ξ) : ZMod 4) := by
  let p : Vec ι := dot u ξ • u
  let r : Vec ι := ξ + p
  have hur : dot u r = 0 := by
    dsimp [r, p]
    rw [dot_add_right, dot_smul_right, hu, mul_one]
    exact CharTwo.add_self_eq_zero (dot u ξ)
  have hrp : dot r p = 0 := by
    dsimp [p]
    rw [dot_smul_right, dot_comm r u, hur, mul_zero]
  have hradd : r + p = ξ := by
    dsimp [r]
    rw [add_assoc, vec_add_self, add_zero]
  have hadd : weightModFour r + weightModFour p = weightModFour ξ := by
    rw [← weightModFour_add_of_dot_zero r p hrp, hradd]
  have htwo : (2 : ZMod 4) * weightModFour p = 2 * (bit (dot u ξ) : ZMod 4) := by
    change (2 : ZMod 4) * weightModFour (dot u ξ • u) = _
    rw [weightModFour_smul]
    rcases norm_one_weightModFour u hu with h | h
    · rw [h]; ring
    · rw [h]
      calc
        _ = (-2 : ZMod 4) * (bit (dot u ξ) : ZMod 4) := by ring
        _ = _ := by rw [show (-2 : ZMod 4) = 2 by decide]
  have hneg : -(2 * weightModFour p) = 2 * (bit (dot u ξ) : ZMod 4) := by
    rw [htwo, ← neg_mul, show (-2 : ZMod 4) = 2 by decide]
  change weightModFour r - weightModFour p = _
  calc
    _ = (weightModFour r + weightModFour p) + -(2 * weightModFour p) := by ring
    _ = _ := by rw [hadd, hneg]

/-- Whole-array terminal identity for every norm-one u, not only the weight-27 instance. -/
theorem terminal_frame_ratio (u : Vec ι) (hu : dot u u = 1) :
    (frameMap (perpExponent u)).comp (frameMap (fun ξ => -lineExponent u ξ)) =
      (translateMap u).comp (frameMap weightModFour) := by
  apply operator_eq_of_characters
  intro ξ
  simp only [LinearMap.comp_apply, frameMap_character, map_smul,
    translate_character, smul_smul]
  congr 1
  calc
    _ = phase (perpExponent u ξ - lineExponent u ξ) := by
      rw [← phase_add, add_comm, sub_eq_add_neg]
    _ = _ := by rw [terminal_weight_ratio u ξ hu, phase_add, ← binarySign_phase]

end
end ExactFourierCircuits.FrameSpectrum
