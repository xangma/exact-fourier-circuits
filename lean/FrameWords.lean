import FrameSpectrum
import RoleWords

/- Literal WordStep realization of the signed Walsh frame operators. -/
namespace ExactFourierCircuits.FrameWords
open OAI.ExactFourier BinaryFrames BinaryTensor FrameSpectrum
open scoped BigOperators
noncomputable section
variable {n : ℕ}

def binaryAction (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Operator (ι := Fin n) :=
  Matrix.mulVecLin (Matrix.reindex (DirectionalWords.addresses n).symm
    (DirectionalWords.addresses n).symm M)

theorem binaryAction_one : binaryAction (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) =
    LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp [binaryAction]

theorem binaryAction_mul (M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    binaryAction (M * N) = (binaryAction M).comp (binaryAction N) := by
  apply LinearMap.ext
  intro f
  change ((Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm) (M * N)).mulVec f =
    ((Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm) M).mulVec
      (((Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm) N).mulVec f)
  rw [map_mul]
  exact (Matrix.mulVec_mulVec f
    ((Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm) M)
    ((Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm) N)).symm

lemma translation_entry (z x y : DirectionalWords.Bits n) :
    DirectionalWords.translation z x y = if y = x + z then 1 else 0 := by
  have he : x = y + z ↔ y = x + z := by
    constructor <;> intro h
    · rw [h, add_assoc, DirectionalWords.bits_add_self, add_zero]
    · rw [h, add_assoc, DirectionalWords.bits_add_self, add_zero]
  simp [DirectionalWords.translation, permM, DirectionalWords.translationEquiv, he]

theorem binaryAction_translation (z : DirectionalWords.Bits n) :
    binaryAction (DirectionalWords.translationFin z) = translateMap z := by
  apply LinearMap.ext
  intro f
  ext x
  simp [binaryAction, DirectionalWords.translationFin, Matrix.reindex_apply,
    Matrix.mulVec, dotProduct, translation_entry, translateMap, Projection.translate]

theorem binaryAction_directional (z : DirectionalWords.Bits n) :
    binaryAction (DirectionalWords.directionalC z) = directionalMap z := by
  apply LinearMap.ext
  intro f
  ext x
  simp [binaryAction, DirectionalWords.directionalC, DirectionalWords.directionalMatrix,
    Matrix.reindex_apply, Matrix.mulVec, dotProduct, translation_entry,
    directionalMap, Projection.directionalC]

theorem binaryAction_inverse (z : DirectionalWords.Bits n) (hz : z ≠ 0) :
    binaryAction (DirectionalWords.directionalC z)⁻¹ = inverseDirectionalMap z := by
  obtain ⟨p, hp⟩ := DirectionalWords.exists_pivot z hz
  rw [DirectionalWords.directionalC_inverse z p hp, binaryAction_mul,
    binaryAction_translation, binaryAction_directional]
  exact (inverse_directional_translation z).symm

lemma norm_one_nonzero (z : Vec (Fin n)) (hz : dot z z = 1) : z ≠ 0 := by
  intro h
  simp [h, dot] at hz

def signedLayer (z : Vec (Fin n)) (hz : dot z z = 1) (decreasing : Bool) :
    List (WordStep C (2 ^ n)) :=
  if weightModFour z = 1 then
    if decreasing then DirectionalWords.inverseDirectionalWord z (norm_one_nonzero z hz)
    else DirectionalWords.directionalWord z (norm_one_nonzero z hz)
  else if decreasing then DirectionalWords.directionalWord z (norm_one_nonzero z hz)
    else DirectionalWords.inverseDirectionalWord z (norm_one_nonzero z hz)

theorem signedLayer_action (z : Vec (Fin n)) (hz : dot z z = 1) (decreasing : Bool) :
    binaryAction (wordMatrix (signedLayer z hz decreasing)) = signedMap z decreasing := by
  have hf : binaryAction (wordMatrix (DirectionalWords.directionalWord z (norm_one_nonzero z hz))) =
      directionalMap z := by
    rw [DirectionalWords.directionalWord, DirectionalWords.directionalWordAt_matrix,
      binaryAction_directional]
  have hi : binaryAction (wordMatrix (DirectionalWords.inverseDirectionalWord z (norm_one_nonzero z hz))) =
      inverseDirectionalMap z := by
    rw [DirectionalWords.inverseDirectionalWord, DirectionalWords.inverseDirectionalWordAt_matrix,
      binaryAction_inverse z (norm_one_nonzero z hz)]
  unfold signedLayer signedMap
  split <;> cases decreasing <;> simp [hf, hi]

theorem signedLayer_calls (hn : 1 ≤ n) (z : Vec (Fin n)) (hz : dot z z = 1)
    (decreasing : Bool) : wordCalls (signedLayer z hz decreasing) = 2 ^ (n - 1) := by
  have hf := DirectionalWords.directionalWordAt_calls hn z
  have hi := DirectionalWords.inverseDirectionalWordAt_calls hn z
  unfold signedLayer DirectionalWords.directionalWord DirectionalWords.inverseDirectionalWord
  split <;> cases decreasing <;> simp [hf, hi]

variable {κ : Type*}

def signedFrameList (z : κ → Vec (Fin n)) (hz : ∀ i, dot (z i) (z i) = 1)
    (decreasing : Bool) (is : List κ) : List (WordStep C (2 ^ n)) :=
  (is.map (fun i => signedLayer (z i) (hz i) decreasing)).flatten

theorem signedFrameList_action (z : κ → Vec (Fin n)) (hz : ∀ i, dot (z i) (z i) = 1)
    (decreasing : Bool) (is : List κ) :
    binaryAction (wordMatrix (signedFrameList z hz decreasing is)) =
      FrameSpectrum.signedWord z decreasing is := by
  induction is with
  | nil => simpa [signedFrameList, wordMatrix, signedWord] using (binaryAction_one (n := n))
  | cons i is ih =>
    simp only [signedFrameList, List.map_cons, List.flatten_cons,
      TypedKernelWords.wordMatrix_append, binaryAction_mul]
    rw [← signedFrameList, ih, signedLayer_action]
    rfl

theorem signedFrameList_calls (hn : 1 ≤ n) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1) (decreasing : Bool) (is : List κ) :
    wordCalls (signedFrameList z hz decreasing is) = is.length * 2 ^ (n - 1) := by
  induction is with
  | nil => simp [signedFrameList, wordCalls]
  | cons i is ih =>
    simp only [signedFrameList, List.map_cons, List.flatten_cons,
      TypedKernelWords.wordCalls_append, signedLayer_calls hn]
    rw [← signedFrameList, ih, List.length_cons]
    ring

/-- This is an actual finite WordStep list realizing the whole-array signed
    frame, with exactly one forward pair layer per orthonormal basis vector. -/
theorem compile_signed_frame [Fintype κ] (hn : 1 ≤ n) (z : κ → Vec (Fin n))
    (hunit : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) (decreasing : Bool) :
    ∃ W : List (WordStep C (2 ^ n)),
      binaryAction (wordMatrix W) =
        frameMap (fun ξ => edgeSign decreasing * weightModFour (frameProjection z ξ)) ∧
      wordCalls W = Fintype.card κ * 2 ^ (n - 1) := by
  classical
  refine ⟨signedFrameList z hunit decreasing Finset.univ.toList, ?_, ?_⟩
  · rw [signedFrameList_action, signedWord_frame z decreasing hunit horth]
  · rw [signedFrameList_calls hn]
    simp

end
end ExactFourierCircuits.FrameWords
