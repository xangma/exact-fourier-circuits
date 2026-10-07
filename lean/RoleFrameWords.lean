import FrameWords
import BinaryProjection

/- Literal signed frame words embedded into one physical role. -/
namespace ExactFourierCircuits.RoleFrameWords
open OAI.ExactFourier BinaryFrames BinaryTensor FrameSpectrum BinaryProjection Module
open scoped BigOperators
noncomputable section
variable {r n : ℕ}

def roleEmbedding (role : Fin r) : Fin (2 ^ n) ↪ Fin (r * 2 ^ n) where
  toFun a := RoleWords.roleAddresses r n (role, a)
  inj' := by
    intro a b h
    exact congrArg Prod.snd ((RoleWords.roleAddresses r n).injective h)

@[simp] theorem roleEmbedding_apply (role : Fin r) (a : Fin (2 ^ n)) :
    roleEmbedding (n := n) role a = RoleWords.roleAddresses r n (role, a) := rfl

theorem roleEmbedding_not_mem (role i : Fin r) (hi : i ≠ role) (a : Fin (2 ^ n)) :
    RoleWords.roleAddresses r n (i, a) ∉ Set.range (roleEmbedding (n := n) role) := by
  rintro ⟨b, hb⟩
  exact hi (congrArg Prod.fst ((RoleWords.roleAddresses r n).injective hb)).symm

theorem roleMatrix_selected_entry (role j : Fin r)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (a b : Fin (2 ^ n)) :
    Embedded.matrix (roleEmbedding role) M (RoleWords.roleAddresses r n (role, a))
      (RoleWords.roleAddresses r n (j, b)) = if j = role then M a b else 0 := by
  by_cases hj : j = role
  · subst j
    simpa only [roleEmbedding_apply, ↓reduceIte] using
      Embedded.matrix_on (roleEmbedding (n := n) role) M a b
  · have hne : RoleWords.roleAddresses r n (role, a) ≠
        RoleWords.roleAddresses r n (j, b) := by
      intro h
      exact hj (congrArg Prod.fst ((RoleWords.roleAddresses r n).injective h)).symm
    rw [Embedded.matrix_off_col _ _ _ _ (roleEmbedding_not_mem role j hj b)]
    simp [hj, hne]

theorem roleMatrix_selected_apply (role : Fin r)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (a : Fin (2 ^ n)) :
    (Embedded.matrix (roleEmbedding role) M).mulVec (RoleWords.arrayValues n X)
      (RoleWords.roleAddresses r n (role, a)) = M.mulVec (X role) a := by
  unfold Matrix.mulVec dotProduct
  rw [← (RoleWords.roleAddresses r n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [roleMatrix_selected_entry, RoleWords.arrayValues_at]
  simp

theorem roleMatrix_untouched_apply (role i : Fin r) (hi : i ≠ role)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (a : Fin (2 ^ n)) :
    (Embedded.matrix (roleEmbedding role) M).mulVec (RoleWords.arrayValues n X)
      (RoleWords.roleAddresses r n (i, a)) = X i a := by
  unfold Matrix.mulVec dotProduct
  simp_rw [Embedded.matrix_off_row _ _ _ _ (roleEmbedding_not_mem role i hi a)]
  simp

def roleWord (role : Fin r) (W : List (WordStep C (2 ^ n))) :
    List (WordStep C (r * 2 ^ n)) := TensorWords.embeddedWord (roleEmbedding role) W

theorem roleWord_matrix (role : Fin r) (W : List (WordStep C (2 ^ n))) :
    wordMatrix (roleWord role W) = Embedded.matrix (roleEmbedding role) (wordMatrix W) :=
  TensorWords.embeddedWord_matrix _ _

theorem roleWord_calls (role : Fin r) (W : List (WordStep C (2 ^ n))) :
    wordCalls (roleWord role W) = wordCalls W := TensorWords.embeddedWord_calls _ _

/-- Arbitrary values in every role, with role outermost and binary address innermost. -/
def binaryValues (X : Fin r → Array (ι := Fin n)) : Fin (r * 2 ^ n) → ℂ :=
  RoleWords.arrayValues n (fun i a => X i ((DirectionalWords.addresses n).symm a))

@[simp] theorem binaryValues_at (X : Fin r → Array (ι := Fin n))
    (i : Fin r) (x : Vec (Fin n)) :
    binaryValues X (RoleWords.roleAddresses r n (i, DirectionalWords.addresses n x)) = X i x := by
  simp [binaryValues]

theorem binaryValues_surjective : Function.Surjective (binaryValues (r := r) (n := n)) := by
  intro f
  refine ⟨fun i x => f (RoleWords.roleAddresses r n (i, DirectionalWords.addresses n x)), ?_⟩
  funext k
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses r n).surjective k
  obtain ⟨x, rfl⟩ := (DirectionalWords.addresses n).surjective a
  exact binaryValues_at _ i x

theorem binaryAction_apply (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Array (ι := Fin n)) (x : Vec (Fin n)) :
    FrameWords.binaryAction M f x =
      M.mulVec (fun a => f ((DirectionalWords.addresses n).symm a))
        (DirectionalWords.addresses n x) := by
  change (Matrix.reindex (DirectionalWords.addresses n).symm
    (DirectionalWords.addresses n).symm M).mulVec f x = _
  rw [reindex_mulVec]
  rfl

theorem roleWord_selected_apply (role : Fin r) (W : List (WordStep C (2 ^ n)))
    (X : Fin r → Array (ι := Fin n)) (x : Vec (Fin n)) :
    (wordMatrix (roleWord role W)).mulVec (binaryValues X)
      (RoleWords.roleAddresses r n (role, DirectionalWords.addresses n x)) =
      FrameWords.binaryAction (wordMatrix W) (X role) x := by
  rw [roleWord_matrix, binaryValues, roleMatrix_selected_apply, binaryAction_apply]

theorem roleWord_untouched_apply (role i : Fin r) (hi : i ≠ role)
    (W : List (WordStep C (2 ^ n))) (X : Fin r → Array (ι := Fin n)) (x : Vec (Fin n)) :
    (wordMatrix (roleWord role W)).mulVec (binaryValues X)
      (RoleWords.roleAddresses r n (i, DirectionalWords.addresses n x)) = X i x := by
  rw [roleWord_matrix, binaryValues, roleMatrix_untouched_apply role i hi]
  simp

theorem roleWord_array (role : Fin r) (W : List (WordStep C (2 ^ n)))
    (X : Fin r → Array (ι := Fin n)) :
    (wordMatrix (roleWord role W)).mulVec (binaryValues X) =
      binaryValues (Function.update X role (FrameWords.binaryAction (wordMatrix W) (X role))) := by
  funext k
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses r n).surjective k
  obtain ⟨x, rfl⟩ := (DirectionalWords.addresses n).surjective a
  rw [binaryValues_at]
  by_cases hi : i = role
  · subst i
    simp only [Function.update_apply, ↓reduceIte]
    exact roleWord_selected_apply role W X x
  · rw [Function.update_of_ne hi, roleWord_untouched_apply role i hi]

variable {κ : Type*} [Fintype κ]

def roleFrameList (role : Fin r) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1) (decreasing : Bool) :
    List (WordStep C (r * 2 ^ n)) :=
  roleWord role (FrameWords.signedFrameList z hz decreasing Finset.univ.toList)

theorem roleFrameList_calls (hn : 1 ≤ n) (role : Fin r) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1) (decreasing : Bool) :
    wordCalls (roleFrameList role z hz decreasing) = Fintype.card κ * 2 ^ (n - 1) := by
  rw [roleFrameList, roleWord_calls, FrameWords.signedFrameList_calls hn]
  simp

theorem roleFrameList_array (role : Fin r) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) (decreasing : Bool)
    (X : Fin r → Array (ι := Fin n)) :
    (wordMatrix (roleFrameList role z hz decreasing)).mulVec (binaryValues X) =
      binaryValues (Function.update X role
        (frameMap (fun ξ => edgeSign decreasing * weightModFour (frameProjection z ξ)) (X role))) := by
  rw [roleFrameList, roleWord_array, FrameWords.signedFrameList_action,
    signedWord_frame z decreasing hz horth]

theorem roleFrameList_selected_apply (role : Fin r) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) (decreasing : Bool)
    (X : Fin r → Array (ι := Fin n)) (x : Vec (Fin n)) :
    (wordMatrix (roleFrameList role z hz decreasing)).mulVec (binaryValues X)
      (RoleWords.roleAddresses r n (role, DirectionalWords.addresses n x)) =
      frameMap (fun ξ => edgeSign decreasing * weightModFour (frameProjection z ξ)) (X role) x := by
  rw [roleFrameList, roleWord_selected_apply, FrameWords.signedFrameList_action,
    signedWord_frame z decreasing hz horth]

theorem roleFrameList_untouched_apply (role i : Fin r) (hi : i ≠ role)
    (z : κ → Vec (Fin n)) (hz : ∀ j, dot (z j) (z j) = 1) (decreasing : Bool)
    (X : Fin r → Array (ι := Fin n)) (x : Vec (Fin n)) :
    (wordMatrix (roleFrameList role z hz decreasing)).mulVec (binaryValues X)
      (RoleWords.roleAddresses r n (i, DirectionalWords.addresses n x)) = X i x :=
  roleWord_untouched_apply role i hi _ X x

theorem compile_signed_role_frame (hn : 1 ≤ n) (role : Fin r) (z : κ → Vec (Fin n))
    (hz : ∀ i, dot (z i) (z i) = 1)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) (decreasing : Bool) :
    ∃ W : List (WordStep C (r * 2 ^ n)),
      (∀ X : Fin r → Array (ι := Fin n),
        (wordMatrix W).mulVec (binaryValues X) =
          binaryValues (Function.update X role
            (frameMap (fun ξ => edgeSign decreasing * weightModFour (frameProjection z ξ)) (X role)))) ∧
      wordCalls W = Fintype.card κ * 2 ^ (n - 1) :=
  ⟨roleFrameList role z hz decreasing,
    roleFrameList_array role z hz horth decreasing,
    roleFrameList_calls hn role z hz decreasing⟩

section NestedBases
variable {α ν : Type*} [DecidableEq κ] [Fintype α] [DecidableEq α]
  [Fintype ν] [DecidableEq ν]

/-- Increasing is larger times inverse smaller; decreasing reverses this ratio. -/
def nestedRatio (a : κ → Vec (Fin n)) (v : ν → Vec (Fin n)) (decreasing : Bool) :
    Operator (ι := Fin n) :=
  if decreasing then
    (frameMap (frameExponent a)).comp (frameMap (fun x => -frameExponent v x))
  else (frameMap (frameExponent v)).comp (frameMap (fun x => -frameExponent a x))

theorem nestedRatio_signedWord (A S : Submodule F2 (Vec (Fin n))) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (BinaryResiduals.residual A S)) (v : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec (Fin n))))
    (he : Orthonormal (fun i => (e i : Vec (Fin n))))
    (hv : Orthonormal (fun i => (v i : Vec (Fin n)))) (decreasing : Bool) :
    nestedRatio (fun i => (a i : Vec (Fin n))) (fun i => (v i : Vec (Fin n))) decreasing =
      signedWord (fun i => (e i : Vec (Fin n))) decreasing Finset.univ.toList := by
  cases decreasing with
  | false => exact nested_basis_ratio_increasing A S hAS a e v ha he hv
  | true => exact nested_basis_ratio_decreasing A S hAS a e v ha he hv

/-- This concrete list realizes the edge using the actual geometric residual.
    No projection equality or phase-difference identity is assumed. -/
theorem roleFrameList_nested_array (role : Fin r)
    (A S : Submodule F2 (Vec (Fin n))) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (BinaryResiduals.residual A S)) (v : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec (Fin n))))
    (he : Orthonormal (fun i => (e i : Vec (Fin n))))
    (hv : Orthonormal (fun i => (v i : Vec (Fin n)))) (decreasing : Bool)
    (X : Fin r → Array (ι := Fin n)) :
    (wordMatrix (roleFrameList role (fun i => (e i : Vec (Fin n)))
      (frame_unit _ he) decreasing)).mulVec (binaryValues X) =
      binaryValues (Function.update X role
        (nestedRatio (fun i => (a i : Vec (Fin n))) (fun i => (v i : Vec (Fin n))) decreasing
          (X role))) := by
  rw [roleFrameList, roleWord_array, FrameWords.signedFrameList_action,
    ← nestedRatio_signedWord A S hAS a e v ha he hv decreasing]

theorem compile_nested_role_edge (hn : 1 ≤ n) (role : Fin r)
    (A S : Submodule F2 (Vec (Fin n))) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (BinaryResiduals.residual A S)) (v : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec (Fin n))))
    (he : Orthonormal (fun i => (e i : Vec (Fin n))))
    (hv : Orthonormal (fun i => (v i : Vec (Fin n)))) (decreasing : Bool) :
    ∃ W : List (WordStep C (r * 2 ^ n)),
      (∀ X : Fin r → Array (ι := Fin n),
        (wordMatrix W).mulVec (binaryValues X) =
          binaryValues (Function.update X role
            (nestedRatio (fun i => (a i : Vec (Fin n))) (fun i => (v i : Vec (Fin n))) decreasing
              (X role)))) ∧
      wordCalls W = Fintype.card α * 2 ^ (n - 1) :=
  ⟨roleFrameList role (fun i => (e i : Vec (Fin n))) (frame_unit _ he) decreasing,
    roleFrameList_nested_array role A S hAS a e v ha he hv decreasing,
    roleFrameList_calls hn role _ (frame_unit _ he) decreasing⟩

end NestedBases

end
end ExactFourierCircuits.RoleFrameWords
