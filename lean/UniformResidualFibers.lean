import UniformFixedNetwork

/- Fixed-pivot fiber coordinates and grouped residual operators.  The grouped
   tensor action is algebraic; address preparation and RAM lowering are separate. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualFibers
open OAI.ExactFourier DirectionalWords BinaryFrames BinaryTensor
open scoped BigOperators Kronecker
noncomputable section
variable {n : ℕ}

abbrev Fibers (q : ℕ) (p : Fin n) := Fin q → Representatives p

/-- Flattening is precisely the existing row-major factor-coordinate transport. -/
def flattenColumns (q n : ℕ) : (Fin q → Bits n) ≃ Bits (q * n) where
  toFun x := StageFrames.coordinates finProdFinEquiv (fun ci => x ci.1 ci.2)
  invFun x c i := x (finProdFinEquiv (c, i))
  left_inv x := by funext c i; simp
  right_inv x := by
    funext j
    obtain ⟨⟨c,i⟩,rfl⟩ := (finProdFinEquiv : Fin q × Fin n ≃ Fin (q*n)).surjective j
    simp

/-- No binary basis is selected: each column retains its fixed representative and pivot bit. -/
def columnPairs (q : ℕ) (p : Fin n) :
    (Fibers q p × Bits q) ≃ (Fin q → Σ _ : Representatives p, Fin 2) where
  toFun u c := ⟨u.1 c, TensorWords.bitEquiv.symm (u.2 c)⟩
  invFun x := (fun c => (x c).1, fun c => TensorWords.bitEquiv (x c).2)
  left_inv u := by cases u; simp
  right_inv x := by funext c; simp

def fiberEquiv (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    (Fibers q p × Bits q) ≃ Bits (q * n) :=
  (columnPairs q p).trans
    ((Equiv.piCongrRight (fun _ : Fin q => pairEquiv v p hp)).trans (flattenColumns q n))

lemma fiberEquiv_apply (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u : Fibers q p) (t : Bits q) (c : Fin q) (i : Fin n) :
    fiberEquiv q v p hp (u,t) (finProdFinEquiv (c,i)) =
      pairPoint v p ⟨u c, TensorWords.bitEquiv.symm (t c)⟩ i := by
  simp [fiberEquiv, columnPairs, flattenColumns]

/-- A prescribed combination of the copied column directions. -/
def copyCombination (q : ℕ) (v : Bits n) (t : Bits q) : Bits (q * n) :=
  StageFrames.coordinates finProdFinEquiv (tensor t v)

def copyVector (q : ℕ) (v : Bits n) (c : Fin q) : Bits (q * n) :=
  copyCombination q v (unit c)

lemma copyCombination_apply (q : ℕ) (v : Bits n) (t : Bits q) (c : Fin q) (i : Fin n) :
    copyCombination q v t (finProdFinEquiv (c,i)) = t c * v i := by
  simp [copyCombination, tensor]

@[simp] lemma bitEquiv_symm_zero : TensorWords.bitEquiv.symm (0 : ZMod 2) = (0 : Fin 2) := rfl
@[simp] lemma bitEquiv_symm_one : TensorWords.bitEquiv.symm (1 : ZMod 2) = (1 : Fin 2) := rfl

lemma pairPoint_add_bit (v : Bits n) (p : Fin n) (u : Representatives p) (s t : ZMod 2) :
    pairPoint v p ⟨u, TensorWords.bitEquiv.symm (s + t)⟩ =
      pairPoint v p ⟨u, TensorWords.bitEquiv.symm s⟩ + t • v := by
  rcases binary_values s with rfl | rfl <;> rcases binary_values t with rfl | rfl <;>
    simp [pairPoint, CharTwo.add_self_eq_zero, add_assoc]

/-- Every pivot-bit update stays inside the same explicitly encoded fiber. -/
lemma fiberEquiv_add (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u : Fibers q p) (s t : Bits q) :
    fiberEquiv q v p hp (u,s+t) = fiberEquiv q v p hp (u,s) + copyCombination q v t := by
  funext j
  obtain ⟨⟨c,i⟩,rfl⟩ := (finProdFinEquiv : Fin q × Fin n ≃ Fin (q*n)).surjective j
  simp only [fiberEquiv_apply, Pi.add_apply, copyCombination_apply]
  exact congrFun (pairPoint_add_bit v p (u c) (s c) (t c)) i

lemma fibers_card (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    Fintype.card (Fibers q p) = 2 ^ (q * (n - 1)) := by
  have hn : 1 ≤ n := by have := p.isLt; omega
  rw [Fintype.card_fun, Fintype.card_fin, representatives_card hn v p hp, ← pow_mul]
  rw [Nat.mul_comm]

lemma fiber_width (q : ℕ) : Fintype.card (Bits q) = 2 ^ q := by simp [Bits, ZMod.card]

lemma fiber_partition_card (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    2 ^ (q * (n - 1)) * 2 ^ q = 2 ^ (q * n) := by
  have h := Fintype.card_congr (fiberEquiv q v p hp)
  simpa only [Fintype.card_prod, fibers_card q v p hp, fiber_width] using h

/-- Fixed fiber labels with an arbitrary operator on the selected bits. -/
def fiberHom (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    Matrix (Bits q) (Bits q) ℂ →* Matrix (Bits (q*n)) (Bits (q*n)) ℂ where
  toFun M := Matrix.reindex (fiberEquiv q v p hp) (fiberEquiv q v p hp)
    ((1 : Matrix (Fibers q p) (Fibers q p) ℂ) ⊗ₖ M)
  map_one' := by
    ext x y
    obtain ⟨⟨u,s⟩,rfl⟩ := (fiberEquiv q v p hp).surjective x
    obtain ⟨⟨w,t⟩,rfl⟩ := (fiberEquiv q v p hp).surjective y
    simp [Matrix.reindex_apply, Matrix.one_apply, (fiberEquiv q v p hp).injective.eq_iff,
      ite_and]
  map_mul' M N := by
    rw [← PaddingWords.reindex_mul, ← Matrix.mul_kronecker_mul]
    simp

lemma fiber_translation (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (t : Bits q) :
    fiberHom q v p hp (translation t) = translation (copyCombination q v t) := by
  ext x y
  obtain ⟨⟨u,s⟩,rfl⟩ := (fiberEquiv q v p hp).surjective x
  obtain ⟨⟨w,r⟩,rfl⟩ := (fiberEquiv q v p hp).surjective y
  have ht : fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) + copyCombination q v t ↔
      u = w ∧ s = r+t := by
    rw [← fiberEquiv_add]
    rw [(fiberEquiv q v p hp).injective.eq_iff]
    simp only [Prod.mk.injEq]
  change Matrix.reindex (fiberEquiv q v p hp) (fiberEquiv q v p hp)
    ((1 : Matrix (Fibers q p) (Fibers q p) ℂ) ⊗ₖ translation t)
    (fiberEquiv q v p hp (u,s)) (fiberEquiv q v p hp (w,r)) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  change (if u=w then (1 : ℂ) else 0) * (if s=r+t then 1 else 0) =
    if fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) + copyCombination q v t then 1 else 0
  simp only [ht]
  by_cases h : u=w <;> simp [h]

lemma fiber_directional (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (t : Bits q) :
    fiberHom q v p hp (directionalMatrix t) = directionalMatrix (copyCombination q v t) := by
  ext x y
  obtain ⟨⟨u,s⟩,rfl⟩ := (fiberEquiv q v p hp).surjective x
  obtain ⟨⟨w,r⟩,rfl⟩ := (fiberEquiv q v p hp).surjective y
  have he : fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) ↔ u=w ∧ s=r := by
    rw [(fiberEquiv q v p hp).injective.eq_iff]
    simp only [Prod.mk.injEq]
  have ht : fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) + copyCombination q v t ↔
      u=w ∧ s=r+t := by
    rw [← fiberEquiv_add]
    rw [(fiberEquiv q v p hp).injective.eq_iff]
    simp only [Prod.mk.injEq]
  change Matrix.reindex (fiberEquiv q v p hp) (fiberEquiv q v p hp)
    ((1 : Matrix (Fibers q p) (Fibers q p) ℂ) ⊗ₖ directionalMatrix t)
    (fiberEquiv q v p hp (u,s)) (fiberEquiv q v p hp (w,r)) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  change (if u=w then (1 : ℂ) else 0) *
      (a * (if s=r then 1 else 0) + b * (if s=r+t then 1 else 0)) =
    a * (if fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) then 1 else 0) +
    b * (if fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,r) + copyCombination q v t then 1 else 0)
  simp only [he, ht]
  by_cases h : u=w <;> simp [h]

lemma unit_axes_product_list (q : ℕ) (L : List (Fin q)) (hL : L.Nodup)
    (hfull : ∀ c, c ∈ L) :
    (L.map (fun c => directionalMatrix (TensorWords.unitDirection c))).prod =
      PiTensor.matrix (fun _ : Fin q => TensorWords.binaryC) := by
  simp_rw [← TensorWords.unit_axis_matrix]
  let upd := fun c : Fin q => Function.update (1 : Fin q → Matrix (ZMod 2) (ZMod 2) ℂ) c TensorWords.binaryC
  change (L.map (fun c => PiTensor.hom (upd c))).prod = _
  rw [show L.map (fun c => PiTensor.hom (upd c)) = (L.map upd).map PiTensor.hom from (List.map_map ..).symm]
  rw [← map_list_prod]
  change PiTensor.matrix ((L.map upd).prod) = PiTensor.matrix (fun _ : Fin q => TensorWords.binaryC)
  congr 1
  funext c
  rw [Embedded.list_update_prod _ _ hL]
  simp [hfull c]

/-- The actual chronological product, whose matrix multiplication reverses its column list. -/
def copiedProduct (q : ℕ) (v : Bits n) : Matrix (Bits (q*n)) (Bits (q*n)) ℂ :=
  (Finset.univ.toList.map (fun c => directionalMatrix (copyVector q v c))).reverse.prod

lemma copiedProduct_fibers (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    copiedProduct q v = fiberHom q v p hp (PiTensor.matrix (fun _ : Fin q => TensorWords.binaryC)) := by
  unfold copiedProduct
  rw [← List.map_reverse]
  simp_rw [copyVector, ← fiber_directional q v p hp]
  rw [show Finset.univ.toList.reverse.map
      (fun c => fiberHom q v p hp (directionalMatrix (unit c))) =
      (Finset.univ.toList.reverse.map (fun c => directionalMatrix (unit c))).map (fiberHom q v p hp)
    from (List.map_map ..).symm]
  rw [← map_list_prod, unit_axes_product_list q _
    (by simpa only [List.nodup_reverse] using Finset.nodup_toList (Finset.univ : Finset (Fin q))) (by intro c; simp)]


/-- The selected bits use exactly the upstream tensor-power coordinate equivalence. -/
def selectedBits (q : ℕ) : Fin (2 ^ q) ≃ Bits q :=
  (tensorCoordinates 2 q).trans (TensorWords.tensorBits q)

lemma selectedBits_tensor (q : ℕ) :
    Matrix.reindex (selectedBits q) (selectedBits q) (tensorPower C q) =
      PiTensor.matrix (fun _ : Fin q => TensorWords.binaryC) := by
  ext s t
  simp [selectedBits, TensorWords.tensorBits, TensorWords.binaryC, tensorPower,
    PiTensor.matrix, Matrix.reindex_apply]

def fiberCoordinates (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    (Σ _ : Fibers q p, Fin (2 ^ q)) ≃ Bits (q*n) :=
  (Equiv.sigmaEquivProd _ _).trans
    (((Equiv.refl (Fibers q p)).prodCongr (selectedBits q)).trans (fiberEquiv q v p hp))

@[simp] lemma fiberCoordinates_symm_fiber (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u : Fibers q p) (s : Bits q) :
    (fiberCoordinates q v p hp).symm (fiberEquiv q v p hp (u,s)) =
      ⟨u, (selectedBits q).symm s⟩ := by simp [fiberCoordinates]

/-- A complete direct sum of q-bit transforms, not a partially filled batch. -/
theorem copiedProduct_blocks (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    copiedProduct q v = Matrix.reindex (fiberCoordinates q v p hp) (fiberCoordinates q v p hp)
      (Matrix.blockDiagonal' (fun _ : Fibers q p => tensorPower C q)) := by
  rw [copiedProduct_fibers q v p hp]
  ext x y
  obtain ⟨⟨u,s⟩,rfl⟩ := (fiberEquiv q v p hp).surjective x
  obtain ⟨⟨w,t⟩,rfl⟩ := (fiberEquiv q v p hp).surjective y
  have hM := congrFun (congrFun (selectedBits_tensor q) s) t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hM
  change Matrix.reindex (fiberEquiv q v p hp) (fiberEquiv q v p hp)
    ((1 : Matrix (Fibers q p) (Fibers q p) ℂ) ⊗ₖ
      PiTensor.matrix (fun _ : Fin q => TensorWords.binaryC))
    (fiberEquiv q v p hp (u,s)) (fiberEquiv q v p hp (w,t)) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    fiberCoordinates_symm_fiber]
  by_cases h : u=w
  · subst w
    simpa [Matrix.one_apply, Matrix.blockDiagonal'_apply] using hM.symm
  · simp [Matrix.blockDiagonal'_apply, h]

/-- Arbitrary scalar arrays are independently transformed on every actual fiber. -/
theorem copiedProduct_array (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (X : Bits (q*n) → ℂ) (u : Fibers q p) (a : Fin (2 ^ q)) :
    (copiedProduct q v).mulVec X (fiberCoordinates q v p hp ⟨u,a⟩) =
      (tensorPower C q).mulVec (fun b => X (fiberCoordinates q v p hp ⟨u,b⟩)) a := by
  rw [copiedProduct_blocks q v p hp]
  unfold Matrix.mulVec dotProduct
  rw [← (fiberCoordinates q v p hp).sum_comp, Fintype.sum_sigma]
  simp [Matrix.reindex_apply, Matrix.blockDiagonal'_apply]

lemma fiber_unique (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u w : Fibers q p) (s t : Bits q) :
    fiberEquiv q v p hp (u,s) = fiberEquiv q v p hp (w,t) ↔ u=w ∧ s=t := by
  rw [(fiberEquiv q v p hp).injective.eq_iff]
  simp only [Prod.mk.injEq]

lemma fiber_cover (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (x : Bits (q*n)) :
    ∃ u t, fiberEquiv q v p hp (u,t) = x := by
  obtain ⟨⟨u,t⟩,h⟩ := (fiberEquiv q v p hp).surjective x
  exact ⟨u,t,h⟩

/-- The translation appended to an inverse flips all selected bits, once per column. -/
def totalDirection (q : ℕ) (v : Bits n) : Bits (q*n) :=
  copyCombination q v (fun _ => 1)

def binaryFlip : Matrix (ZMod 2) (ZMod 2) ℂ :=
  Matrix.reindex TensorWords.bitEquiv TensorWords.bitEquiv swap

lemma binaryC_square : TensorWords.binaryC * TensorWords.binaryC = binaryFlip := by
  change (Matrix.reindexAlgEquiv ℂ ℂ TensorWords.bitEquiv) C *
    (Matrix.reindexAlgEquiv ℂ ℂ TensorWords.bitEquiv) C = _
  rw [← map_mul, C_square]
  rfl

lemma binaryFlip_apply (s t : ZMod 2) : binaryFlip s t = if s=t+1 then 1 else 0 := by
  rcases binary_values s with rfl | rfl <;> rcases binary_values t with rfl | rfl <;>
    simp [binaryFlip, Matrix.reindex_apply, swap, CharTwo.add_self_eq_zero]

lemma tensorFlip_translation (q : ℕ) : PiTensor.matrix (fun _ : Fin q => binaryFlip) =
    translation (fun _ : Fin q => 1) := by
  ext s t
  change (∏ c, binaryFlip (s c) (t c)) = if s=t+(fun _ => 1) then 1 else 0
  simp_rw [binaryFlip_apply]
  by_cases h : s=t+(fun _ => 1)
  · subst s
    simp
  · rw [ite_eq_right h]
    obtain ⟨c,hc⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [Pi.add_apply] at hc
    simp [hc]

lemma copiedProduct_square (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    copiedProduct q v * copiedProduct q v = translation (totalDirection q v) := by
  rw [copiedProduct_fibers q v p hp, ← map_mul]
  rw [← PiTensor.mul]
  have h : (fun _ : Fin q => TensorWords.binaryC) * (fun _ : Fin q => TensorWords.binaryC) =
      fun _ : Fin q => binaryFlip := by funext c; exact binaryC_square
  rw [h, tensorFlip_translation, fiber_translation]
  rfl

lemma copiedProduct_inverse (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    (copiedProduct q v)⁻¹ = translation (totalDirection q v) * copiedProduct q v := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, copiedProduct_square q v p hp, translation_square]

lemma copiedProduct_list (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (L : List (Fin q)) (hL : L.Nodup) (hfull : ∀ c, c∈L) :
    (L.map (fun c => directionalMatrix (copyVector q v c))).prod = copiedProduct q v := by
  rw [copiedProduct_fibers q v p hp]
  simp_rw [copyVector, ← fiber_directional q v p hp]
  rw [show L.map (fun c => fiberHom q v p hp (directionalMatrix (unit c))) =
      (L.map (fun c => directionalMatrix (unit c))).map (fiberHom q v p hp) from (List.map_map ..).symm]
  rw [← map_list_prod, unit_axes_product_list q L hL hfull]

/-- The inverse chronological column product is exactly a simultaneous translation after the forward group. -/
def copiedInverseProduct (q : ℕ) (v : Bits n) : Matrix (Bits (q*n)) (Bits (q*n)) ℂ :=
  (Finset.univ.toList.map (fun c => (directionalMatrix (copyVector q v c))⁻¹)).reverse.prod

lemma copiedInverseProduct_eq (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    copiedInverseProduct q v = translation (totalDirection q v) * copiedProduct q v := by
  have h := Matrix.list_prod_inv_reverse
    (Finset.univ.toList.map (fun c => directionalMatrix (copyVector q v c)))
  rw [copiedProduct_list q v p hp _ (Finset.nodup_toList _) (by intro c; simp)] at h
  have hlist : copiedInverseProduct q v = (copiedProduct q v)⁻¹ := by
    simpa only [copiedInverseProduct, List.map_reverse, List.map_map, Function.comp_def] using h.symm
  rw [hlist, copiedProduct_inverse q v p hp]

/-- The inverse uses the very same fibers and forward tensor kernel, with all
    selected output bits translated.  Scalar inputs remain arbitrary. -/
theorem copiedInverseProduct_array (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (X : Bits (q*n) → ℂ) (u : Fibers q p) (s : Bits q) :
    (copiedInverseProduct q v).mulVec X (fiberEquiv q v p hp (u,s)) =
      (tensorPower C q).mulVec (fun b => X (fiberCoordinates q v p hp ⟨u,b⟩))
        ((selectedBits q).symm (s + (fun _ => 1))) := by
  rw [copiedInverseProduct_eq q v p hp, ← Matrix.mulVec_mulVec]
  have ht (Y : Bits (q*n) → ℂ) (x : Bits (q*n)) :
      (translation (totalDirection q v)).mulVec Y x = Y (x + totalDirection q v) := by
    simp [Matrix.mulVec, dotProduct, FrameWords.translation_entry]
  rw [ht, totalDirection, ← fiberEquiv_add]
  have hc : fiberEquiv q v p hp (u,s + (fun _ => 1)) =
      fiberCoordinates q v p hp ⟨u, (selectedBits q).symm (s + (fun _ => 1))⟩ := by
    simp [fiberCoordinates]
  rw [hc, copiedProduct_array q v p hp]

/-- The grouped call schema uses C^tensor q as its kernel, once per actual fiber.
    It does not claim that a grouped call is a RAM instruction. -/
def fiberAddresses (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    (Σ _ : Fibers q p, Fin (2^q)) ≃ Fin (2^(q*n)) :=
  (fiberCoordinates q v p hp).trans (addresses (q*n))

def groupedEmbedding (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u : Fibers q p) : Fin (2^q) ↪ Fin (2^(q*n)) :=
  (Embedded.sigmaIn u).trans (fiberAddresses q v p hp).toEmbedding

def groupedForwardWord (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    List (WordStep (tensorPower C q) (2^(q*n))) :=
  (Finset.univ.toList.map (fun u : Fibers q p =>
    WordStep.call (groupedEmbedding q v p hp u))).reverse

theorem groupedForwardWord_calls (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    wordCalls (groupedForwardWord q v p hp) = 2^(q*(n-1)) := by
  simpa [groupedForwardWord, wordCalls, WordStep.calls, List.map_reverse, List.map_map,
    Function.comp_def] using fibers_card q v p hp

theorem groupedForwardWord_matrix (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    wordMatrix (groupedForwardWord q v p hp) =
      Matrix.reindex (addresses (q*n)) (addresses (q*n)) (copiedProduct q v) := by
  have hc (u : Fibers q p) : embeddedCall (tensorPower C q) (groupedEmbedding q v p hp u) =
      Matrix.reindex (fiberAddresses q v p hp) (fiberAddresses q v p hp)
        (Embedded.matrix (Embedded.sigmaIn u) (tensorPower C q)) := by
    rw [Packing.embeddedCall_eq, groupedEmbedding, ← Embedded.matrix_comp, Embedded.matrix_equiv]
  simp only [groupedForwardWord, wordMatrix, List.map_reverse, List.reverse_reverse,
    List.map_map, Function.comp_def, WordStep.matrix, hc]
  rw [show Finset.univ.toList.map (fun u : Fibers q p =>
      Matrix.reindex (fiberAddresses q v p hp) (fiberAddresses q v p hp)
        (Embedded.matrix (Embedded.sigmaIn u) (tensorPower C q))) =
      (Finset.univ.toList.map (fun u : Fibers q p =>
        Embedded.matrix (Embedded.sigmaIn u) (tensorPower C q))).map
          (Matrix.reindexAlgEquiv ℂ ℂ (fiberAddresses q v p hp)).toMonoidHom
    from (List.map_map ..).symm]
  rw [← map_list_prod, Embedded.blockDiagonal'_product, copiedProduct_blocks q v p hp]
  rfl

def groupedInverseWord (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    List (WordStep (tensorPower C q) (2^(q*n))) :=
  groupedForwardWord q v p hp ++
    [.monomial (translationFin (totalDirection q v)) (translationFin_isMonomial _)]

theorem groupedInverseWord_calls (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    wordCalls (groupedInverseWord q v p hp) = 2^(q*(n-1)) := by
  rw [groupedInverseWord, TypedKernelWords.wordCalls_append, groupedForwardWord_calls]
  simp [wordCalls, WordStep.calls]

theorem groupedInverseWord_matrix (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) :
    wordMatrix (groupedInverseWord q v p hp) =
      Matrix.reindex (addresses (q*n)) (addresses (q*n)) (copiedInverseProduct q v) := by
  rw [groupedInverseWord, TypedKernelWords.wordMatrix_append, groupedForwardWord_matrix,
    copiedInverseProduct_eq q v p hp, PaddingWords.reindex_mul]
  simp [wordMatrix, translationFin, WordStep.matrix]

lemma copyVector_norm (q : ℕ) (v : Bits n) (hv : dot v v = 1) (c : Fin q) :
    dot (copyVector q v c) (copyVector q v c) = 1 := by
  unfold copyVector copyCombination
  rw [StageFrames.coordinates_dot, dot_tensor, dot_units]
  simp [hv]

lemma copyVector_weight (q : ℕ) (v : Bits n) (c : Fin q) :
    weightModFour (copyVector q v c) = weightModFour v := by
  unfold copyVector copyCombination weightModFour
  rw [StageFrames.coordinates_weight, weight_tensor, BinaryColumns.weight_unit, one_mul]

lemma copyVector_pivot (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (c : Fin q) :
    copyVector q v c (finProdFinEquiv (c,p)) = 1 := by
  simp [copyVector, copyCombination_apply, unit, hp]

/-- Geometric decreasing orientation and weight-three phases are both retained. -/
def inverseOrientation (v : Bits n) (decreasing : Bool) : Bool :=
  if weightModFour v = 1 then decreasing else !decreasing

lemma directionalMatrix_inverse (v : Bits n) (p : Fin n) (hp : v p = 1) :
    (directionalMatrix v)⁻¹ = translation v * directionalMatrix v := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, directionalMatrix_square v p hp, translation_square]

lemma reindex_directional_inverse (v : Bits n) (p : Fin n) (hp : v p = 1) :
    Matrix.reindex (addresses n) (addresses n) (directionalMatrix v)⁻¹ =
      (directionalC v)⁻¹ := by
  rw [directionalMatrix_inverse v p hp, directionalC_inverse v p hp,
    PaddingWords.reindex_mul]
  rfl

lemma signedLayer_matrix (v : Bits n) (hv : dot v v = 1) (p : Fin n) (hp : v p = 1)
    (decreasing : Bool) :
    wordMatrix (FrameWords.signedLayer v hv decreasing) =
      Matrix.reindex (addresses n) (addresses n)
        (if inverseOrientation v decreasing then (directionalMatrix v)⁻¹ else directionalMatrix v) := by
  have hf : wordMatrix (directionalWord v (FrameWords.norm_one_nonzero v hv)) = directionalC v :=
    directionalWordAt_matrix _ _ _
  have hi : wordMatrix (inverseDirectionalWord v (FrameWords.norm_one_nonzero v hv)) =
      (directionalC v)⁻¹ := inverseDirectionalWordAt_matrix _ _ _
  unfold FrameWords.signedLayer inverseOrientation
  split <;> cases decreasing <;> simp [hf, hi, reindex_directional_inverse v p hp, directionalC]

/-- This is the literal C-pair word already used by the copied residual basis. -/
def signedColumnWord (q : ℕ) (v : Bits n) (hv : dot v v = 1) (decreasing : Bool) :
    List (WordStep C (2^(q*n))) :=
  FrameWords.signedFrameList (fun c => copyVector q v c) (copyVector_norm q v hv)
    decreasing Finset.univ.toList

theorem signedColumnWord_calls (q : ℕ) (v : Bits n) (hv : dot v v = 1)
    (decreasing : Bool) (hn : 1 ≤ q*n) :
    wordCalls (signedColumnWord q v hv decreasing) = q * 2^(q*n-1) := by
  rw [signedColumnWord, FrameWords.signedFrameList_calls hn]
  simp

theorem signedColumnWord_matrix (q : ℕ) (v : Bits n) (hv : dot v v = 1)
    (p : Fin n) (hp : v p = 1) (decreasing : Bool) :
    wordMatrix (signedColumnWord q v hv decreasing) =
      Matrix.reindex (addresses (q*n)) (addresses (q*n))
        (if inverseOrientation v decreasing then copiedInverseProduct q v else copiedProduct q v) := by
  have hs (c : Fin q) := signedLayer_matrix (copyVector q v c) (copyVector_norm q v hv c)
    (finProdFinEquiv (c,p)) (copyVector_pivot q v p hp c) decreasing
  simp only [inverseOrientation, copyVector_weight] at hs
  unfold signedColumnWord FrameWords.signedFrameList
  rw [TensorWords.wordMatrix_flatten]
  simp only [List.map_map, Function.comp_def, hs]
  change ((Finset.univ.toList.map (fun c =>
      (Matrix.reindexAlgEquiv ℂ ℂ (addresses (q*n)))
        (if inverseOrientation v decreasing then (directionalMatrix (copyVector q v c))⁻¹
          else directionalMatrix (copyVector q v c)))).reverse).prod = _
  rw [← List.map_reverse]
  rw [show Finset.univ.toList.reverse.map (fun c =>
      (Matrix.reindexAlgEquiv ℂ ℂ (addresses (q*n)))
        (if inverseOrientation v decreasing then (directionalMatrix (copyVector q v c))⁻¹
          else directionalMatrix (copyVector q v c))) =
      (Finset.univ.toList.reverse.map (fun c =>
        if inverseOrientation v decreasing then (directionalMatrix (copyVector q v c))⁻¹
          else directionalMatrix (copyVector q v c))).map
        (Matrix.reindexAlgEquiv ℂ ℂ (addresses (q*n))).toMonoidHom from (List.map_map ..).symm]
  rw [← map_list_prod]
  cases inverseOrientation v decreasing <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, copiedInverseProduct, copiedProduct,
      List.map_reverse] <;> rfl

/-- The actual signed C word can be replaced algebraically by one forward grouped
    tensor call per fiber and, exactly when required, a literal translation. -/
theorem signedColumnWord_grouped (q : ℕ) (v : Bits n) (hv : dot v v = 1)
    (p : Fin n) (hp : v p = 1) (decreasing : Bool) :
    wordMatrix (signedColumnWord q v hv decreasing) =
      wordMatrix (if inverseOrientation v decreasing then groupedInverseWord q v p hp
        else groupedForwardWord q v p hp) := by
  rw [signedColumnWord_matrix q v hv p hp]
  cases inverseOrientation v decreasing <;>
    simp [groupedForwardWord_matrix, groupedInverseWord_matrix]

def groupedSignedWord (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (decreasing : Bool) : List (WordStep (tensorPower C q) (2^(q*n))) :=
  if inverseOrientation v decreasing then groupedInverseWord q v p hp
    else groupedForwardWord q v p hp

/-- The signed orientation changes only the monomial suffix, never the number of
    forward q-bit kernel calls. -/
theorem groupedSignedWord_calls (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (decreasing : Bool) : wordCalls (groupedSignedWord q v p hp decreasing) = 2^(q*(n-1)) := by
  unfold groupedSignedWord
  split <;> simp only [groupedInverseWord_calls, groupedForwardWord_calls]

lemma inverseOrientation_weight_one (v : Bits n) (decreasing : Bool)
    (h : weightModFour v = 1) : inverseOrientation v decreasing = decreasing := by
  simp [inverseOrientation, h]

lemma inverseOrientation_weight_three (v : Bits n) (decreasing : Bool)
    (h : weightModFour v = 3) : inverseOrientation v decreasing = !decreasing := by
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  simp [inverseOrientation, h, h31]

lemma copyVector_edge (q : ℕ) {A B : FramedScheduleWords.Label n}
    (e : FramedScheduleWords.NestedEdge A B) (c : Fin q) (k : Fin e.dimension) :
    copyVector q (UniformFixedNetwork.edgeVectors e k) c =
      UniformFixedNetwork.columnDirection q e c k := rfl

lemma edgeVector_norm {A B : FramedScheduleWords.Label n}
    (e : FramedScheduleWords.NestedEdge A B) (k : Fin e.dimension) :
    dot (UniformFixedNetwork.edgeVectors e k) (UniformFixedNetwork.edgeVectors e k) = 1 := by
  simpa using UniformFixedNetwork.edgeVectors_orthonormal e k k

/-- Every fixed residual has a pivot already in its original n-bit direction. -/
theorem edgeVector_has_pivot {A B : FramedScheduleWords.Label n}
    (e : FramedScheduleWords.NestedEdge A B) (k : Fin e.dimension) :
    ∃ p, UniformFixedNetwork.edgeVectors e k p = 1 :=
  exists_pivot _ (FrameWords.norm_one_nonzero _ (edgeVector_norm e k))

/-- Connection to the actual fixed residual direction, including its signed orientation. -/
theorem edge_signed_fibers (q : ℕ) {A B : FramedScheduleWords.Label n}
    (e : FramedScheduleWords.NestedEdge A B) (k : Fin e.dimension)
    (p : Fin n) (hp : UniformFixedNetwork.edgeVectors e k p = 1) :
    wordMatrix (signedColumnWord q (UniformFixedNetwork.edgeVectors e k) (edgeVector_norm e k)
      (UniformFixedNetwork.edgeInverse e)) =
      wordMatrix (if inverseOrientation (UniformFixedNetwork.edgeVectors e k)
          (UniformFixedNetwork.edgeInverse e)
        then groupedInverseWord q (UniformFixedNetwork.edgeVectors e k) p hp
        else groupedForwardWord q (UniformFixedNetwork.edgeVectors e k) p hp) :=
  signedColumnWord_grouped q _ (edgeVector_norm e k) p hp _

/-- The finite set of addresses of a fiber, using the prescribed bit coordinates. -/
def fiberSet (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (u : Fibers q p) :
    Finset (Bits (q*n)) := Finset.univ.map
      ⟨fun s => fiberEquiv q v p hp (u,s), by
        intro s t h
        exact ((fiber_unique q v p hp u u s t).mp h).2⟩

lemma fiberSet_card (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1) (u : Fibers q p) :
    (fiberSet q v p hp u).card = 2^q := by
  simp [fiberSet]

lemma fiberSet_disjoint (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (u w : Fibers q p) (h : u ≠ w) : Disjoint (fiberSet q v p hp u) (fiberSet q v p hp w) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, _, hs⟩ := Finset.mem_map.mp hx
  obtain ⟨t, _, ht⟩ := Finset.mem_map.mp hy
  exact h ((fiber_unique q v p hp u w s t).mp (hs.trans ht.symm)).1

lemma fiberSet_cover (q : ℕ) (v : Bits n) (p : Fin n) (hp : v p = 1)
    (x : Bits (q*n)) : ∃ u, x ∈ fiberSet q v p hp u := by
  obtain ⟨u,t,h⟩ := fiber_cover q v p hp x
  exact ⟨u, Finset.mem_map.mpr ⟨t, Finset.mem_univ _, h⟩⟩

end
end ExactFourierCircuits.UniformResidualFibers
