import UniformResidualFibers
import UniformBinaryXorCoordinates
import UniformBinaryTensorCMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualNativeCoordinates
open OAI.ExactFourier BinaryFrames DirectionalWords UniformResidualFibers
open UniformBinaryXorCoordinates UniformBinaryTensorCoordinates
open scoped BigOperators Kronecker
noncomputable section

@[simp] theorem bitTransport (i : Fin 2) :
 TensorWords.bitEquiv.symm (UniformBinaryXorCoordinates.bitEquiv i)=i := by
 fin_cases i <;> rfl

/-- Delete the pivot with the explicit order-preserving Fin map. -/
def representative (w : ℕ) (p : Fin (w+1)) : Bits w ≃ Representatives p where
 toFun x := ⟨Fin.insertNth p 0 x, by simp⟩
 invFun x := Fin.removeNth p x.val
 left_inv x := by simp
 right_inv x := by
  apply Subtype.ext
  change Fin.insertNth p 0 (Fin.removeNth p x.val)=x.val
  simpa only [x.property] using Fin.insertNth_self_removeNth p x.val
@[simp] theorem representative_pivot (w : ℕ) (p : Fin (w+1)) (x : Bits w) :
 (representative w p x).val p=0 := (representative w p x).property
@[simp] theorem representative_other (w : ℕ) (p : Fin (w+1)) (x : Bits w) (i : Fin w) :
 (representative w p x).val (p.succAbove i)=x i := by simp [representative]
def representativeColumns (q w : ℕ) (p : Fin (w+1)) : Bits (q*w) ≃ Fibers q p :=
 (flattenColumns q w).symm.trans (Equiv.piCongrRight (fun _=>representative w p))
@[simp] theorem representativeColumns_other (q w : ℕ) (p : Fin (w+1))
 (x : Bits (q*w)) (c : Fin q) (i : Fin w) :
 (representativeColumns q w p x c).val (p.succAbove i)=x (finProdFinEquiv (c,i)) := by
 simp [representativeColumns,flattenColumns]
/-- Explicit native addresses, without chosen finite enumeration. -/
def nativeFiber (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1) :
 (Fin (2^(q*w)) × Fin (2^q)) ≃ Fin (2^(q*(w+1))) :=
 (((binaryCoordinates (q*w)).trans (representativeColumns q w p)).prodCongr
   (binaryCoordinates q)).trans
   ((fiberEquiv q v p hp).trans (binaryCoordinates (q*(w+1))).symm)
@[simp] theorem nativeFiber_coordinates (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1))
 (hp : v p=1) (b : Fin (2^(q*w))) (t : Fin (2^q)) :
 binaryCoordinates (q*(w+1)) (nativeFiber q w v p hp (b,t))=
 fiberEquiv q v p hp (representativeColumns q w p (binaryCoordinates (q*w) b),
  binaryCoordinates q t) := by simp [nativeFiber]
@[simp] theorem nativeFiber_pivot (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1))
 (hp : v p=1) (b : Fin (2^(q*w))) (t : Fin (2^q)) (c : Fin q) :
 binaryCoordinates (q*(w+1)) (nativeFiber q w v p hp (b,t))
   (finProdFinEquiv (c,p))=binaryCoordinates q t c := by
 rw [nativeFiber_coordinates,fiberEquiv_apply]
 rcases binary_values (binaryCoordinates q t c) with h|h
 <;> simp [pairPoint,h,hp,(representativeColumns q w p (binaryCoordinates (q*w) b) c).property]
@[simp] theorem nativeFiber_other (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1))
 (hp : v p=1) (b : Fin (2^(q*w))) (t : Fin (2^q)) (c : Fin q) (i : Fin w) :
 binaryCoordinates (q*(w+1)) (nativeFiber q w v p hp (b,t))
   (finProdFinEquiv (c,p.succAbove i))=
 binaryCoordinates (q*w) b (finProdFinEquiv (c,i))+
 binaryCoordinates q t c*v (p.succAbove i) := by
 rw [nativeFiber_coordinates,fiberEquiv_apply]
 rcases binary_values (binaryCoordinates q t c) with h|h
 <;> simp [pairPoint,h]
theorem native_partition (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1)
 (z : Fin (2^(q*(w+1)))) :
 ∃! bt : Fin (2^(q*w)) × Fin (2^q), nativeFiber q w v p hp bt=z := by
 refine ⟨(nativeFiber q w v p hp).symm z, by simp, ?_⟩
 intro y hy
 exact (nativeFiber q w v p hp).injective (hy.trans (by simp))
def nativeCopiedMatrix (q w : ℕ) (v : Bits (w+1)) :
 Matrix (Fin (2^(q*(w+1)))) (Fin (2^(q*(w+1)))) ℂ :=
 Matrix.reindex (binaryCoordinates (q*(w+1))).symm
  (binaryCoordinates (q*(w+1))).symm (copiedProduct q v)
/-- The child kernel is the actual little-endian q-bit tensor operator. -/
theorem nativeCopied_blocks (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1) :
 nativeCopiedMatrix q w v=
 Matrix.reindex (nativeFiber q w v p hp) (nativeFiber q w v p hp)
  ((1 : Matrix (Fin (2^(q*w))) (Fin (2^(q*w))) ℂ) ⊗ₖ physicalMatrix q) := by
 ext x y
 obtain ⟨⟨b,s⟩,rfl⟩ := (nativeFiber q w v p hp).surjective x
 obtain ⟨⟨c,t⟩,rfl⟩ := (nativeFiber q w v p hp).surjective y
 rw [nativeCopiedMatrix,copiedProduct_fibers q v p hp]
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
  Equiv.symm_apply_apply,nativeFiber_coordinates]
 change ((1 : Matrix (Fibers q p) (Fibers q p) ℂ) ⊗ₖ
   PiTensor.matrix (fun _ : Fin q=>TensorWords.binaryC))
    ((fiberEquiv q v p hp).symm (fiberEquiv q v p hp
      (representativeColumns q w p (binaryCoordinates (q*w) b),binaryCoordinates q s)))
    ((fiberEquiv q v p hp).symm (fiberEquiv q v p hp
      (representativeColumns q w p (binaryCoordinates (q*w) c),binaryCoordinates q t)))=
    (if b=c then (1:ℂ) else 0)*physicalMatrix q s t
 simp only [Equiv.symm_apply_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
 have same : representativeColumns q w p (binaryCoordinates (q*w) b)=
      representativeColumns q w p (binaryCoordinates (q*w) c) ↔ b=c :=
     ((representativeColumns q w p).injective.eq_iff.trans
       (binaryCoordinates (q*w)).injective.eq_iff)
 simp only [same]
 have coefficients : PiTensor.matrix (fun _ : Fin q=>TensorWords.binaryC)
   (binaryCoordinates q s) (binaryCoordinates q t)=physicalMatrix q s t := by
  change (∏i:Fin q,C (TensorWords.bitEquiv.symm (binaryCoordinates q s i))
   (TensorWords.bitEquiv.symm (binaryCoordinates q t i)))=
   ∏i:Fin q,C (coordinates q s i) (coordinates q t i)
  simp only [binaryCoordinates,Equiv.trans_apply,Equiv.piCongrRight_apply,Pi.map_apply,bitTransport]
 rw [coefficients]
theorem nativeCopied_array (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1)
 (X : Fin (2^(q*(w+1)))→ℂ) (b : Fin (2^(q*w))) (t : Fin (2^q)) :
 (nativeCopiedMatrix q w v).mulVec X (nativeFiber q w v p hp (b,t))=
 (physicalMatrix q).mulVec (fun s=>X (nativeFiber q w v p hp (b,s))) t := by
 rw [nativeCopied_blocks q w v p hp]
 unfold Matrix.mulVec dotProduct
 rw [←(nativeFiber q w v p hp).sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

/-- Complete recursive groups of W arrays; no fiber is independently padded. -/
def batchFibers (q w b : ℕ) (h : b≤q*w) :
 (Fin (2^(q*w-b)) × Fin (2^b)) ≃ Fin (2^(q*w)) :=
 finProdFinEquiv.trans (finCongr (by rw [←Nat.pow_add];congr 1;omega))

def nativeBatches (q w b : ℕ) (h : b≤q*w) (v : Bits (w+1))
 (p : Fin (w+1)) (hp : v p=1) :
 (Fin (2^(q*w-b)) × (Fin (2^b) × Fin (2^q))) ≃ Fin (2^(q*(w+1))) :=
 (Equiv.prodAssoc _ _ _).symm.trans
  (((batchFibers q w b h).prodCongr (Equiv.refl _)).trans (nativeFiber q w v p hp))

theorem nativeBatches_apply (q w b : ℕ) (h : b≤q*w) (v : Bits (w+1))
 (p : Fin (w+1)) (hp : v p=1) (c : Fin (2^(q*w-b)))
 (i : Fin (2^b)) (t : Fin (2^q)) :
 nativeBatches q w b h v p hp (c,(i,t))=
 nativeFiber q w v p hp (batchFibers q w b h (c,i),t) := rfl

theorem complete_batch_size (q w b : ℕ) (h : b≤q*w) :
 2^(q*w-b)*(2^b*2^q)=2^(q*(w+1)) := by
 rw [←Nat.mul_assoc,←Nat.pow_add,←Nat.pow_add]
 congr 1
 simp only [Nat.mul_add,Nat.mul_one]
 omega

theorem seed_batch_capacity (q : ℕ) (hq : 1≤q) :
 ExplicitSeedBudget.roleBits≤q*(ExplicitSeedBudget.m-1) := by
 change 71≤q*(1000000-1)
 norm_num
 omega

/-- Each child sees W simultaneous q-bit arrays at native role-major offsets. -/
theorem nativeBatches_array (q w b : ℕ) (h : b≤q*w) (v : Bits (w+1))
 (p : Fin (w+1)) (hp : v p=1) (X : Fin (2^(q*(w+1)))→ℂ)
 (c : Fin (2^(q*w-b))) (i : Fin (2^b)) (t : Fin (2^q)) :
 (nativeCopiedMatrix q w v).mulVec X (nativeBatches q w b h v p hp (c,(i,t)))=
 (physicalMatrix q).mulVec (fun s=>X (nativeBatches q w b h v p hp (c,(i,s)))) t :=
 nativeCopied_array q w v p hp X _ t


@[simp] theorem encode_zero (k : ℕ) : encode (0 : Bits k)=0 := by
 apply Fin.ext
 rw [encode_value]
 simp
@[simp] theorem coordinates_zero (k : ℕ) : binaryCoordinates k 0=0 := by
 have h:=congrArg (binaryCoordinates k) (encode_zero k)
 simpa [encode] using h.symm

theorem nativeFiber_xor (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1)
 (b c : Fin (2^(q*w))) (s t : Fin (2^q)) :
 nativeFiber q w v p hp (xorIndex b c,xorIndex s t)=
 xorIndex (nativeFiber q w v p hp (b,s)) (nativeFiber q w v p hp (c,t)) := by
 apply (binaryCoordinates (q*(w+1))).injective
 rw [xor_coordinates]
 funext j
 obtain ⟨⟨column,i⟩,rfl⟩ := (finProdFinEquiv : Fin q×Fin (w+1)≃Fin (q*(w+1))).surjective j
 rcases Fin.eq_self_or_eq_succAbove p i with hi|⟨i,hi⟩
 · subst hi
   simp only [Pi.add_apply,nativeFiber_pivot,xor_coordinates]
 · subst hi
   simp only [Pi.add_apply,nativeFiber_other,xor_coordinates]
   ring

@[simp] theorem nativeFiber_zero (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1)) (hp : v p=1) :
 nativeFiber q w v p hp (0,0)=0 := by
 apply (binaryCoordinates (q*(w+1))).injective
 funext j
 obtain ⟨⟨c,i⟩,rfl⟩ := (finProdFinEquiv : Fin q×Fin (w+1)≃Fin (q*(w+1))).surjective j
 rcases Fin.eq_self_or_eq_succAbove p i with hi|⟨i,hi⟩
 · subst hi
   simp
 · subst hi
   simp

/-- Selected-bit basis images are exactly the copied column directions. -/
theorem nativeFiber_selected_image (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1))
 (hp : v p=1) (c : Fin q) :
 nativeFiber q w v p hp (0,encode (unit c))=encode (copyVector q v c) := by
 apply (binaryCoordinates (q*(w+1))).injective
 simp only [encode,Equiv.apply_symm_apply]
 funext j
 obtain ⟨⟨column,i⟩,rfl⟩ := (finProdFinEquiv : Fin q×Fin (w+1)≃Fin (q*(w+1))).surjective j
 rcases Fin.eq_self_or_eq_succAbove p i with hi|⟨i,hi⟩
 · subst hi
   simp [copyVector,copyCombination_apply,hp]
 · subst hi
   simp [copyVector,copyCombination_apply]

/-- Representative-bit images are literal native powers of two, with the
pivot omitted in its ordinary order. -/
theorem nativeFiber_representative_image (q w : ℕ) (v : Bits (w+1)) (p : Fin (w+1))
 (hp : v p=1) (c : Fin q) (i : Fin w) :
 nativeFiber q w v p hp (encode (unit (finProdFinEquiv (c,i))),0)=
 encode (unit (finProdFinEquiv (c,p.succAbove i))) := by
 apply (binaryCoordinates (q*(w+1))).injective
 simp only [encode,Equiv.apply_symm_apply]
 funext j
 obtain ⟨⟨column,k⟩,rfl⟩ := (finProdFinEquiv : Fin q×Fin (w+1)≃Fin (q*(w+1))).surjective j
 rcases Fin.eq_self_or_eq_succAbove p k with hk|⟨k,hk⟩
 · subst hk
   simp [unit]
 · subst hk
   simp [unit,Fin.succAbove_right_injective.eq_iff]

end
end ExactFourierCircuits.UniformResidualNativeCoordinates
