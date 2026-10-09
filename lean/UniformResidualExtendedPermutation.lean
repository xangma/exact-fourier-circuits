import UniformResidualSpectators
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualExtendedPermutation
open BinaryFrames UniformBinaryXorCoordinates UniformResidualPermutation UniformResidualNativeCoordinates
open UniformBinaryTensorCoordinates
open scoped BigOperators Kronecker
noncomputable section

def image (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (i:ℕ) : ℕ :=
 if hi:i< k+r then (UniformResidualSpectators.extend k r F (encode (unit ⟨i,hi⟩))).val else 0
lemma image_small (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (i:ℕ) (hi:i< k+r) : image k r F i< 2^(k+r) := by
 simp only [image,dite_eq_left hi]
 exact Fin.isLt _
lemma image_low (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (i:ℕ) (hi:i< k) :
 image k r F i=(F (encode (unit (⟨i,hi⟩:Fin k)))).val := by
 have larger:i< k+r:=by omega
 simp only [image,dite_eq_left larger]
 have input:(encode (unit (⟨i,larger⟩:Fin (k+r))))=
  (⟨(encode (unit (⟨i,hi⟩:Fin k))).val,(encode (unit (⟨i,hi⟩:Fin k))).isLt.trans_le
   (Nat.pow_le_pow_right (by omega) (by omega))⟩:Fin (2^(k+r))) := by apply Fin.ext;simp [encode_unit]
 rw [input,UniformResidualSpectators.extend_low]
lemma image_high (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0) (i:ℕ) (lo:k≤ i) (hi:i< k+r) :
 image k r F i=2^i := by
 let j:Fin r:=⟨i-k,by omega⟩
 have value:k+j.val=i:=by simp [j];omega
 simp only [image,dite_eq_left hi]
 have input:encode (unit (⟨i,hi⟩:Fin (k+r)))=encode (unit (⟨k+j.val,by omega⟩:Fin (k+r))):=by congr 2;apply Fin.ext;exact value.symm
 rw [input,UniformResidualSpectators.extend_high_unit k r F zero j,value]
lemma address_eq (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0)
 (add:∀a b,F (xorIndex a b)=xorIndex (F a) (F b)) (j:Fin (2^(k+r))) :
 UniformResidualFiberTraversal.address (image k r F) (k+r) 0 j.val=
 (UniformResidualSpectators.extend k r F j).val := by
 have h:=address_of_xor_equiv (UniformResidualSpectators.extend k r F)
  (UniformResidualSpectators.extend_zero k r F zero) (UniformResidualSpectators.extend_xor k r F add)
  (image k r F) (by intro i;simp [image,i.isLt]) (k+r) 0 j.val (by omega) j.isLt
 simpa using h

/-- Remainder bits join the representative labels of each copied direction.
The selected q coordinates are still the innermost contiguous array. -/
def fibers (q w r:ℕ) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1) :
 (Fin (2^(q*w+r))×Fin (2^q))≃Fin (2^(q*(w+1)+r)) :=
 ((UniformResidualSpectators.split (q*w) r).prodCongr (Equiv.refl _)).trans
  ((Equiv.prodAssoc _ _ _).trans
   (((Equiv.refl _).prodCongr (nativeFiber q w v p hp)).trans (UniformResidualSpectators.split (q*(w+1)) r).symm))
lemma fibers_coordinates (q w r:ℕ) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1)
 (b:Fin (2^(q*w+r))) (t:Fin (2^q)) :
 UniformResidualSpectators.split (q*(w+1)) r (fibers q w r v p hp (b,t))=
 ((UniformResidualSpectators.split (q*w) r b).1,nativeFiber q w v p hp ((UniformResidualSpectators.split (q*w) r b).2,t)) := by
 simp [fibers]

/-- Arithmetic flattening of all spectator/representative labels and q-bit
inner arrays. It is the physical fiber-major order consumed by batch RAM. -/
def flat (q w r:ℕ) : (Fin (2^(q*w+r))×Fin (2^q))≃Fin (2^(q*(w+1)+r)) :=
 ((UniformResidualSpectators.split (q*w) r).prodCongr (Equiv.refl _)).trans
  ((Equiv.prodAssoc _ _ _).trans
   (((Equiv.refl _).prodCongr (UniformResidualPermutation.splitInput q w).symm).trans
    (UniformResidualSpectators.split (q*(w+1)) r).symm))
lemma flat_value (q w r:ℕ) (b:Fin (2^(q*w+r))) (t:Fin (2^q)) :
 (flat q w r (b,t)).val=b.val*2^q+t.val:=by
 simp [flat,UniformResidualSpectators.split,UniformResidualPermutation.splitInput,finProdFinEquiv]
 have parts:=Nat.mod_add_div b.val (2^(q*w))
 have powers:2^(q*(w+1))=2^(q*w)*2^q:=by rw [Nat.mul_add,Nat.mul_one,Nat.pow_add]
 rw [powers]
 calc
  t.val+2^q*(b.val%2^(q*w))+2^(q*w)*2^q*(b.val/2^(q*w))=
   (b.val%2^(q*w)+2^(q*w)*(b.val/2^(q*w)))*2^q+t.val:=by ring
  _=b.val*2^q+t.val:=by rw [parts]

lemma fibers_flat (q w r:ℕ) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1)
 (b:Fin (2^(q*w+r))) (t:Fin (2^q)) :
 UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp)
  (flat q w r (b,t))=fibers q w r v p hp (b,t):=by
 simp [UniformResidualSpectators.extend,flat,fibers,UniformResidualPermutation.permutation,Prod.map]


def copiedMatrix (q w r:ℕ) (v:Vec (Fin (w+1))) : Matrix (Fin (2^(q*(w+1)+r))) (Fin (2^(q*(w+1)+r))) ℂ :=
 Matrix.reindex (UniformResidualSpectators.split (q*(w+1)) r).symm
  (UniformResidualSpectators.split (q*(w+1)) r).symm
  ((1:Matrix (Fin (2^r)) (Fin (2^r)) ℂ)⊗ₖnativeCopiedMatrix q w v)
/-- The spectator coordinates are untouched; each native copied-column
operator acts on the original qm coordinates. -/
def copiedArray (q w r:ℕ) (v:Vec (Fin (w+1))) (X:Fin (2^(q*(w+1)+r))→ℂ) (z:Fin (2^(q*(w+1)+r))) : ℂ :=
 (nativeCopiedMatrix q w v).mulVec
  (fun y=>X ((UniformResidualSpectators.split (q*(w+1)) r).symm
    ((UniformResidualSpectators.split (q*(w+1)) r z).1,y)))
  (UniformResidualSpectators.split (q*(w+1)) r z).2
lemma copied_array (q w r:ℕ) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1)
 (X:Fin (2^(q*(w+1)+r))→ℂ) (b:Fin (2^(q*w+r))) (t:Fin (2^q)) :
 copiedArray q w r v X (fibers q w r v p hp (b,t))=
 (physicalMatrix q).mulVec (fun s=>X (fibers q w r v p hp (b,s))) t := by
 unfold copiedArray
 rw [fibers_coordinates]
 simpa only [fibers,Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Equiv.prodAssoc_apply,Prod.map] using
  nativeCopied_array q w v p hp (fun z=>X ((UniformResidualSpectators.split (q*(w+1)) r).symm
   ((UniformResidualSpectators.split (q*w) r b).1,z))) ((UniformResidualSpectators.split (q*w) r b).2) t

/-- Every recursive call sees exactly 2^b actual arrays, with no independent
padding of individual fibers. Spectator bits are in the same grouping. -/
def groups (q w r b:ℕ) (fits:b≤ q*w+r) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1) :
 (Fin (2^(q*w+r-b))×(Fin (2^b)×Fin (2^q)))≃Fin (2^(q*(w+1)+r)) :=
 (Equiv.prodAssoc _ _ _).symm.trans
  (((finProdFinEquiv.trans (finCongr (by rw [←Nat.pow_add];congr 1;omega))).prodCongr (Equiv.refl _)).trans
   (fibers q w r v p hp))
lemma groups_fibers (q w r b:ℕ) (fits:b≤ q*w+r) (v:Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1)
 (c:Fin (2^(q*w+r-b))) (i:Fin (2^b)) (t:Fin (2^q)) :
 groups q w r b fits v p hp (c,(i,t))=fibers q w r v p hp
  (finCongr (by rw [←Nat.pow_add];congr 1;omega) (finProdFinEquiv (c,i)),t):=rfl
lemma seed_groups_fit (q r:ℕ) (qp:1≤ q) :
 ExplicitSeedBudget.roleBits≤ q*(ExplicitSeedBudget.m-1)+r := by
 exact (UniformResidualNativeCoordinates.seed_batch_capacity q qp).trans (Nat.le_add_right _ _)

lemma complete_batches (q w r b:ℕ) (fits:b≤ q*w+r) :
 2^(q*w+r-b)*(2^b*2^q)=2^(q*(w+1)+r) := by
 rw [←Nat.mul_assoc,←Nat.pow_add,←Nat.pow_add]
 congr 1
 rw [Nat.mul_add,Nat.mul_one]
 omega
lemma padded_bits (q m r:ℕ) (qp:1≤ q) (rp:r< m) : q*m+r≤ q*(m+r) ∧ q*(m+r)≤ 2*(q*m+r) := by
 constructor <;> nlinarith
end
end ExactFourierCircuits.UniformResidualExtendedPermutation
