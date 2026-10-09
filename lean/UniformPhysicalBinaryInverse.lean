import UniformBinaryXorCoordinates

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalBinaryInverse
open OAI.ExactFourier BinaryFrames
open UniformBinaryTensorCoordinates UniformBinaryXorCoordinates
open scoped BigOperators
noncomputable section

def flip(i:Fin 2):Fin 2:=⟨1-i.val,by omega⟩
lemma flip_flip(i:Fin 2):flip (flip i)=i:=by fin_cases i <;>rfl
lemma flip_bit(i:Fin 2):bitEquiv (flip i)=bitEquiv i+1:=by fin_cases i <;>rfl
lemma swap_flip(i j:Fin 2):swap i j=(1:Matrix (Fin 2) (Fin 2) ℂ) (flip i) j:=by
 fin_cases i <;>fin_cases j <;>norm_num [swap,flip,Matrix.one_apply]

def mask(q:ℕ):Fin (2^q):=encode (1:Vec (Fin q))
lemma sum_two_pow(q:ℕ):(∑i:Fin q,2^i.val)+1=2^q:=by
 induction q with
 | zero=>simp
 | succ q ih=>
   rw [Fin.sum_univ_castSucc]
   simp only [Fin.val_castSucc,Fin.val_last,Nat.pow_succ]
   omega
lemma mask_value(q:ℕ):(mask q).val=2^q-1:=by
 rw [mask,encode_value]
 have each:∀i:Fin q,((1:Vec (Fin q)) i).val=1:=by intro i;rfl
 simp only [each,Nat.mul_one]
 have h:=sum_two_pow q
 omega
lemma coordinates_flip(q:ℕ)(x:Fin (2^q)):
 coordinates q (xorIndex x (mask q))=fun i=>flip (coordinates q x i):=by
 funext i
 apply bitEquiv.injective
 have h:=congrFun (translated_address x (1:Vec (Fin q))) i
 change bitEquiv (coordinates q (xorIndex x (mask q)) i)=bitEquiv (coordinates q x i)+1 at h
 exact h.trans (flip_bit _).symm

/-- The matrix homomorphism uses precisely the machine's numeric coordinates. -/
def physicalHom(q:ℕ):(Fin q→Matrix (Fin 2) (Fin 2) ℂ)→*Matrix (Fin (2^q)) (Fin (2^q)) ℂ:=
 (Matrix.reindexAlgEquiv ℂ ℂ (coordinates q).symm).toMonoidHom.comp PiTensor.hom
lemma physicalHom_apply(q:ℕ)(A:Fin q→Matrix (Fin 2) (Fin 2) ℂ):
 physicalHom q A=Matrix.reindex (coordinates q).symm (coordinates q).symm (PiTensor.matrix A):=rfl

def swapPhysical(q:ℕ):Matrix (Fin (2^q)) (Fin (2^q)) ℂ:=physicalHom q (fun _=>swap)
lemma physical_square(q:ℕ):physicalMatrix q*physicalMatrix q=swapPhysical q:=by
 change physicalHom q (fun _=>C)*physicalHom q (fun _=>C)=physicalHom q (fun _=>swap)
 rw [←map_mul]
 congr 1;funext i;exact C_square
lemma swap_square(q:ℕ):swapPhysical q*swapPhysical q=1:=by
 unfold swapPhysical
 rw [←map_mul]
 have eq:((fun _:Fin q=>swap)*(fun _=>swap))=(1:Fin q→Matrix (Fin 2) (Fin 2) ℂ):=by
   funext i;exact ExactFourierCircuits.swap_square
 rw [eq,map_one]
lemma physical_inverse(q:ℕ):(physicalMatrix q)⁻¹=swapPhysical q*physicalMatrix q:=by
 apply Matrix.inv_eq_left_inv
 rw [Matrix.mul_assoc,physical_square,swap_square]
lemma swapPhysical_apply(q:ℕ)(x y:Fin (2^q)):
 swapPhysical q x y=if xorIndex x (mask q)=y then 1 else 0:=by
 change (∏i:Fin q,swap (coordinates q x i) (coordinates q y i))=_
 simp only [swap_flip]
 change PiTensor.matrix (1:Fin q→Matrix (Fin 2) (Fin 2) ℂ)
   (fun i=>flip (coordinates q x i)) (coordinates q y)=_
 rw [PiTensor.one,←coordinates_flip,Matrix.one_apply]
 simp only [(coordinates q).injective.eq_iff]
lemma swapPhysical_mulVec(q:ℕ)(f:Fin (2^q)→ℂ)(x:Fin (2^q)):
 (swapPhysical q).mulVec f x=f (xorIndex x (mask q)):=by
 simp [Matrix.mulVec,dotProduct,swapPhysical_apply]
/-- The inverse needs exactly one positive child, followed by an all-ones
low-q-bit XOR. There is no additional child call, sign or scalar correction. -/
theorem inverse_mulVec(q:ℕ)(f:Fin (2^q)→ℂ)(x:Fin (2^q)):
 ((physicalMatrix q)⁻¹).mulVec f x=(physicalMatrix q).mulVec f (xorIndex x (mask q)):=by
 rw [physical_inverse,←Matrix.mulVec_mulVec,swapPhysical_mulVec]
end
end ExactFourierCircuits.UniformPhysicalBinaryInverse
