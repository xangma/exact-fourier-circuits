import UniformBinaryTensorCoordinates
import ColumnTerminalFlat
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBinaryXorCoordinates
open BinaryFrames UniformBinaryTensorCoordinates
open scoped BigOperators
noncomputable section

/-- Explicit little-endian physical binary coordinates, valued in F2. -/
def bitEquiv : Fin 2≃F2 where
 toFun:=fun i=>(i.val:F2)
 invFun:=fun z=>⟨z.val,ZMod.val_lt z⟩
 left_inv:=by intro i;apply Fin.ext;simp [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
 right_inv:=ZMod.natCast_zmod_val

def binaryCoordinates (k : ℕ) : Fin (2^k)≃Vec (Fin k) :=
 (coordinates k).trans (Equiv.piCongrRight (fun _=>bitEquiv))

theorem binaryCoordinates_value (k : ℕ) (z : Fin (2^k)) (i : Fin k) :
 (binaryCoordinates k z i).val=(z.val/2^i.val)%2 := by
 simp [binaryCoordinates,bitEquiv,coordinates_value,ZMod.val_natCast]

def xorIndex {k : ℕ} (a b : Fin (2^k)) : Fin (2^k) :=
 ⟨a.val^^^b.val,Nat.xor_lt_two_pow a.isLt b.isLt⟩

theorem xor_coordinates (k : ℕ) (a b : Fin (2^k)) :
 binaryCoordinates k (xorIndex a b)=binaryCoordinates k a+binaryCoordinates k b := by
 funext i
 apply ZMod.val_injective
 rw [binaryCoordinates_value]
 simp only [xorIndex,Fin.val_mk,Pi.add_apply]
 rw [Nat.xor_div_two_pow,Nat.xor_mod_two_eq,ZMod.val_add,binaryCoordinates_value,binaryCoordinates_value]
 rw [←Nat.add_mod]

/-- Integer encoding of an actual binary vector, with no chosen enumeration. -/
def encode {k : ℕ} (u : Vec (Fin k)) : Fin (2^k) := (binaryCoordinates k).symm u

theorem encode_value {k : ℕ} (u : Vec (Fin k)) :
 (encode u).val=∑i:Fin k,2^i.val*(u i).val := by
 simp [encode,binaryCoordinates,bitEquiv,coordinates_inverse]

theorem translated_address {k : ℕ} (z : Fin (2^k)) (u : Vec (Fin k)) :
 binaryCoordinates k (xorIndex z (encode u))=binaryCoordinates k z+u := by
 rw [xor_coordinates,encode,Equiv.apply_symm_apply]

/-- Copied Y translation repeats each original descriptor in every physical
column: bit c*m+j has exactly the original descriptor bit j. -/
theorem repeated_direction_bit (q m : ℕ) (u : Vec (Fin m)) (c : Fin q) (j : Fin m) :
 ColumnTerminalFlat.direction q u (finProdFinEquiv (c,j))=u j := by
 change u ((finProdFinEquiv.symm (finProdFinEquiv (c,j))).2)=u j
 rw [Equiv.symm_apply_apply]

theorem repeated_mask_value (q m : ℕ) (u : Vec (Fin m)) :
 (encode (ColumnTerminalFlat.direction q u)).val=
 ∑c:Fin q,∑j:Fin m,2^(c.val*m+j.val)*(u j).val := by
 rw [encode_value]
 rw [←(finProdFinEquiv : Fin q×Fin m≃Fin (q*m)).sum_comp]
 rw [Fintype.sum_prod_type]
 simp [repeated_direction_bit,Nat.mul_comm,Nat.add_comm]

end
end ExactFourierCircuits.UniformBinaryXorCoordinates
