import UniformNativeResidualBasis
import UniformNativeRoleSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeUnitColumns
open OAI.ExactFourier BinaryFrames BinaryTensor DirectionalWords FrameWords FrameSpectrum
open UniformResidualFibers UniformNativeResidualBasis UniformNativeResidualSemantics
open UniformBinaryTensorCoordinates UniformBinaryXorCoordinates UniformResidualNativeCoordinates
open scoped BigOperators
noncomputable section

lemma copy_unit (q n : ℕ) (c : Fin q) (j : Fin n) :
 copyVector q (unit j) c=unit (finProdFinEquiv (c,j)) := by
 funext z
 obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin q×Fin n ≃ Fin (q*n)).surjective z
 rw [copyVector,copyCombination_apply]
 by_cases ha : a=c <;> by_cases hb : b=j <;>
  simp [unit,(finProdFinEquiv : Fin q×Fin n ≃ Fin (q*n)).injective.eq_iff,ha,hb]

/-- The actual unit-padding loop uses n original directions, each processed by
SAME-q column grouping, in ascending descriptor order. -/
def unitColumns (q n : ℕ) : List (WordStep C (2^(q*n))) :=
 ((List.finRange n).map (fun j => signedColumnWord q (unit j) (by simp [unit]) false)).flatten

lemma unitAxes_signed (n : ℕ) :
 wordMatrix (TensorWords.unitAxesWord n)=
 wordMatrix (signedFrameList (unit : Fin n→Bits n) (fun _ => by simp [unit]) false
  (Finset.univ.toList.reverse)) := by
 have hs (p : Fin n) : wordMatrix (TensorWords.unitAxisWord p)=
  wordMatrix (signedLayer (unit p) (by simp [unit]) false) := by
  rw [TensorWords.unitAxisWord_matrix,signedLayer_matrix (unit p) (by simp [unit]) p (by simp [unit]) false]
  simp [inverseOrientation,weightModFour_unit,directionalC]
 rw [TensorWords.unitAxesWord,signedFrameList,TensorWords.wordMatrix_flatten,TensorWords.wordMatrix_flatten]
 simp only [List.map_reverse,List.reverse_reverse,List.map_map,Function.comp_def]
 simp_rw [hs]

/-- The n SAME-q grouped unit calls compose to the exact ordinary q*n tensor.
No single q*n child call, commutation premise, or execution premise is used. -/
theorem unitColumns_matrix (q n : ℕ) :
 wordMatrix (unitColumns q n)=wordMatrix (TensorWords.unitAxesWord (q*n)) := by
 apply binaryAction_injective (q*n)
 apply operator_eq_of_characters
 intro ξ
 rw [unitColumns,groups_character,unitAxes_signed,FrameWords.signedFrameList_action,
  signedWord_character (unit : Fin (q*n)→Bits (q*n)) false (fun _ => by simp [unit])]
 simp only [List.map_reverse,List.sum_reverse,Finset.sum_map_toList,copy_unit,
  weightModFour_unit,dot_unit_left,edgeSign,Bool.false_eq_true,ite_false,one_mul]
 rw [←Fin.sum_univ_def,←(finProdFinEquiv : Fin q×Fin n ≃ Fin (q*n)).sum_comp]
 rw [Fintype.sum_prod_type,Finset.sum_comm]

lemma native_unitAxes (n : ℕ) :
 nativeWordMatrix (TensorWords.unitAxesWord n)=physicalMatrix n := by
 unfold nativeWordMatrix
 rw [TensorWords.unitAxesWord_matrix]
 ext x y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,originalToNative,Equiv.symm_trans_apply,
  Equiv.symm_symm,Equiv.symm_apply_apply]
 change PiTensor.matrix (fun _ : Fin n => TensorWords.binaryC)
  (binaryCoordinates n x) (binaryCoordinates n y)=physicalMatrix n x y
 change (∏i : Fin n,C (TensorWords.bitEquiv.symm (binaryCoordinates n x i))
  (TensorWords.bitEquiv.symm (binaryCoordinates n y i)))=∏i : Fin n,C (coordinates n x i) (coordinates n y i)
 simp only [binaryCoordinates,Equiv.trans_apply,Equiv.piCongrRight_apply,Pi.map_apply,bitTransport]

/-- Numerical little-endian padding tensor, suitable for the real SAME-q
unit-direction RAM loop and any dirty input array. -/
theorem native_unitColumns (q n : ℕ) :
 nativeWordMatrix (unitColumns q n)=physicalMatrix (q*n) := by
 unfold nativeWordMatrix
 rw [unitColumns_matrix]
 exact native_unitAxes (q*n)

/-- High spectator slices are preserved by the complete SAME-q unit loop. -/
theorem native_unitColumns_spectator (q n rest : ℕ)
 (X : Fin (2^(q*n+rest))→ℂ) (s : Fin (2^rest)) (z : Fin (2^(q*n))) :
 (UniformNativeCopiedInverse.spectatorMatrix (q*n) rest
  (nativeWordMatrix (unitColumns q n))).mulVec X
  ((UniformNativeCopiedInverse.spectatorSplit (q*n) rest).symm (s,z))=
 (physicalMatrix (q*n)).mulVec (fun y =>
  X ((UniformNativeCopiedInverse.spectatorSplit (q*n) rest).symm (s,y))) z := by
 rw [native_unitColumns,UniformNativeResidualSemantics.spectator_array]


end
end ExactFourierCircuits.UniformNativeUnitColumns
