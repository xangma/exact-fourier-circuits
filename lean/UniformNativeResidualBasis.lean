import UniformNativeCopiedInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeResidualBasis
open OAI.ExactFourier BinaryFrames BinaryTensor DirectionalWords UniformResidualFibers
open UniformFixedNetwork FrameSpectrum FrameWords
open scoped BigOperators
noncomputable section

lemma binaryAction_injective (n : ℕ) : Function.Injective
 (FrameWords.binaryAction (n:=n)) := by
 intro M N h
 apply (Matrix.reindexAlgEquiv ℂ ℂ (addresses n).symm).injective
 apply Matrix.mulVec_injective
 exact congrArg (fun F => fun X => F X) h

/-- The real descriptor visits original basis vectors in ascending order.
Each vector's grouped call combines all columns before the next basis vector. -/
def basisWord (q : ℕ) {n : ℕ} {A B : FramedScheduleWords.Label n}
 (e : FramedScheduleWords.NestedEdge A B) : List (WordStep C (2^(q*n))) :=
 ((List.finRange e.dimension).map (fun k =>
  signedColumnWord q (edgeVectors e k) (edgeVector_norm e k) (edgeInverse e))).flatten

lemma groups_character {n d : ℕ} (q : ℕ) (v : Fin d→Bits n)
 (hv : ∀k,dot (v k) (v k)=1) (decreasing : Bool) (L : List (Fin d))
 (ξ : Bits (q*n)) :
 binaryAction (wordMatrix ((L.map (fun k => signedColumnWord q (v k) (hv k) decreasing)).flatten))
  (character ξ)=
 phase ((L.map (fun k => ∑c : Fin q,
  edgeSign decreasing*weightModFour (copyVector q (v k) c)*
   (bit (dot (copyVector q (v k) c) ξ) : ZMod 4))).sum) • character ξ := by
 induction L with
 | nil => simp only [List.map_nil,List.flatten_nil,List.sum_nil,wordMatrix,List.reverse_nil,List.prod_nil,binaryAction_one,
     LinearMap.id_apply,phase_zero,one_smul]
 | cons k L ih =>
  simp only [List.map_cons,List.flatten_cons,TypedKernelWords.wordMatrix_append,binaryAction_mul,
    LinearMap.comp_apply]
  rw [signedColumnWord,FrameWords.signedFrameList_action,
    signedWord_character (fun c => copyVector q (v k) c) decreasing
     (copyVector_norm q (v k) (hv k))]
  rw [Finset.sum_map_toList,map_smul,ih]
  simp only [List.sum_cons,phase_add,smul_smul]

/-- Equality of the actual basis-major grouped chronology and the existing
column-major literal signed frame. Walsh characters establish equality for
all arrays, so no commutation or projection premise is supplied. -/
theorem basisWord_matrix (q : ℕ) {n : ℕ} {A B : FramedScheduleWords.Label n}
 (e : FramedScheduleWords.NestedEdge A B) :
 wordMatrix (basisWord q e)=wordMatrix
  (FrameWords.signedFrameList (edgeVectors (ColumnSchedule.edgeColumns q e))
   (fun j => edgeVector_norm (ColumnSchedule.edgeColumns q e) j)
   (edgeInverse (ColumnSchedule.edgeColumns q e)) Finset.univ.toList) := by
 apply binaryAction_injective (q*n)
 apply operator_eq_of_characters
 intro ξ
 rw [basisWord,groups_character,FrameWords.signedFrameList_action,
   signedWord_character (edgeVectors (ColumnSchedule.edgeColumns q e))
    (edgeInverse (ColumnSchedule.edgeColumns q e))
    (fun j => edgeVector_norm (ColumnSchedule.edgeColumns q e) j),
   Finset.sum_map_toList,copied_edge_inverse]
 rw [←Fin.sum_univ_def]
 let idx : Fin q×Fin e.dimension ≃ Fin (ColumnSchedule.edgeColumns q e).dimension :=
  finProdFinEquiv.trans (finCongr (ColumnSchedule.edgeColumns_dimension q e).symm)
 rw [←idx.sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
 congr 2
 apply Finset.sum_congr rfl
 intro c hc
 apply Finset.sum_congr rfl
 intro k hk
 have vec := copied_edge_vector q e c k
 change edgeVectors (ColumnSchedule.edgeColumns q e)
  (Fin.cast (ColumnSchedule.edgeColumns_dimension q e).symm (finProdFinEquiv (c,k))) = _ at vec
 change edgeSign (edgeInverse e)*weightModFour (copyVector q (edgeVectors e k) c)*
   (bit (dot (copyVector q (edgeVectors e k) c) ξ) : ZMod 4)=
  edgeSign (edgeInverse e)*weightModFour
   (edgeVectors (ColumnSchedule.edgeColumns q e)
    (Fin.cast (ColumnSchedule.edgeColumns_dimension q e).symm (finProdFinEquiv (c,k))))*
   (bit (dot (edgeVectors (ColumnSchedule.edgeColumns q e)
    (Fin.cast (ColumnSchedule.edgeColumns_dimension q e).symm (finProdFinEquiv (c,k)))) ξ) : ZMod 4)
 rw [vec,←copyVector_edge]

/-- The grouped residuals are precisely the macro's actual role-local edge
word, including geometric inverse and all signed weight-three phases. -/
theorem role_basisWord_matrix (q : ℕ) {R n : ℕ}
 {A B : FramedScheduleWords.Label n} (role : Fin R)
 (e : FramedScheduleWords.NestedEdge A B) :
 wordMatrix (RoleFrameWords.roleWord role (basisWord q e))=
 wordMatrix ((ColumnSchedule.edgeColumns q e).word role) := by
 rw [RoleFrameWords.roleWord_matrix,basisWord_matrix]
 cases e <;> simp only [ColumnSchedule.edgeColumns,FramedScheduleWords.NestedEdge.word,
  RoleFrameWords.roleFrameList,RoleFrameWords.roleWord_matrix,edgeVectors,edgeInverse] <;> rfl

end
end ExactFourierCircuits.UniformNativeResidualBasis
