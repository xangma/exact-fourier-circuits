import UniformForwardMatchingFactorValues
import UniformSixCInverseMatchingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformReplayPrint
namespace F
abbrev Config:=UniformForwardMatchingFactorPreparation.Config
abbrev Layout:=UniformForwardMatchingFactorPreparation.Layout
end F
noncomputable section
variable {B:ℕ}
def reference (c:F.Config) (l:F.Layout c B) (ha he)
 (i:Fin (UniformForwardMatchingFactorPreparation.rows c l ha he).length):=
 UniformMatchingCoefficientValueBridge.selectedReference c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformForwardMatchingFactorPreparation.selectedIndex c l ha he i)
lemma reference_leaf (c:F.Config) (l:F.Layout c B) (ha he)
 (i:Fin (UniformForwardMatchingFactorPreparation.rows c l ha he).length):
 UniformMatchingCoefficientValueBridge.ForwardLeaf c.chunk.height.K (reference c l ha he i):=
 UniformMatchingCoefficientValueBridge.selectedReference_leaf c.chunk.height.K c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformMatchingCoefficientValueBridge.crossWord_leaf c.chunk ha he)
  (UniformForwardMatchingFactorPreparation.selectedIndex c l ha he i)
lemma coefficient_reference (c:F.Config) (l:F.Layout c B) (ha he)
 (i:Fin (UniformForwardMatchingFactorPreparation.rows c l ha he).length):
 UniformForwardMatchingFactorPreparation.coefficient c l ha he i=
 UniformMatchingConjugateLoadMachine.fromReference (reference c l ha he i):=by
 have hi:i.val<(UniformChunkMatchingPreparation.indices c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)).length:=by
  rw[←UniformForwardMatchingFactorPreparation.rows_length c l ha he];exact i.isLt
 simp only[UniformForwardMatchingFactorPreparation.coefficient,UniformPackedMatchingShearMachine.selectedLabels,
  dite_eq_left hi,reference,UniformMatchingCoefficientValueBridge.selectedReference,
  UniformForwardMatchingFactorPreparation.selectedIndex]
 rfl
lemma forward_pointer (c:F.Config) (l:F.Layout c B) (ha he)
 (i:Fin (UniformForwardMatchingFactorPreparation.rows c l ha he).length):
 ((UniformForwardMatchingFactorPreparation.rows c l ha he)[i.val]'i.isLt).coefficient=
 (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)
  c.chunk.height.C c.negative c.chunk.height.P).address (reference c l ha he i):=by
 rw[UniformForwardMatchingFactorPreparation.coefficient_address,coefficient_reference]
 exact (UniformMatchingConjugateLoadMachine.reference_address _ _ _ _).symm
lemma forward_domain (c:F.Config) (l:F.Layout c B) (ha he):
 ∀r∈UniformForwardMatchingFactorPreparation.rows c l ha he,
 UniformInverseShearTableMachine.Domain c.chunk.height.C c.chunk.height.P
  (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) r.coefficient:=by
 intro r hr
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hr
 rw[←eq,forward_pointer c l ha he ⟨i,hi⟩]
 exact UniformSixCInverseMatchingPreparation.forward_domain _ _ _ _ _ (reference_leaf c l ha he ⟨i,hi⟩)
def rows (c:F.Config) (l:F.Layout c B) (ha he):=
 UniformInverseShearTableMachine.inverseRows c.chunk.height.C c.negative c.chunk.height.P
  (UniformForwardMatchingFactorPreparation.rows c l ha he)
lemma rows_length (c:F.Config) (l:F.Layout c B) (ha he):
 (rows c l ha he).length=(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by
 simp only[rows,UniformInverseShearTableMachine.inverseRows_length]
def reverseIndex (c:F.Config) (l:F.Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 Fin (UniformForwardMatchingFactorPreparation.rows c l ha he).length:=
 ⟨(UniformForwardMatchingFactorPreparation.rows c l ha he).length-i.val-1,by
  have hi:i.val<(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by simpa only[rows_length] using i.isLt
  omega⟩
def coefficient (c:F.Config) (l:F.Layout c B) (ha he) (i:Fin (rows c l ha he).length):=
 UniformMatchingCoefficientValueBridge.inverseReference (reference c l ha he (reverseIndex c l ha he i))
lemma rows_get (c:F.Config) (l:F.Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 (rows c l ha he)[i.val]'i.isLt=
 UniformInverseShearTableMachine.inverseRow c.chunk.height.C c.negative c.chunk.height.P
  ((UniformForwardMatchingFactorPreparation.rows c l ha he)[(reverseIndex c l ha he i).val]):=by
 exact UniformInverseShearTableMachine.inverseRows_get _ _ _ _ _ (by simpa only[rows_length] using i.isLt)
lemma coefficient_address (c:F.Config) (l:F.Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 ((rows c l ha he)[i.val]'i.isLt).coefficient=
 UniformMatchingConjugateLoadMachine.address c.chunk.height.C c.negative c.chunk.height.P (coefficient c l ha he i):=by
 rw[rows_get]
 change UniformInverseShearTableMachine.inverseAddress _ _ _ _=_
 rw[forward_pointer]
 apply UniformSixCInverseMatchingPreparation.inverse_pointer c.chunk.height.K _ _ _ _ (reference_leaf c l ha he _)
 have a:=l.coefficient.positiveBelow;have b:=l.coefficient.negativeBelow;omega
lemma coefficient_value (c:F.Config) (l:F.Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (i:Fin (rows c l ha he).length):
 UniformMatchingConjugateLoadMachine.value c.chunk.height.K bank (coefficient c l ha he i)=
 -(reference c l ha he (reverseIndex c l ha he i)).eval bank:=by
 rw[coefficient,UniformMatchingCoefficientValueBridge.inverse_value _ _ _ (reference_leaf c l ha he _)]
 exact UniformReplayPrint.Coefficient.eval_negate _ _
lemma endpoints (c:F.Config) (l:F.Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 ((rows c l ha he)[i.val]'i.isLt).dst=
  ((UniformForwardMatchingFactorPreparation.rows c l ha he)[(reverseIndex c l ha he i).val]).dst ∧
 ((rows c l ha he)[i.val]'i.isLt).src=
  ((UniformForwardMatchingFactorPreparation.rows c l ha he)[(reverseIndex c l ha he i).val]).src:=by
 rw[rows_get];exact ⟨rfl,rfl⟩
lemma reverseIndex_injective (c:F.Config) (l:F.Layout c B) (ha he):
 Function.Injective (reverseIndex c l ha he):=by
 intro i j eq
 apply Fin.ext
 have v:=congrArg Fin.val eq
 have hi:i.val<(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by simpa only[rows_length] using i.isLt
 have hj:j.val<(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by simpa only[rows_length] using j.isLt
 simp only[reverseIndex] at v
 omega
lemma rows_geometry (c:F.Config) (l:F.Layout c B) (ha he):
 UniformGlobalMatchingPoolPreparation.Bounds c.ambient (rows c l ha he) ∧
 UniformGlobalMatchingPoolPreparation.Different (rows c l ha he) ∧
 UniformGlobalMatchingPoolPreparation.Matching (rows c l ha he):=by
 have geo:=UniformForwardMatchingFactorPreparation.rows_geometry c l ha he
 refine ⟨?_,?_,?_⟩
 · intro i;rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2];exact geo.1 _
 · intro i;rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2];exact geo.2.1 _
 · intro i j ne
   rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2,(endpoints c l ha he j).1,(endpoints c l ha he j).2]
   exact geo.2.2 _ _ (fun eq=>ne (reverseIndex_injective c l ha he eq))
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
