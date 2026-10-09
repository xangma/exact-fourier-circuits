import UniformRecursiveResidualDirectionLoop
import UniformRecursivePaddingControl
import UniformNativeUnitColumns
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingUnitEdge
open BinaryFrames BinaryResiduals FramedScheduleWords Module
open UniformFixedNetwork UniformFixedNetworkScheduleMachine
noncomputable section

def bottomLabel (m:ℕ) : Label m :=
 ⟨⊥,0,Basis.empty (ι:=Fin 0) (↥(⊥:Submodule F2 (Vec (Fin m)))),by intro i;exact Fin.elim0 i⟩
def topLabel (m:ℕ) : Label m := ⟨⊤,m,fullBasis,fullBasis_orthonormal⟩
lemma residual_full (m:ℕ) : residual (bottomLabel m).space (topLabel m).space=⊤ :=
 residual_of_decomposes (zero_decomposes _) nondegenerate_bot

def unitBasis (m:ℕ) : Basis (Fin m) F2 (residual (bottomLabel m).space (topLabel m).space) :=
 residualBasis ⊥ ⊤ ⊤ (zero_decomposes _) nondegenerate_bot (fullBasis (ι:=Fin m))
lemma unitBasis_value (m:ℕ) (j:Fin m) : (unitBasis m j : Vec (Fin m))=unit j := by
 exact (residualBasis_apply (⊥:Submodule F2 (Vec (Fin m))) ⊤ ⊤ (zero_decomposes _) nondegenerate_bot (fullBasis (ι:=Fin m)) j).trans (fullBasis_apply j)

abbrev unitEdge (m:ℕ) : NestedEdge (bottomLabel m) (topLabel m) :=
 .increasing bot_le m (unitBasis m) (by intro i j;change dot (unitBasis m i : Vec (Fin m)) (unitBasis m j : Vec (Fin m))=_;rw [unitBasis_value,unitBasis_value];exact dot_units i j)
lemma dimension (m:ℕ) : (unitEdge m).dimension=m := rfl
lemma vectors (m:ℕ) (j:Fin m) : edgeVectors (unitEdge m) j=unit j := unitBasis_value m j
lemma inverse (m:ℕ) : edgeInverse (unitEdge m)=false := rfl

lemma edgeBits_unit (m:ℕ) : edgeBits (unitEdge m)=
 (UniformRecursiveNodePreparation.binaryUnitRecord m).directions := by
 unfold edgeBits
 change List.ofFn (fun z:Fin (m*m)=>
  (edgeVectors (unitEdge m) ((finProdFinEquiv.symm z).1) ((finProdFinEquiv.symm z).2)).val)=_
 apply congrArg List.ofFn
 funext z
 rw [vectors]
 change (if (finProdFinEquiv.symm z).2=(finProdFinEquiv.symm z).1 then (1:ZMod 2) else 0).val=
  if z.val/m=z.val%m then 1 else 0
 have heq:(finProdFinEquiv.symm z).2=(finProdFinEquiv.symm z).1 ↔ z.val/m=z.val%m:=by
  simp only [finProdFinEquiv_symm_apply,Fin.ext_iff]
  change z.val%m=z.val/m ↔ z.val/m=z.val%m
  exact eq_comm
 by_cases h:z.val/m=z.val%m
 · rw [ite_eq_left (heq.mpr h),ite_eq_left h];rfl
 · rw [ite_eq_right (fun h'=>h (heq.mp h')),ite_eq_right h];rfl


lemma macro_unit {nRoles R:ℕ} (q m:ℕ) (emb:Fin nRoles↪Fin R) (role:Fin nRoles) :
 macroRecord q emb (.edge _ _ role (unitEdge m))=
 UniformRecursivePaddingControl.patchRecord (UniformRecursiveNodePreparation.binaryUnitRecord m) q (emb role).val := by
 change (⟨0,q,m,(emb role).val,0,0,m,0,edgeBits (unitEdge m)⟩:Record)=_
 rw [edgeBits_unit]
 rfl

lemma macro_fixed {nRoles R:ℕ} (q:ℕ) (emb:Fin nRoles↪Fin R) (role:Fin nRoles) :
 macroRecord q emb (.edge _ _ role (unitEdge ExplicitSeedBudget.m))=
 UniformRecursivePaddingControl.patchRecord UniformRecursiveSavingProgram.unitRecord q (emb role).val :=
 macro_unit q ExplicitSeedBudget.m emb role

lemma basisWord_unit (q m:ℕ) : UniformNativeResidualBasis.basisWord q (unitEdge m)=
 UniformNativeUnitColumns.unitColumns q m := by
 simp only [UniformNativeResidualBasis.basisWord,UniformNativeUnitColumns.unitColumns,
  unitEdge,FramedScheduleWords.NestedEdge.dimension,UniformFixedNetwork.edgeVectors,
  UniformFixedNetwork.edgeInverse,unitBasis_value]

lemma action_unit (q w r:ℕ) (f:Fin (2^(q*(w+1)+r))→ℂ) :
 UniformRecursiveResidualDirectionLoop.action q w r (unitEdge (w+1)) (List.finRange (w+1)) f=
 (UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformBinaryTensorCoordinates.physicalMatrix (q*(w+1)))).mulVec f := by
 have h:=UniformRecursiveResidualDirectionLoop.action_basis q w r (unitEdge (w+1)) f
 rw [basisWord_unit,UniformNativeUnitColumns.native_unitColumns] at h
 exact h
end
end ExactFourierCircuits.UniformRecursivePaddingUnitEdge
