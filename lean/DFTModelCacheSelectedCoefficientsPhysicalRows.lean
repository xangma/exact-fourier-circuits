import DFTModelCacheSelectedCoefficientsProduced
import UniformSixCInverseMatchingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] program produced

/-- Value-level encoding of an already published physical three-word row bank.
The theorem below does not supply its production for free. -/
def physicalRows (rs : List UniformInPlaceMachine.Row) : Tape Row.T :=
  Tape.tab rs.length (fun j=>let q:=rs[j]?.getD ⟨0,0,0⟩; (q.dst,(q.src,q.coefficient)))

theorem physicalRows_lookup (rs : List UniformInPlaceMachine.Row) (i : Fin rs.length) :
    (physicalRows rs).look i.val Row.blank=(rs[i.val].dst,(rs[i.val].src,rs[i.val].coefficient)) := by
  unfold physicalRows
  rw [tab_lookup rs.length _ i.val Row.blank i.isLt]
  simp only [List.getElem?_eq_getElem i.isLt,Option.getD_some]

/-- A genuine native selected mapped table determines every input address. -/
theorem mapped_rows_source {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
    (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a≤p.radix)
    (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ) :
    RowSource C T P
      (physicalRows (UniformChunkMatchingPreparation.mappedRows p fit W
        (UniformCrossShearTableMachine.locations R C T P)))
      (fun i:Fin (UniformChunkMatchingPreparation.indices p W).length=>
        UniformPackedMatchingShearMachine.selectedLabels p W i.val) := by
  have len:=UniformPackedMatchingShearMachine.mappedRows_length p fit W
    (UniformCrossShearTableMachine.locations R C T P)
  refine ⟨len,?_⟩
  intro i
  have hi:i.val<(UniformChunkMatchingPreparation.mappedRows p fit W
      (UniformCrossShearTableMachine.locations R C T P)).length:=len.symm ▸ i.isLt
  rw [physicalRows_lookup _ ⟨i.val,hi⟩]
  exact UniformPackedMatchingShearMachine.mappedRows_reference p fit W C T P i.val hi

/-- The actual inverse36 output has reversed labels with the signed inverse
policy. The forward-only pointer policy is never applied to -1/N here. -/
theorem inverse_rows_source {R : ℕ} (K C T P : ℕ)
    (W:List (UniformReplayPrint.ShearCode ℕ R))
    (good:∀q∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf K q.coefficient)
    (below:C+R≤P) :
    RowSource C T P
      (physicalRows (UniformInverseShearTableMachine.inverseRows C T P
        (UniformSixCInverseMatchingPreparation.forwardRows C T P W)))
      (fun i:Fin W.length=>UniformSixCInverseMatchingPreparation.inverseLabels W i.val) := by
  have len:(UniformInverseShearTableMachine.inverseRows C T P
      (UniformSixCInverseMatchingPreparation.forwardRows C T P W)).length=W.length := by
    rw [UniformInverseShearTableMachine.inverseRows_length,UniformSixCInverseMatchingPreparation.forwardRows_length]
  refine ⟨len,?_⟩
  intro i
  have hi:i.val<(UniformInverseShearTableMachine.inverseRows C T P
      (UniformSixCInverseMatchingPreparation.forwardRows C T P W)).length:=len.symm ▸ i.isLt
  rw [physicalRows_lookup _ ⟨i.val,hi⟩]
  exact UniformSixCInverseMatchingPreparation.inverseRows_reference K C T P W good below i

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
