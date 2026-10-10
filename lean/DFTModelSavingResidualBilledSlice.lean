import DFTModelSavingResidualBilledCost
import DFTModelSavingResidualNativeGroupSlice

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine BinaryFrames DFTModelAffine DFTModelSavingResidualSetup
open DFTModelSavingResidual
open scoped BigOperators
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelResidualClosedRole.gather

/-- The actual typed child-work sum uses exactly the physical first-pivot
batches billed by the native source loop, including both returned channels. -/
theorem childrenWork_first {R : ℕ} (q w r : ℕ) (v : Vec (Fin (w+1))) (bits : Tape ℕ)
  (a : Fin R) (X X0 : Fin R → Fin (2^(q*(w+1)+r)) → Scalar) (qp : 1≤q)
  (source : ∀i : Fin (w+1),bits.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i : Fin (w+1),i.val<p.val→v i=0)
  (fits : ExplicitSeedBudget.roleBits≤q*w+r) (rawInverse k : ℕ) (I : ℂ)
  (h : Handler Port) :
  let x : Input.T:=((q,(w+1,(r,bits))),
    (a.val,(rawInverse,((k,I),DFTModelRecursiveScalarSource.paired X X0))))
  (∑g∈Finset.range (arguments x).2.1,
    (h ((arguments x).1,DFTModelClockBatch.sliced (arguments x).2.2.1 g
      (arguments x).2.2.2 Tagged.blank)).work)=
  remainingWork q I h
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X a))
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X0 a)) 0 := by
  dsimp only
  obtain ⟨length,_⟩:=gather_first q w r a.val v bits
    (DFTModelRecursiveScalarSource.paired X X0) qp source p hp before
  have width : UniformBatching.width=W := by unfold UniformBatching.width; rfl
  rw [args_value]
  change (∑g∈Finset.range ((run (DFTModelResidualClosedRole.gather Tagged)
    ((q,(w+1,(r,bits))),(a.val,DFTModelRecursiveScalarSource.paired X X0))).val.2.2.len/(UniformBatching.width*2^q)),
    (h ((q,I),DFTModelClockBatch.sliced (UniformBatching.width*2^q) g
      (run (DFTModelResidualClosedRole.gather Tagged)
        ((q,(w+1,(r,bits))),(a.val,DFTModelRecursiveScalarSource.paired X X0))).val.2.2 Tagged.blank)).work)=_
  rw [length,(DFTModelSavingResidualGeometry.partition q w r fits).1,width]
  change (∑g∈Finset.range (UniformRecursiveBatchGroupMachine.groupCount q w r),_)=_
  rw [Finset.sum_range,remainingWork_zero]
  apply Finset.sum_congr rfl
  intro g _
  rw [sliced_first q w r v bits a X X0 qp source p hp before fits g]

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup
