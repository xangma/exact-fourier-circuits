import DFTModelSavingNativeDirectionTyped
import DFTModelSavingResidualPaired
import DFTModelSavingResidualNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry (partition)
open DFTModelSavingResidualAction
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelSavingResidualBatch.program DFTModelResidualClosedRole.gather

/-- Finite flat reads preserve the exact paired child Scalars. -/
theorem paired_flat {q groups D : ℕ} {I : ℂ} {h : Handler Port}
  {input input0 : Fin groups→Fin UniformRecursiveSelfCallMachine.W→Fin (2^q)→Scalar}
  {u u0 : State}
  (bank : DFTModelSavingResidualNativeGroup.PairBank q groups D groups I h input input0 u u0)
  (g : Fin groups) (j : Fin (UniformRecursiveSelfCallMachine.W*2^q)) :
  (h ((q,I),DFTModelRecursiveScalarSource.paired (input g) (input0 g))).val.look j.val Tagged.blank=
    encodePaired ((u.scalarHeap (D+g.val*(UniformRecursiveSelfCallMachine.W*2^q)+j.val)).getD Scalar.zero)
      ((u0.scalarHeap (D+g.val*(UniformRecursiveSelfCallMachine.W*2^q)+j.val)).getD Scalar.zero) := by
  let ij := (finProdFinEquiv : Fin UniformRecursiveSelfCallMachine.W×Fin (2^q)≃
    Fin (UniformRecursiveSelfCallMachine.W*2^q)).symm j
  have value : j.val=ij.1.val*2^q+ij.2.val := by
    have back := congrArg Fin.val ((finProdFinEquiv : Fin UniformRecursiveSelfCallMachine.W×Fin (2^q)≃
      Fin (UniformRecursiveSelfCallMachine.W*2^q)).apply_symm_apply j)
    have flat := UniformRecursiveResidualFiberValues.representative_value_generic
      UniformRecursiveSelfCallMachine.W (2^q) (UniformRecursiveSelfCallMachine.W*2^q) rfl ij.1 ij.2
    change (finProdFinEquiv (ij.1,ij.2)).val=ij.1.val*2^q+ij.2.val at flat
    exact back.symm.trans flat
  simpa only [value,Nat.add_assoc] using bank.paired g g.isLt ij.1 ij.2

/-- The actual complete-W call output is the physical completed child bank. -/
theorem returned_paired {R : ℕ} (h : Handler Port) (q w r D k : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (raw : Tape ℕ) (a : Fin R) (I : ℂ) (inverse : Bool)
  (X X0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) (qp : 1≤q)
  (source : ∀i:Fin (w+1),raw.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i:Fin (w+1),i.val<p.val→v i=0)
  (fits : ExplicitSeedBudget.roleBits≤q*w+r) (u u0 : State)
  (bank : DFTModelSavingResidualNativeGroup.PairBank q (BG.groupCount q w r) D (BG.groupCount q w r) I h
    (FV.input q w r fits v p hp (X a)) (FV.input q w r fits v p hp (X0 a)) u u0)
  (j : Fin (2^(q*(w+1)+r))) :
  (returned h ((q,(w+1,(r,raw))),
    (a.val,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),DFTModelRecursiveScalarSource.paired X X0))))).look
      j.val Tagged.blank=encodePaired ((u.scalarHeap (D+j.val)).getD Scalar.zero)
        ((u0.scalarHeap (D+j.val)).getD Scalar.zero) := by
  obtain ⟨len,_⟩:=DFTModelSavingResidualNativeGroup.gather_first q w r a.val v raw
    (DFTModelRecursiveScalarSource.paired X X0) qp source p hp before
  have widthEq : UniformBatching.width=BG.W :=
    UniformBatching.width_eq_pow.trans UniformRecursiveBatchGroupMachine.W_eq.symm
  rw [returned,args_value,len,(partition q w r fits).1,
    DFTModelSavingResidualBatch.lookup Params Tagged h (q,I) _ _ _
      ⟨j.val,by rw [(partition q w r fits).2];exact j.isLt⟩]
  simp only [widthEq] at *
  have extent : j.val<(BG.groupCount q w r)*(BG.W*2^q) := by
    rw [UniformRecursiveBatchGroupMachine.partition q w r fits];exact j.isLt
  let g : Fin (BG.groupCount q w r) := ⟨j.val/(BG.W*2^q),
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using extent)⟩
  let z : Fin (BG.W*2^q) := ⟨j.val%(BG.W*2^q),Nat.mod_lt _
    (Nat.mul_pos (by rw [UniformRecursiveBatchGroupMachine.W_eq];exact Nat.two_pow_pos _) (Nat.two_pow_pos _))⟩
  change (h ((q,I),DFTModelClockBatch.sliced (BG.W*2^q) g.val
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,raw))),
      (a.val,DFTModelRecursiveScalarSource.paired X X0))).val.2.2 Tagged.blank)).val.look z.val Tagged.blank=_
  rw [DFTModelSavingResidualNativeGroup.sliced_first q w r v raw a X X0 qp source p hp before fits g,
    paired_flat bank g z]
  have address : D+g.val*(BG.W*2^q)+z.val=D+j.val := by
    dsimp only [g,z]
    rw [Nat.add_assoc]
    congr 1
    simpa only [Nat.mul_comm] using Nat.div_add_mod j.val (BG.W*2^q)
  rw [address]

/-- Exact paired endpoint at the shared physical least pivot. -/
theorem endpoint_paired {R : ℕ} (h : Handler Port) (q w r D k : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (raw : Tape ℕ) (a : Fin R) (I : ℂ) (inverse : Bool)
  (X X0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) (qp : 1≤q)
  (source : ∀i:Fin (w+1),raw.look i.val 0=(v i).val) (hv : BinaryFrames.dot v v=1)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i:Fin (w+1),i.val<p.val→v i=0)
  (fits : ExplicitSeedBudget.roleBits≤q*w+r) (u u0 : State)
  (bank : DFTModelSavingResidualNativeGroup.PairBank q (BG.groupCount q w r) D (BG.groupCount q w r) I h
    (FV.input q w r fits v p hp (X a)) (FV.input q w r fits v p hp (X0 a)) u u0)
  (j : Fin (2^(q*(w+1)+r))) :
  (Code.run DFTModelSavingResidual.program h ((q,(w+1,(r,raw))),
    (a.val,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),DFTModelRecursiveScalarSource.paired X X0))))).val.2.look
      (a.val*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank=
    encodePaired
      ((u.scalarHeap (D+effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val)).getD Scalar.zero)
      ((u0.scalarHeap (D+effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val)).getD Scalar.zero) := by
  have room : a.val*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤(DFTModelRecursiveScalarSource.paired X X0).len := by
    change a.val*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤R*2^(q*(w+1)+r)
    calc
      _=(a.val+1)*2^(q*(w+1)+r) := by ring
      _≤R*2^(q*(w+1)+r) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt a.isLt)
  obtain ⟨_,inside,_⟩:=endpoint_first h q w r v raw a.val k I inverse
    (DFTModelRecursiveScalarSource.paired X X0) qp source hv fits room p hp before
  rw [inside j]
  exact returned_paired h q w r D k v raw a I inverse X X0 qp source p hp before fits u u0 bank
    ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val,
      effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt⟩

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
