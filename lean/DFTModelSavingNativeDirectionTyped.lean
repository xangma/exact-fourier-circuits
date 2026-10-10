import DFTModelSavingNativeDirectionPairChildren
import DFTModelSavingResidualGeometry
import DFTModelSavingResidualNativeGroupSlice

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelResidualClosedBasis (Meta)
open DFTModelSavingResidualGeometry (partition)
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelResidualClosedRole.gather DFTModelResidualClosedRole.scatter
  DFTModelSavingResidualSetup.program DFTModelSavingResidualSetup.initial

/-- The genuine typed basis producer uses exactly the physical least pivot. -/
theorem endpoint_first (h:Handler Port) (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1)))
  (bits:Tape ℕ) (a k:ℕ) (I:ℂ) (inverse:Bool) (old:Tape Tagged.T) (qp:1≤q)
  (source:∀i:Fin (w+1),bits.look i.val 0=(v i).val) (hv:BinaryFrames.dot v v=1)
  (fits:UniformBatching.roleBits≤q*w+r)
  (room:a*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤old.len)
  (p:Fin (w+1)) (hp:v p=1) (before:∀i:Fin (w+1),i.val<p.val→v i=0) :
    (∀j:Fin (2^(q*(w+1)+r)),
      (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2.look j.val Tagged.blank=
        old.look (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank) ∧
    (∀j:Fin (2^(q*(w+1)+r)),
      (Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
          (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank=
      (returned h ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).look
        (if UniformResidualFibers.inverseOrientation v inverse then DFTModelSavingResidualFlip.index (2^q) j.val else j.val) Tagged.blank) ∧
    (∀j:Fin old.len,¬(a*2^(q*(w+1)+r)≤j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r))→
      (Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look j.val Tagged.blank=
        old.look j.val Tagged.blank) := by
  have nz:v≠0:=by intro z;rw [z] at hv;simp [BinaryFrames.dot] at hv
  let ctx:Meta.T:=(q,(w+1,(r,bits)))
  let x:Input.T:=(ctx,(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))
  let next:=returned h x
  have orient:=DFTModelSavingResidualOrientation.source_value v bits source hv inverse
  let flipped:=(run (DFTModelSavingResidualFlip.program Tagged)
    (2^q,(UniformResidualOrientationArithmetic.boolCode (UniformResidualFibers.inverseOrientation v inverse),next))).val
  obtain ⟨addressLength,table⟩:=DFTModelSavingResidualNativeGroup.addresses_first q w r v bits qp source p hp before
  have inside:=DFTModelResidualClosedRole.scatter_permutation Tagged ctx a (2^(q*(w+1)+r)) old
    (run DFTModelResidualClosedAddresses.program ctx).val flipped
    (DFTModelResidualBasisGeometry.permutation q w r v p hp) addressLength table room
  have outside:∀j:Fin old.len,¬(a*2^(q*(w+1)+r)≤j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r))→
    (run (DFTModelResidualClosedRole.scatter Tagged)
      ((ctx,(a,old)),((run DFTModelResidualClosedAddresses.program ctx).val,flipped))).val.look j.val Tagged.blank=old.look j.val Tagged.blank:=by
    intro j hj
    apply DFTModelResidualClosedRole.scatter_outside
    rwa [addressLength]
  have final:(Code.run DFTModelSavingResidual.program h x).val.2=
    (run (DFTModelResidualClosedRole.scatter Tagged)
      ((ctx,(a,old)),((run DFTModelResidualClosedAddresses.program ctx).val,flipped))).val := by
    rw [DFTModelSavingResidual.value,DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
      DFTModelSavingResidualSetup.initial_value,DFTModelSavingResidualFinish.value]
    dsimp only [ctx,x,next,flipped]
    rw [orient,DFTModelResidualClosedRole.gather_value]
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [DFTModelResidualClosedRole.gathered_lookup Tagged _ a old _ addressLength j
      (by rw [table j];exact Fin.isLt _),table j]
  · intro j
    change (Code.run DFTModelSavingResidual.program h x).val.2.look _ _=_
    rw [final,inside]
    dsimp only [flipped]
    have len:next.len=2^(q*(w+1)+r):=by
      dsimp only [next,x,ctx]
      rw [returned,DFTModelSavingResidualBatch.length,args_value]
      obtain ⟨_,_,_,_,gl,_⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v bits a old qp source nz
      rw [gl,(partition q w r fits).1]
      exact (partition q w r fits).2
    rw [DFTModelSavingResidualFlip.lookup Tagged _ _ next ⟨j.val,by rw [len];exact j.isLt⟩]
    cases UniformResidualFibers.inverseOrientation v inverse <;>rfl
  · intro j hj
    change (Code.run DFTModelSavingResidual.program h x).val.2.look _ _=_
    rw [final]
    exact outside j hj


end
end ExactFourierCircuits.DFTModelSavingNativeDirection
