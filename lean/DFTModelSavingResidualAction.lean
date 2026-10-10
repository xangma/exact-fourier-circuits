import DFTModelSavingResidualChild

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualAction
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry DFTModelSavingResidualChild
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelSavingResidualBatch.program DFTModelResidualClosedRole.gather

theorem block_lt (N L j s:ℕ) (_pos:0<N) (divides:N∣L) (live:j<L) (small:s<N) :
  j/N*N+s<L := by
  obtain ⟨G,rfl⟩:=divides
  have quotient:j/N<G:=Nat.div_lt_of_lt_mul live
  have bound:=Nat.mul_le_mul_right N (show j/N+1≤G by omega)
  nlinarith

theorem size_divides (q w r:ℕ) : 2^q∣2^(q*(w+1)+r) := by
  use 2^(q*w+r)
  rw [←Nat.pow_add]
  congr 1
  ring

def effectiveIndex (N:ℕ) (inverse:Bool) (j:ℕ) : ℕ :=
  if inverse then DFTModelSavingResidualFlip.index N j else j

theorem effectiveIndex_lt (N L j : ℕ) (inverse : Bool) (pos : 0 < N)
  (divides : N ∣ L) (live : j < L) : effectiveIndex N inverse j < L := by
  cases inverse
  · exact live
  · exact DFTModelSavingResidualFlip.index_lt N L j pos divides live

/-- Native per-direction action of the same open syntax. Only the internal
smaller-child C^q induction property is used. Raw direction bits generate the
basis, addresses and orientation; every unrelated complete Tagged cell stays
unchanged. The two returned coordinates are the actual zero-source baseline
and its homogeneous difference, respectively. -/
theorem channels (h:Handler Port) (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1)))
  (bits:Tape ℕ) (a k:ℕ) (I:ℂ) (inverse:Bool) (old:Tape Tagged.T) (qp:1≤q)
  (source:∀i:Fin (w+1),bits.look i.val 0=(v i).val) (hv:BinaryFrames.dot v v=1)
  (fits:UniformBatching.roleBits≤q*w+r)
  (room:a*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤old.len)
  (ih:Channels h q I (2^(q*w+r-UniformBatching.roleBits))
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2) :
  ∃p:Fin (w+1),∃hp:v p=1,
    (∀j:Fin (2^(q*(w+1)+r)),
      ((Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
          (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank).2=
      ((UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
        (fun s=>old.look (a*2^(q*(w+1)+r)+
          (DFTModelResidualBasisGeometry.permutation q w r v p hp
            ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val/2^q*2^q+s.val,
             block_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r)
              (effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt) s.isLt⟩).val) Tagged.blank |>.2.1)
        ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
       (UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
        (fun s=>old.look (a*2^(q*(w+1)+r)+
          (DFTModelResidualBasisGeometry.permutation q w r v p hp
            ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val/2^q*2^q+s.val,
             block_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r)
              (effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt) s.isLt⟩).val) Tagged.blank |>.2.2)
        ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩)) ∧
    (∀j:Fin old.len,¬(a*2^(q*(w+1)+r)≤j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r))→
      (Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look j.val Tagged.blank=
        old.look j.val Tagged.blank) := by
  obtain ⟨p,hp,gather,inside,outside⟩:=endpoint h q w r v bits a k I inverse old qp source hv fits room
  have nz:v≠0:=by intro z;rw [z] at hv;simp [BinaryFrames.dot] at hv
  obtain ⟨_,count,chunk,len⟩:=source_arguments q w r v bits a
    (UniformResidualOrientationArithmetic.boolCode inverse) k I old qp source nz fits
  refine ⟨p,hp,?_,outside⟩
  intro j
  rw [inside j]
  let index:=effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val
  have live:index<2^(q*(w+1)+r):=
    effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt
  change ((returned h _).look index Tagged.blank).2=_
  rw [args_value] at len
  change (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2.len=2^(q*(w+1)+r) at len
  rw [returned,args_value,len,(partition q w r fits).1]
  have result:=batch_channels h q I (2^(q*w+r-UniformBatching.roleBits))
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2 ih
    ⟨index,by rw [(partition q w r fits).2];exact live⟩
  rw [result]
  have data:∀s:Fin (2^q),
    ((run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2.look
      (index/2^q*2^q+s.val) Tagged.blank)=
    old.look (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp
      ⟨index/2^q*2^q+s.val,block_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) live s.isLt⟩).val) Tagged.blank:=by
    intro s
    exact gather ⟨_,block_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) live s.isLt⟩
  simp only [data]
  rfl

end
end ExactFourierCircuits.DFTModelSavingResidualAction
