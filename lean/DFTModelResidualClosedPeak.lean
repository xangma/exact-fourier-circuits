import DFTModelResidualClosedBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualClosedAddresses
noncomputable section
attribute [local irreducible] DFTModelResidualClosedBasis.parameters
  DFTModelResidualBasisImages.program DFTModelResidualTable.program
  DFTModelResidualAddresses.program DFTModelResidualCore.power

def budget (q m r:ℕ) : ℕ :=
  (2^m+m+2)+(2^(q*m+r)+(q*m+r)*(m+2)+2*m+2)+
  (2^q*2^q+2^q+2)+(q*m+r+m+r+2^q+2)+
  (2^(q*(m+r))+2^q*2^q+(m+r)+2^(q*m+r)+2)

theorem basis_peak_bound (z:DFTModelResidualClosedBasis.Meta.T) (b c:ℕ)
    (pc:(run DFTModelResidualClosedBasis.parameters z).peak ≤ b)
    (ic:(run DFTModelResidualBasisImages.program
      (run DFTModelResidualClosedBasis.parameters z).val).peak ≤ c) :
    (run basis z).peak ≤ b+c := by
  change max (max (run DFTModelResidualClosedBasis.parameters z).peak
    (max (max 0 (run DFTModelResidualBasisImages.program
      (run DFTModelResidualClosedBasis.parameters z).val).peak) 0)) 0 ≤ _
  omega

theorem table_peak_bound (z:DFTModelResidualClosedBasis.Meta.T) (b c:ℕ)
    (bc:(run basis z).peak ≤ b)
    (tc:(run DFTModelResidualTable.program (run basis z).val.1.1).peak ≤ c) :
    (run table z).peak ≤ b+c := by
  change max (max (run basis z).peak
    (max (max 0 (max (max 0 (run DFTModelResidualTable.program
      (run basis z).val.1.1).peak) 0)) 0)) 0 ≤ _
  omega

theorem program_peak_bound (z:DFTModelResidualClosedBasis.Meta.T) (b c d:ℕ)
    (tc:(run table z).peak ≤ b)
    (fc:(run format (run table z).val).peak ≤ c)
    (ac:(run DFTModelResidualAddresses.program (run format (run table z).val).val).peak ≤ d) :
    (run program z).peak ≤ b+c+d := by
  change max (max (run table z).peak
    (max (max (run format (run table z).val).peak
      (run DFTModelResidualAddresses.program (run format (run table z).val).val).peak) 0)) 0 ≤ _
  omega

theorem program_peak (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1))) (p:Fin (w+1)) (hp:v p=1)
    (raw:Tape ℕ) (qp:1 ≤ q)
    (prepared:(run DFTModelResidualClosedBasis.parameters (q,(w+1,(r,raw)))).val=
      (q,(w+1,(r,((UniformBinaryXorCoordinates.encode v).val,p.val)))))
    (binary:∀i,i<w+1 → raw.look i 0<2) :
    (run program (q,(w+1,(r,raw)))).peak ≤ budget q (w+1) r := by
  let z:=(q,(w+1,(r,raw)))
  let a:=(UniformBinaryXorCoordinates.encode v).val
  let k:=q*(w+1)+r
  let images:=(run DFTModelResidualBasisImages.program (q,(w+1,(r,(a,p.val))))).val
  have pc:=DFTModelResidualClosedBasis.parameters_peak q (w+1) r raw binary
  have ic:(run DFTModelResidualBasisImages.program
      (run DFTModelResidualClosedBasis.parameters z).val).peak ≤ 2^k+k*(w+3)+2*(w+1)+2 := by
    rw [prepared]
    have h:=DFTModelResidualBasisBounds.program_peak q w r v p hp
    have pp:=p.isLt
    dsimp only [k]
    omega
  have bc:=basis_peak_bound z _ _ pc ic
  have tc:(run DFTModelResidualTable.program (run basis z).val.1.1).peak ≤ 2^q*2^q+2^q+2 := by
    rw [basis_value,prepared]
    exact DFTModelResidualTable.program_peak q
  have tb:=table_peak_bound z _ _ bc tc
  have imageBank:=DFTModelResidualBasisGeometry.program_images q w r v p hp
  have cover:k ≤ q*((w+1)+r):=by dsimp [k];nlinarith
  have small:∀i,i<k → images.look i 0<2^(q*((w+1)+r)) := by
    intro i hi
    rw [imageBank ⟨i,hi⟩]
    exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) cover)
  have ac:=DFTModelResidualPeakAddresses.program_peak q ((w+1)+r) k images small
  have fc:(run format (run table z).val).peak ≤ k+(w+1)+r+2^q+2 := by
    rw [table_value,basis_value,prepared]
    exact DFTModelResidualClosedBounds.format_peak q (w+1) r a p.val images
      (run DFTModelResidualTable.program q).val
  have ad:(run DFTModelResidualAddresses.program (run format (run table z).val).val).peak ≤
      2^(q*((w+1)+r))+2^q*2^q+((w+1)+r)+2^k+2 := by
    rw [table_value,basis_value,prepared,format_value]
    exact ac
  have result:=program_peak_bound z _ _ _ tb fc ad
  change (run program z).peak ≤ _
  dsimp only [k] at result
  unfold budget
  simpa only [Nat.add_assoc,Nat.reduceAdd] using result

end
end ExactFourierCircuits.DFTModelResidualClosedPeak
