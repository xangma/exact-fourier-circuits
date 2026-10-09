import DFTModelRecursiveYDirection
import DFTModelRecursiveYBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveYDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

attribute [local irreducible] program moved ready
  DFTModelRecursiveYMovement.program
  DFTModelRecursiveYMask.program DFTModelResidualTable.program DFTModelResidualCore.power

theorem program_peak_formula (R : ℕ) (x : Input.T) :
    (run (program R) x).peak=max (run (ready R) x).peak
      (run (DFTModelRecursiveYMovement.program DFTModelAffine.Tagged)
        (run (ready R) x).val).peak := by
  simp only [program,moved,node,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    max_zero,zero_max]

theorem program_peak {R m : ℕ} (q r A k B : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) (d : UniformNativeYRecordMachine.Direction R m)
    (positive : 0 < R) (len : v.len=R*2^k) (shape : k=q*m+r) (qp : 1 ≤ q)
    (roleSource : raw.look A 0=d.role.val)
    (bits : ∀i:Fin m,raw.look (A+1+i.val) 0=(d.vector i).val)
    (extent : R*2^k≤B) (rowEnd : A+m+1≤B)
    (padded : 2^(q*(m+r))≤B) (square : 2^q*2^q≤B) :
    (run (program R) (input q m r A k I raw v)).peak≤4*B+2 := by
  have native : k≤q*(m+r) := by nlinarith only [shape,qp]
  have maskPadded : 2^(q*m)≤B :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans padded
  have qmBound : q*m≤B := Nat.lt_two_pow_self.le.trans maskPadded
  have widthBound : m+r≤B := by
    have w : m+r≤q*(m+r) := Nat.le_mul_of_pos_left _ qp
    exact w.trans (Nat.lt_two_pow_self.le.trans padded)
  have roles : R≤B := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans extent
  have radixBound : 2^q≤B :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans square
  have small : (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val<2^k :=
    (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have maskPeak:=DFTModelRecursiveYMask.program_peak q m A raw (by
    intro i;rw [bits i];exact ZMod.val_lt _)
  have tablePeak:=DFTModelResidualTable.program_peak q
  have powerPeak:=DFTModelResidualCore.power_peak q
  have rd : (run (ready R) (input q m r A k I raw v)).peak≤4*B+2 := by
    simp only [ready,volume,width,rest,radix,role,table,mask,bank,node,columns,maskInput,
      DFTModelRecursiveYMask.columns,DFTModelRecursiveYMask.width,
      DFTModelRecursiveYMask.raw,DFTModelRecursiveYMask.base,
      input,DFTModelRecursiveYMask.input,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word]
    dsimp only [run,DFTModelRecursiveYMask.input] at maskPeak tablePeak powerPeak
    have quotientBound : v.len/R≤B := (Nat.div_le_self _ _).trans (by omega)
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega
  have rv:=ready_value R q m r A k I raw v
  have vdiv : v.len/R=2^k := by rw [len,Nat.mul_div_cancel_left _ positive]
  rw [vdiv,roleSource,DFTModelRecursiveYMask.source_value q A d.vector raw bits] at rv
  have mv:=DFTModelRecursiveYMovement.program_peak DFTModelAffine.Tagged q (m+r) k R d.role.val
    (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val B v
    len extent d.role.isLt small roles padded square widthBound native
  rw [program_peak_formula,rv]
  exact max_le rd mv

end
end ExactFourierCircuits.DFTModelRecursiveYDirection
