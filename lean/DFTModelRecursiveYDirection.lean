import DFTModelRecursiveYMask
import DFTModelRecursiveYMovement
import DFTModelClockControl
import UniformNativeYRecordMachine

set_option autoImplicit false

/-! Charged raw Y-row translation, producing one complete paired bank. This
primitive reads the role and original bits, constructs the XOR table, and
performs the readonly gather. Record-header decoding and the finite row
loop are separate callers. -/
namespace ExactFourierCircuits.DFTModelRecursiveYDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open UniformMachine
noncomputable section

abbrev Input := p DFTModelRecursiveYMask.Input (p w DFTModelClockControl.Node)
def maskInput : Prog false Input DFTModelRecursiveYMask.Input := .atom .fst
def node : Prog false Input DFTModelClockControl.Node := .comp (.atom .snd) (.atom .snd)
def bank : Prog false Input (Ty.a DFTModelAffine.Tagged) := .comp node (.atom .snd)
def columns : Prog false Input w := .comp maskInput DFTModelRecursiveYMask.columns
def width : Prog false Input w := .comp maskInput DFTModelRecursiveYMask.width
def rest : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def role : Prog false Input w := .comp (.fork
  (.comp maskInput DFTModelRecursiveYMask.raw)
  (.comp maskInput DFTModelRecursiveYMask.base)) (.atom .look)
def radix : Prog false Input w := .comp columns DFTModelResidualCore.power
def table : Prog false Input (Ty.a w) := .comp columns DFTModelResidualTable.program
def mask : Prog false Input w := .comp maskInput DFTModelRecursiveYMask.program
def volume (R : ℕ) : Prog false Input w := binary .div
  (.comp bank (.atom .len)) (.atom (.lit R))
def ready (R : ℕ) : Prog false Input (DFTModelRecursiveYMovement.Input DFTModelAffine.Tagged) :=
  .fork (.fork (volume R) (binary .add width rest))
    (.fork (.fork radix role) (.fork table (.fork mask bank)))
def moved (R : ℕ) : Prog false Input (Ty.a DFTModelAffine.Tagged) :=
  .comp (ready R) (DFTModelRecursiveYMovement.program DFTModelAffine.Tagged)
def program (R : ℕ) : Prog false Input DFTModelClockControl.Node :=
  .fork (.comp node (.atom .fst)) (moved R)

def input (q m r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) : Input.T :=
  (DFTModelRecursiveYMask.input q m A raw,(r,((k,I),v)))

attribute [local irreducible] DFTModelRecursiveYMovement.program
  DFTModelRecursiveYMask.program DFTModelResidualTable.program DFTModelResidualCore.power

theorem ready_value (R q m r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) :
    (run (ready R) (input q m r A k I raw v)).val=
      DFTModelRecursiveYMovement.input DFTModelAffine.Tagged q (m+r)
        (v.len/R) (raw.look A 0)
        (run DFTModelRecursiveYMask.program (DFTModelRecursiveYMask.input q m A raw)).val v := by
  have power:=DFTModelResidualCore.power_value q
  simp only [ready,volume,width,rest,radix,role,table,mask,bank,node,columns,maskInput,
    DFTModelRecursiveYMask.columns,DFTModelRecursiveYMask.width,
    DFTModelRecursiveYMask.raw,DFTModelRecursiveYMask.base,
    DFTModelRecursiveYMask.input,DFTModelRecursiveYMovement.input,input,
    binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  exact congrArg (fun z=>((v.len/R,m+r),((z,raw.look A 0),
    ((run DFTModelResidualTable.program q).val,
      ((run DFTModelRecursiveYMask.program (DFTModelRecursiveYMask.input q m A raw)).val,v))))) power

theorem program_value {R m : ℕ} (q r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) (d : UniformNativeYRecordMachine.Direction R m)
    (positive : 0 < R) (len : v.len=R*2^k) (shape : k=q*m+r) (qp : 1 ≤ q)
    (roleSource : raw.look A 0=d.role.val)
    (bits : ∀i:Fin m,raw.look (A+1+i.val) 0=(d.vector i).val) :
    (run (program R) (input q m r A k I raw v)).val=
      ((k,I),DFTModelRecursiveYMovement.data DFTModelAffine.Tagged (2^k) d.role.val
        (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val v) := by
  have vdiv : v.len/R=2^k := by rw [len,Nat.mul_div_cancel_left _ positive]
  have padding : k ≤ q*(m+r) := by nlinarith only [shape,qp]
  have vs : 2^k≤2^(q*(m+r)) := Nat.pow_le_pow_right (by decide) padding
  have small := (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).isLt
  have ms : (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val
      <2^(q*(m+r)) := small.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have rv:=ready_value R q m r A k I raw v
  rw [vdiv,roleSource,DFTModelRecursiveYMask.source_value q A d.vector raw bits] at rv
  have result : (run (moved R) (input q m r A k I raw v)).val=
      DFTModelRecursiveYMovement.data DFTModelAffine.Tagged (2^k) d.role.val
        (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val v := by
    change (run (DFTModelRecursiveYMovement.program DFTModelAffine.Tagged)
      (run (ready R) (input q m r A k I raw v)).val).val=_
    rw [rv]
    exact DFTModelRecursiveYMovement.program_value _ _ _ _ _ _ _ (Nat.two_pow_pos _) vs ms
  change ((k,I),(run (moved R) (input q m r A k I raw v)).val)=_
  rw [result]

theorem ready_valid (R : ℕ) (x : Input.T) : (run (ready R) x).valid := by
  have maskValid : (run mask x).valid :=
    ⟨trivial,DFTModelRecursiveYMask.program_valid x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2⟩
  have tableValid : (run table x).valid := ⟨by trivial,DFTModelResidualTable.program_valid _⟩
  have radixValid : (run radix x).valid := ⟨by trivial,DFTModelResidualCore.power_valid _⟩
  simpa only [ready,volume,width,rest,role,bank,node,columns,maskInput,
    DFTModelRecursiveYMask.columns,DFTModelRecursiveYMask.width,
    DFTModelRecursiveYMask.raw,DFTModelRecursiveYMask.base,
    binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    and_true,true_and] using ⟨radixValid,tableValid,maskValid⟩

theorem program_valid (R : ℕ) (x : Input.T) : (run (program R) x).valid := by
  have mv : (run (moved R) x).valid :=
    ⟨ready_valid R x,DFTModelRecursiveYMovement.program_valid _ _⟩
  simpa only [program,node,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    true_and,and_true] using mv

theorem ready_work (R q m r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) :
    (run (ready R) (input q m r A k I raw v)).work≤
      (run DFTModelResidualTable.program q).work+8*q+73*(q*m)+110 := by
  have maskWork:=DFTModelRecursiveYMask.program_work q m A raw
  have powerWork:=DFTModelResidualCore.power_work q
  simp only [ready,volume,width,rest,radix,role,table,mask,bank,node,columns,maskInput,
    DFTModelRecursiveYMask.columns,DFTModelRecursiveYMask.width,
    DFTModelRecursiveYMask.raw,DFTModelRecursiveYMask.base,
    input,DFTModelRecursiveYMask.input,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  dsimp only [run,DFTModelRecursiveYMask.input] at maskWork powerWork
  omega

theorem program_work (R q m r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) :
    (run (program R) (input q m r A k I raw v)).work≤
      (run DFTModelResidualTable.program q).work+8*q+73*(q*m)+
        (120*(m+r)+154)*v.len+130 := by
  have rd:=ready_work R q m r A k I raw v
  have move:=DFTModelRecursiveYMovement.program_work DFTModelAffine.Tagged q (m+r)
    (v.len/R) (raw.look A 0)
    (run DFTModelRecursiveYMask.program (DFTModelRecursiveYMask.input q m A raw)).val v
  change 5+((run (ready R) (input q m r A k I raw v)).work+
    (run (DFTModelRecursiveYMovement.program DFTModelAffine.Tagged)
      (run (ready R) (input q m r A k I raw v)).val).work+1)+1≤_
  rw [ready_value]
  omega

end
end ExactFourierCircuits.DFTModelRecursiveYDirection
