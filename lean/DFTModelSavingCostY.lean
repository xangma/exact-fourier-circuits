import DFTModelSavingShape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelSavingY.body DFTModelSavingY.program
  DFTModelRecursiveYDirection.program DFTModelResidualTable.program

theorem y_body_work (R r k i : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v0 v : Tape Tagged.T) :
    (run (DFTModelSavingY.body R) (DFTModelSavingY.rowInput r k i I raw v0 v)).work≤
      (run DFTModelResidualTable.program (raw.look 1 0)).work+8*(raw.look 1 0)+
        73*(raw.look 1 0*raw.look 2 0)+
        (120*(raw.look 2 0+r)+154)*v.len+188 := by
  have cost:=DFTModelRecursiveYDirection.program_work R (raw.look 1 0) (raw.look 2 0) r
    (8+(raw.look 2 0+1)*i) k I raw v
  rw [DFTModelSavingY.body,DFTModelRecursiveScalarCore.comp_run,DFTModelSavingY.arguments_run]
  dsimp only [Bill.pass,Bill.pay]
  omega

def yAllowance (r : ℕ) (raw : Tape ℕ) (L : ℕ) : ℕ :=
  (run DFTModelResidualTable.program (raw.look 1 0)).work+8*(raw.look 1 0)+
    73*(raw.look 1 0*raw.look 2 0)+(120*(raw.look 2 0+r)+154)*L+189

theorem y_steps_work (R r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape Tagged.T) (n : ℕ) :
    (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).work≤
      1+yAllowance r raw v.len*n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have shape:=DFTModelSavingShape.steps_preserves ((k,I),v)
      (fun i old=>run (DFTModelSavingY.body R) (DFTModelSavingY.input r k I raw v,(i,old)))
      (fun _ _=>DFTModelSavingShape.y_body_preserves R _) n
    have same : (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).val=
        ((k,I),(DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).val.2) :=
      Prod.ext shape.1 rfl
    change (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).work+
      (run (DFTModelSavingY.body R) (DFTModelSavingY.input r k I raw v,
        (n,(DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).val))).work+1≤_
    rw [same]
    have cost:=y_body_work R r k n I raw v
      (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).val.2
    have len : (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) n).val.2.len=v.len := shape.2
    rw [len] at cost
    change _≤_ at cost
    dsimp only [DFTModelSavingY.rowInput] at cost
    rw [Nat.mul_add,Nat.mul_one]
    dsimp only [yAllowance] at *
    omega

/-- Runtime raw Y directions are read and executed in their actual order.
The bound uses bank length, with no canonical flags or supplied action. -/
theorem y_work (R r k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (DFTModelSavingY.program R) (DFTModelSavingY.input r k I raw v)).work≤
      12+yAllowance r raw v.len*(raw.look 6 0) := by
  rw [DFTModelSavingY.program_run]
  have cost:=y_steps_work R r k I raw v (raw.look 6 0)
  change (DFTModelSavingY.steps R (DFTModelSavingY.input r k I raw v) (raw.look 6 0)).work+11≤_
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
