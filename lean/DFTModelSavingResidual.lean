import DFTModelSavingResidualBatch
import DFTModelSavingResidualFinish

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidual
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup
open scoped BigOperators
noncomputable section

abbrev Port := DFTModelClockBatch.Port Params Tagged

/-- Concrete residual opcode body. The only port is the same recursive child
on one complete W-array batch. Both affine channels travel in a single Tagged
element and therefore use one child invocation, not two. -/
def program : Code false Port Input Node := .comp (.importClosed DFTModelSavingResidualSetup.program)
  (.comp (.fork (.atom .id) (.comp (.importClosed batchArgs)
    (DFTModelSavingResidualBatch.program Params Tagged)))
    (.importClosed DFTModelSavingResidualFinish.program))

attribute [local irreducible] DFTModelSavingResidualSetup.program batchArgs
  DFTModelSavingResidualBatch.program DFTModelSavingResidualFinish.program

def prepared (x:Input.T) : Setup.T := (run DFTModelSavingResidualSetup.program x).val
def arguments (x:Input.T) : (DFTModelClockBatch.Input Params Tagged).T :=
  (run batchArgs (prepared x)).val
def returned (h:Handler Port) (x:Input.T) : Tape Tagged.T :=
  (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).val

theorem value (h:Handler Port) (x:Input.T) :
  (Code.run program h x).val=
    (run DFTModelSavingResidualFinish.program (prepared x,returned h x)).val := rfl

theorem work_exact (h:Handler Port) (x:Input.T) :
  (Code.run program h x).work=
    (run DFTModelSavingResidualSetup.program x).work+
    (run batchArgs (prepared x)).work+
    (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).work+
    (run DFTModelSavingResidualFinish.program (prepared x,returned h x)).work+8 := by
  simp only [program,prepared,arguments,returned,Code.run,run,Bill.pass,Bill.pay,Bill.one,Atom.run]
  omega

theorem valid (h:Handler Port) (x:Input.T)
  (children:∀g<(arguments x).2.1,
    (h ((arguments x).1,DFTModelClockBatch.sliced (arguments x).2.2.1 g
      (arguments x).2.2.2 Tagged.blank)).valid) :
  (Code.run program h x).valid := by
  have a:=DFTModelSavingResidualSetup.valid x.1 x.2.1 x.2.2.1 x.2.2.2.1.1 x.2.2.2.1.2 x.2.2.2.2
  have b: (run batchArgs (prepared x)).valid := by
    rw [DFTModelSavingResidualSetup.batchArgs_run];trivial
  have c:=DFTModelSavingResidualBatch.valid Params Tagged h (arguments x).1
    (arguments x).2.1 (arguments x).2.2.1 (arguments x).2.2.2 children
  have d:=DFTModelSavingResidualFinish.valid (prepared x).1 (prepared x).2.1 (prepared x).2.2 (returned h x)
  simpa only [program,prepared,arguments,returned,Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    and_true,true_and] using And.intro a (And.intro (And.intro b c) d)

theorem args_value (ctx:DFTModelResidualClosedBasis.Meta.T) (role raw k:ℕ)
  (I:ℂ) (old:Tape Tagged.T) :
  arguments (ctx,(role,(raw,((k,I),old))))=
    ((ctx.1,I),
      ((run (DFTModelResidualClosedRole.gather Tagged) (ctx,(role,old))).val.2.2.len/
        (UniformBatching.width*2^ctx.1),
       (UniformBatching.width*2^ctx.1,
        (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(role,old))).val.2.2))) := by
  rw [arguments,prepared,DFTModelSavingResidualSetup.value,
    DFTModelSavingResidualSetup.initial_value,DFTModelSavingResidualSetup.batchArgs_run]

end
end ExactFourierCircuits.DFTModelSavingResidual
