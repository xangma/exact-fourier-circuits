import DFTModelSavingResidualSetup
import DFTModelSavingResidualFlip

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualFinish
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup
noncomputable section

abbrev Input := p Setup (Ty.a Tagged)
def context : Prog false Input (DFTModelResidualClosedRoleStages.Context Tagged) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
def flipArgs : Prog false Input (DFTModelSavingResidualFlip.Input Tagged) := .fork
  (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))) (.atom .snd))
def scatterArgs : Prog false Input (DFTModelResidualClosedRoleStages.Context Tagged) := .fork
  (.comp context (.atom .fst))
  (.fork (.comp context (.comp (.atom .snd) (.atom .fst)))
    (.comp flipArgs (DFTModelSavingResidualFlip.program Tagged)))
def originalParams : Prog false Input Params := .comp (.atom .fst)
  (.comp (.atom .fst) (.comp (.atom .fst) (.comp node (.atom .fst))))
def program : Prog false Input Node := .fork originalParams
  (.comp scatterArgs (DFTModelResidualClosedRole.scatter Tagged))

attribute [local irreducible] DFTModelSavingResidualFlip.program DFTModelResidualClosedRole.scatter

theorem flipArgs_run (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  run flipArgs ((f,(N,T)),child)=⟨(N,(f.2.1,child)),15,0,True⟩ := by
  simp [flipArgs,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem scatterArgs_value (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  (run scatterArgs ((f,(N,T)),child)).val=
    (f.2.2.1,(f.2.2.2.1,(run (DFTModelSavingResidualFlip.program Tagged) (N,(f.2.1,child))).val)) := rfl

theorem value (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  (run program ((f,(N,T)),child)).val=
    (f.1.2.2.2.1,(run (DFTModelResidualClosedRole.scatter Tagged)
      (f.2.2.1,(f.2.2.2.1,(run (DFTModelSavingResidualFlip.program Tagged) (N,(f.2.1,child))).val))).val) := rfl

theorem length (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  (run program ((f,(N,T)),child)).val.2.len=f.2.2.1.2.2.len := by
  rw [value,DFTModelResidualClosedRole.scatter_len]

theorem work (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  (run program ((f,(N,T)),child)).work≤
    45*child.len+18*f.2.2.2.1.len+104*f.2.2.1.2.2.len+90 := by
  have fw:=DFTModelSavingResidualFlip.work Tagged N f.2.1 child
  have sw:=DFTModelResidualClosedRole.scatter_work Tagged f.2.2.1.1 f.2.2.1.2.1 f.2.2.1.2.2
    f.2.2.2.1 (run (DFTModelSavingResidualFlip.program Tagged) (N,(f.2.1,child))).val
  change (Code.run (DFTModelSavingResidualFlip.program Tagged) () (N,(f.2.1,child))).work≤_ at fw
  change (Code.run (DFTModelResidualClosedRole.scatter Tagged) ()
    (f.2.2.1,(f.2.2.2.1,(Code.run (DFTModelSavingResidualFlip.program Tagged) () (N,(f.2.1,child))).val))).work≤_ at sw
  simp only [program,scatterArgs,flipArgs,originalParams,context,node,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  omega

theorem valid (f:First.T) (N T:ℕ) (child:Tape Tagged.T) :
  (run program ((f,(N,T)),child)).valid := by
  have fw:=DFTModelSavingResidualFlip.valid Tagged N f.2.1 child
  have sw:=DFTModelResidualClosedRoleBounds.scatter_valid Tagged f.2.2.1.1 f.2.2.1.2.1 f.2.2.1.2.2
    f.2.2.2.1 (run (DFTModelSavingResidualFlip.program Tagged) (N,(f.2.1,child))).val
  simpa only [program,scatterArgs,flipArgs,originalParams,context,node,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one,and_true,true_and] using And.intro fw sw

end
end ExactFourierCircuits.DFTModelSavingResidualFinish
