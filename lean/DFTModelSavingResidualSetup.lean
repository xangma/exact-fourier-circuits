import DFTModelSavingResidualOrientation
import DFTModelResidualClosedRoleBounds
import DFTModelAffinePaired
import UniformBatching
import DFTModelClockBatch

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualSetup
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelResidualCore
open DFTModelResidualClosedBasis (Meta)
noncomputable section
attribute [local irreducible] UniformBatching.width

abbrev Params := p w sc
abbrev Node := p Params (Ty.a Tagged)
/-- Raw descriptor metadata, selected parent role, raw decreasing flag, and
the complete parent node. Neither the effective orientation nor any address
table is supplied. -/
abbrev Input := p Meta (p w (p w Node))
abbrev First := p Input (p w (DFTModelResidualClosedRoleStages.Context Tagged))
abbrev Setup := p First (p w w)

def metadata : Prog false Input Meta := .atom .fst
def role : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def inverse : Prog false Input w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def node : Prog false Input Node := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def q : Prog false Input w := .comp metadata (.atom .fst)
def m : Prog false Input w := .comp metadata (.comp (.atom .snd) (.atom .fst))
def bits : Prog false Input (Ty.a w) :=
  .comp metadata (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def roleInput : Prog false Input (DFTModelResidualClosedRoleStages.Input Tagged) :=
  .fork metadata (.fork role (.comp node (.atom .snd)))
def orientationInput : Prog false Input DFTModelSavingResidualOrientation.Input :=
  .fork (.fork m bits) inverse
def initial : Prog false Input First := .fork (.atom .id) (.fork
  (.comp orientationInput DFTModelSavingResidualOrientation.program)
  (.comp roleInput (DFTModelResidualClosedRole.gather Tagged)))
def sizeTail : Prog false (p First w) Setup := .fork (.atom .fst)
  (.fork (.atom .snd) (binary .mul (.atom (.lit UniformBatching.width)) (.atom .snd)))
def sizes : Prog false First Setup := .comp
  (.fork (.atom .id) (.comp (.comp (.atom .fst) q) power)) sizeTail
def program : Prog false Input Setup := .comp initial sizes

def gathered : Prog false Setup (Ty.a Tagged) := .comp (.atom .fst)
  (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
def chunk : Prog false Setup w := .comp (.atom .snd) (.atom .snd)
def params : Prog false Setup Params := .fork
  (.comp (.atom .fst) (.comp (.atom .fst) q))
  (.comp (.atom .fst) (.comp (.atom .fst) (.comp node (.comp (.atom .fst) (.atom .snd)))))
def batchArgs : Prog false Setup (DFTModelClockBatch.Input Params Tagged) := .fork params
  (.fork (binary .div (.comp gathered (.atom .len)) chunk) (.fork chunk gathered))

attribute [local irreducible] DFTModelResidualClosedRole.gather
  DFTModelSavingResidualOrientation.program power

theorem initial_value (ctx:Meta.T) (a raw:ℕ) (k:ℕ) (I:ℂ) (bank:Tape Tagged.T) :
  (run initial (ctx,(a,(raw,((k,I),bank))))).val=
    ((ctx,(a,(raw,((k,I),bank)))),
      ((run DFTModelSavingResidualOrientation.program ((ctx.2.1,ctx.2.2.2),raw)).val,
        (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,bank))).val)) := rfl

theorem sizes_run (f:First.T) :
  run sizes f=⟨(f,(2^f.1.1.1,UniformBatching.width*2^f.1.1.1)),
    (run power f.1.1.1).work+18,
    max (run power f.1.1.1).peak (max UniformBatching.width (UniformBatching.width*2^f.1.1.1)),
    (run power f.1.1.1).valid⟩ := by
  simp [sizes,sizeTail,q,metadata,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,DFTModelResidualCore.power_value,
    max_left_comm]
  omega

attribute [local irreducible] initial sizes

theorem value (ctx:Meta.T) (a raw k:ℕ) (I:ℂ) (bank:Tape Tagged.T) :
  (run program (ctx,(a,(raw,((k,I),bank))))).val=
    ((run initial (ctx,(a,(raw,((k,I),bank))))).val,(2^ctx.1,UniformBatching.width*2^ctx.1)) := by
  change (run sizes (run initial (ctx,(a,(raw,((k,I),bank))))).val).val=_
  rw [sizes_run]
  have first:(run initial (ctx,(a,(raw,((k,I),bank))))).val.1=(ctx,(a,(raw,((k,I),bank)))):=congrArg Prod.fst (initial_value ctx a raw k I bank)
  rw [first]

theorem batchArgs_run (f:First.T) (N T:ℕ) :
  run batchArgs (f,(N,T))=⟨((f.1.1.1,f.1.2.2.2.1.2),
    (f.2.2.2.2.len/T,(T,f.2.2.2.2))),53,
      max f.2.2.2.2.len (f.2.2.2.2.len/T),True⟩ := by
  simp [batchArgs,params,gathered,chunk,node,q,metadata,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem initial_work (ctx:Meta.T) (a raw k:ℕ) (I:ℂ) (bank:Tape Tagged.T) :
  (run initial (ctx,(a,(raw,((k,I),bank))))).work=
    (run DFTModelSavingResidualOrientation.program ((ctx.2.1,ctx.2.2.2),raw)).work+
    (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,bank))).work+37 := by
  simp [initial,orientationInput,roleInput,m,bits,metadata,inverse,role,node,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  omega

theorem work (ctx:Meta.T) (a raw k:ℕ) (I:ℂ) (bank:Tape Tagged.T) :
  (run program (ctx,(a,(raw,((k,I),bank))))).work≤
    (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,bank))).work+22*ctx.2.1+8*ctx.1+88 := by
  have oi:=DFTModelSavingResidualOrientation.program_work ctx.2.1 ctx.2.2.2 raw
  change (run initial _).work+(run sizes (run initial _).val).work+1≤_
  rw [initial_work,sizes_run,initial_value,power_work]
  dsimp only [Bill.work]
  omega

theorem valid (ctx:Meta.T) (a raw k:ℕ) (I:ℂ) (bank:Tape Tagged.T) :
  (run program (ctx,(a,(raw,((k,I),bank))))).valid := by
  have orientation:=DFTModelSavingResidualOrientation.program_valid ctx.2.1 ctx.2.2.2 raw
  have gather:=DFTModelResidualClosedRoleBounds.gather_valid Tagged ctx a bank
  have first:(run initial (ctx,(a,(raw,((k,I),bank))))).valid:=by
    simpa only [initial,orientationInput,roleInput,m,bits,metadata,inverse,role,node,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,true_and,and_true] using
      And.intro orientation gather
  change (run initial _).valid ∧ (run sizes (run initial _).val).valid
  rw [sizes_run,initial_value]
  exact ⟨first,power_valid _⟩

end
end ExactFourierCircuits.DFTModelSavingResidualSetup
