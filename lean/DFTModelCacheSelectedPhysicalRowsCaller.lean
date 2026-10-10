import DFTModelCacheSelectedPhysicalRowsProducedCorrect
import DFTModelCacheHeightColorCallerBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Input := p DFTModelCacheSelectedPhysicalRowsProduced.Control
 (p DFTModelCacheSelectedPhysicalRows.Geometry DFTModelCacheHeightColorCaller.Input)
abbrev Context := p Input DFTModelCacheHeightColorCaller.Output
abbrev Output := p DFTModelCacheHeightColorCaller.Output DFTModelCacheMatchingProduced.Output

def prepare : Prog false Input Context := .fork (.atom .id)
 (.comp (.comp (.atom .snd) (.atom .snd)) DFTModelCacheHeightColorCaller.program)
def argument : Prog false Context DFTModelCacheSelectedPhysicalRowsProduced.Input :=
 .fork (.comp (.atom .fst) (.atom .fst))
  (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
   (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
def finish : Prog false Context Output := .fork (.atom .snd)
 (.comp argument DFTModelCacheSelectedPhysicalRowsProduced.program)
/-- One actual raw topology/height/color call followed by one physical mapper
and one MatchingProduced call. Original topology and selected rows are retained. -/
def program : Prog false Input Output := .comp prepare finish
def argumentValue (x:Input.T) (h:DFTModelCacheHeightColorCaller.Output.T) :
 DFTModelCacheSelectedPhysicalRowsProduced.Input.T := (x.1,(x.2.1,h.2.2))

attribute [local irreducible] DFTModelCacheHeightColorCaller.program
 DFTModelCacheSelectedPhysicalRowsProduced.program

theorem argument_run (x:Input.T) (h:DFTModelCacheHeightColorCaller.Output.T) :
 run argument (x,h)=⟨argumentValue x h,15,0,True⟩ := by
 simp [argument,argumentValue,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] Code.run

theorem prepare_run (x:Input.T) : run prepare x=
 let h:=run DFTModelCacheHeightColorCaller.program x.2.2
 ⟨(x,h.val),h.work+6,h.peak,h.valid⟩ := by
 rw [prepare,DFTModelCacheColorRebase.retained_comp_run]
 simp only [comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,true_and]
 congr 1
 omega

theorem program_run (x:Input.T) :
 let h:=run DFTModelCacheHeightColorCaller.program x.2.2
 let f:=run DFTModelCacheSelectedPhysicalRowsProduced.program (argumentValue x h.val)
 run program x=⟨(h.val,f.val),h.work+f.work+25,max h.peak f.peak,h.valid∧f.valid⟩ := by
 dsimp only
 rw [program,comp_run,prepare_run]
 simp only [Bill.pass,Bill.pay]
 rw [finish,fork_run,comp_run,argument_run,atom_run]
 simp only [Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,true_and,and_true]
 congr 1
 omega

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
