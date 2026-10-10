import DFTModelCacheHeightRawLocalBounds
import DFTModelCacheHeightNative
import DFTModelCacheColorRebaseSelected

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightColorCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore (fork_run comp_run atom_run)
noncomputable section
def nat {s:Ty} (op:NOp) (f g:Prog false s w) : Prog false s w :=
 .comp (.fork f g) (.atom (.int op))
abbrev Input := p w DFTModelCacheHeightRaw.Input
abbrev Context := p Input DFTModelCacheHeightRaw.Output
abbrev Output := p Context (p DFTModelCacheColorRebaseSelected.Ready (Ty.a DFTModelCacheColor.Row))

def color : Prog false Context w := .comp (.atom .fst) (.atom .fst)
def config : Prog false Context DFTModelCacheHeightRaw.Config :=
 .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def extent : Prog false Context w :=
 .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def count : Prog false Context w :=
 .comp (.atom .snd) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))))
def rows : Prog false Context (Ty.a DFTModelCacheColor.Row) := .comp (.atom .snd) (.atom .snd)
def bound : Prog false Context w := nat .add (nat .add extent (.atom (.lit 1))) count

def argument : Prog false Context DFTModelCacheColorRebaseSelected.Input :=
 .fork color (.fork (.comp config (.atom .fst)) (.fork bound rows))
def prepare : Prog false Input Context :=
 .fork (.atom .id) (.comp (.atom .snd) DFTModelCacheHeightRaw.program)
def finish : Prog false Context Output :=
 .fork (.atom .id) (.comp argument DFTModelCacheColorRebaseSelected.program)
/-- Generate topology, depths and rows once, then color locally and retain the
selected original physical rows. No row tape, colors or matching certificate is input. -/
def program : Prog false Input Output := .comp prepare finish

def argumentValue (x:Input.T) (v:DFTModelCacheHeightRaw.Output.T) :
 DFTModelCacheColorRebaseSelected.Input.T :=
 (x.1,(x.2.1.1,(x.2.2.2+1+v.1.1.2.1,v.2)))

theorem argument_run (x:Input.T) (v:DFTModelCacheHeightRaw.Output.T) :
 run argument (x,v)=⟨argumentValue x v,39,x.2.2.2+1+v.1.1.2.1,True⟩ := by
 simp only [argument,color,config,bound,extent,count,rows,nat,run,Code.run,Atom.run,
  NOp.run,argumentValue,Bill.one,Bill.word,Bill.pass,Bill.pay,zero_max,max_zero,and_true]
 congr 1
 omega



attribute [local irreducible] Code.run DFTModelCacheHeightRaw.program
 DFTModelCacheColorRebaseSelected.program prepare finish argument

theorem prepare_run (x:Input.T) : run prepare x=
 let h:=run DFTModelCacheHeightRaw.program x.2
 ⟨(x,h.val),h.work+4,h.peak,h.valid⟩ := by
 rw [prepare,DFTModelCacheColorRebase.retained_comp_run,atom_run]
 simp only [Atom.run,Bill.one,true_and,zero_max]
 congr 1
 omega

theorem finish_run (x:Input.T) (v:DFTModelCacheHeightRaw.Output.T) : run finish (x,v)=
 let c:=run DFTModelCacheColorRebaseSelected.program (argumentValue x v)
 ⟨((x,v),c.val),c.work+42,max (x.2.2.2+1+v.1.1.2.1) c.peak,c.valid⟩ := by
 rw [finish,DFTModelCacheColorRebase.retained_comp_run,argument_run]
 simp only [true_and]
 congr 1
 omega

theorem program_run (x:Input.T) : run program x=
 let h:=run DFTModelCacheHeightRaw.program x.2
 let c:=run DFTModelCacheColorRebaseSelected.program (argumentValue x h.val)
 ⟨((x,h.val),c.val),h.work+c.work+47,max h.peak (max (x.2.2.2+1+h.val.1.1.2.1) c.peak),
 h.valid∧c.valid⟩ := by
 rw [program,comp_run,prepare_run]
 rw [Bill.pass,finish_run]
 simp only [Bill.pay,max_zero]
 congr 1
 omega

end
end ExactFourierCircuits.DFTModelCacheHeightColorCaller
