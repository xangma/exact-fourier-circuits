import DFTModelCacheSelectedPhysicalRowsMatching

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
abbrev Control := p (p w DFTModelCacheSelectedCoefficients.Bases) DFTModelCacheSpectrum.Input
abbrev Input := p Control DFTModelCacheSelectedPhysicalRows.Input
abbrev Mapped := p Input (Ty.a DFTModelCacheColor.Row)
def start : Prog false Input Mapped := .fork (.atom .id)
 (.comp (.atom .snd) DFTModelCacheSelectedPhysicalRows.program)
def argument : Prog false Mapped DFTModelCacheMatchingProduced.Input :=
 .fork (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst)))
   (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))) (.atom .snd)))
def finish : Prog false Mapped DFTModelCacheMatchingProduced.Output :=
 .comp argument DFTModelCacheMatchingProduced.program
/-- Generate physical rows once, then run the actual Matching55, coefficient,
constant and factor producers once on that same generated tape. -/
def program : Prog false Input DFTModelCacheMatchingProduced.Output := .comp start finish
def argumentValue (x:Input.T) (rs:Tape DFTModelCacheColor.Row.T) :
 DFTModelCacheMatchingProduced.Input.T := (x.2.1.1,(x.1.1,(x.1.2,rs)))

attribute [local irreducible] DFTModelCacheSelectedPhysicalRows.program DFTModelCacheMatchingProduced.program
theorem argument_run (x:Input.T) (rs:Tape DFTModelCacheColor.Row.T) :
 run argument (x,rs)=⟨argumentValue x rs,21,0,True⟩ := by
 simp [argument,argumentValue,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem start_run (x:Input.T) : run start x=
 ⟨(x,(run DFTModelCacheSelectedPhysicalRows.program x.2).val),
  (run DFTModelCacheSelectedPhysicalRows.program x.2).work+4,
  (run DFTModelCacheSelectedPhysicalRows.program x.2).peak,
  (run DFTModelCacheSelectedPhysicalRows.program x.2).valid⟩ := by
 rw [start,DFTModelCacheColorRebase.retained_comp_run]
 simp only [atom_run,Atom.run,Bill.one,zero_max,true_and]
 congr 1
 omega

theorem program_run (x:Input.T) :
 let m:=run DFTModelCacheSelectedPhysicalRows.program x.2
 let f:=run DFTModelCacheMatchingProduced.program (argumentValue x m.val)
 run program x=⟨f.val,m.work+f.work+27,max m.peak f.peak,m.valid∧f.valid⟩ := by
 dsimp only
 rw [program,comp_run,start_run]
 simp only [Bill.pass,Bill.pay]
 rw [finish,comp_run,argument_run]
 simp only [Bill.pass,Bill.pay,zero_max,max_zero,true_and]
 congr 1
 omega

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsProduced
