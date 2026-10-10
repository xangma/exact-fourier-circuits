import DFTModelCacheAmbientPoolTranslation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheAmbientPool
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
namespace MP
abbrev Input := DFTModelCacheMatchingProduced.Input
abbrev Output := DFTModelCacheMatchingProduced.Output
end MP
abbrev Input := p w MP.Input
abbrev Ready := p Input MP.Input
abbrev Output := p Ready MP.Output

def inputRows : Prog false Input (Ty.a DFTModelCacheSelectedCoefficients.Row) :=
 .comp (.atom .snd) DFTModelCacheMatchingProduced.rawRows
def translationArgument : Prog false Input TranslationInput := .fork (.atom .fst) inputRows
def physicalRadix : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def coefficientHeader : Prog false Input (p w DFTModelCacheSelectedCoefficients.Bases) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def spectrumArgument : Prog false Input DFTModelCacheSpectrum.Input :=
 .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def matchingArgument : Prog false Input MP.Input :=
 .fork physicalRadix (.fork coefficientHeader (.fork spectrumArgument
  (.comp translationArgument translate)))
def prepare : Prog false Input Ready := .fork (.atom .id) matchingArgument
/-- Translate the genuine local occurrence tape once, then invoke the same
closed proper-spectrum/matching/constants/nine-lane producer once at ambient radix. -/
def program : Prog false Input Output :=
 .comp prepare (.fork (.atom .id) (.comp (.atom .snd) DFTModelCacheMatchingProduced.program))

def argumentValue (x:Input.T) : MP.Input.T :=
 (x.2.1,(x.2.2.1,(x.2.2.2.1,translatedTape x.1 x.2.2.2.2)))
def args (o r K C T P:ℕ) (raw:DFTModelCacheSpectrum.Input.T)
 (rs:Tape DFTModelCacheSelectedCoefficients.Row.T) : Input.T :=
 (o,DFTModelCacheMatchingProduced.args r K C T P raw rs)

attribute [local irreducible] translate DFTModelCacheMatchingProduced.program

theorem prepare_run (x:Input.T) :
 run prepare x=⟨(x,argumentValue x),(run translate (x.1,x.2.2.2.2)).work+30,
  (run translate (x.1,x.2.2.2.2)).peak,(run translate (x.1,x.2.2.2.2)).valid⟩ := by
 simp only [prepare,matchingArgument,physicalRadix,coefficientHeader,spectrumArgument,
  translationArgument,inputRows,DFTModelCacheMatchingProduced.rawRows,
  run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,true_and,and_true]
 rw [translate_value]
 unfold argumentValue
 congr 1
 omega

theorem program_run (x:Input.T) :
 run program x=⟨((x,argumentValue x),
  (run DFTModelCacheMatchingProduced.program (argumentValue x)).val),
  (run translate (x.1,x.2.2.2.2)).work+
   (run DFTModelCacheMatchingProduced.program (argumentValue x)).work+35,
  max (run translate (x.1,x.2.2.2.2)).peak
   (run DFTModelCacheMatchingProduced.program (argumentValue x)).peak,
  (run translate (x.1,x.2.2.2.2)).valid ∧
   (run DFTModelCacheMatchingProduced.program (argumentValue x)).valid⟩ := by
 rw [program,comp_run,prepare_run]
 simp only [fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
  max_zero,zero_max,and_true,true_and]
 congr 1
 omega

end
end ExactFourierCircuits.DFTModelCacheAmbientPool
