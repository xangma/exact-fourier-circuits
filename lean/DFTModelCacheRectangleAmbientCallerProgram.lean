import DFTModelCacheRectangleCallerPeak
import DFTModelCacheAmbientPoolCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
namespace RC
abbrev Input := DFTModelCacheRectangleCaller.Input
abbrev Output := DFTModelCacheRectangleCaller.Output
end RC
namespace MP
abbrev Input := DFTModelCacheMatchingProduced.Input
end MP

/-- Ambient size is an ordinary separate word. The retained rectangle input
contains its original seed order, master root, addresses, slot and seven words. -/
abbrev Input := p w RC.Input
abbrev Context := p w RC.Output
abbrev Output := p Context DFTModelCacheAmbientPool.Output

def original : Prog false Context RC.Input :=
 .comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))
def localInput : Prog false Context MP.Input :=
 .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd)
  (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))))))
def offset : Prog false Context w := .comp original (DFTModelCacheRectangleCaller.row 1)
def coefficientHeader : Prog false Context (p w DFTModelCacheSelectedCoefficients.Bases) :=
 .comp localInput (.comp (.atom .snd) (.atom .fst))
def spectrum : Prog false Context DFTModelCacheSpectrum.Input :=
 .comp localInput (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def rows : Prog false Context (Ty.a DFTModelCacheSelectedCoefficients.Row) :=
 .comp localInput DFTModelCacheMatchingProduced.rawRows
def argument : Prog false Context DFTModelCacheAmbientPool.Input :=
 .fork offset (.fork (.atom .fst) (.fork coefficientHeader (.fork spectrum rows)))
def prepare : Prog false Input Context :=
 .fork (.atom .fst) (.comp (.atom .snd) DFTModelCacheRectangleCaller.program)
def finish : Prog false Context Output :=
 .fork (.atom .id) (.comp argument DFTModelCacheAmbientPool.program)
/-- The descriptor-derived local producer and translated ambient producer run
once each. The local pool remains retained and its entire cost is included. -/
def program : Prog false Input Output := .comp prepare finish

def localInputValue (x:Context.T) : MP.Input.T := x.2.2.2.1.1.1.1
def argumentValue (x:Context.T) : DFTModelCacheAmbientPool.Input.T :=
 (DFTModelCacheRectangleCaller.rowValue x.2.1.1 1,
  (x.1,((localInputValue x).2.1,((localInputValue x).2.2.1,(localInputValue x).2.2.2))))

end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
