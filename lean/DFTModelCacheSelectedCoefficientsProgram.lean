import DFTModelCacheSelectedCoefficientsConstants
import DFTModelCacheMatchingFactorsNative
import UniformMatchingCoefficientValueBridge

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Bases := p w (p w w)
abbrev Row := p w (p w w)
abbrev Input := p (p w Bases) (p PairBank (Ty.a Row))
abbrev Seed := p Input ConstantBank
abbrev Cell := p Seed w
abbrev DecodeInput := p Bases (p PairBank (p ConstantBank w))
abbrev Output := p Input (p ConstantBank PairBank)

def decodeLabel : Prog false DecodeInput w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def decodeBase (negative : Bool) : Prog false DecodeInput w :=
  .comp (.atom .fst) (if negative then .comp (.atom .snd) (.atom .fst) else .atom .fst)
def decodeConstantsBase : Prog false DecodeInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def decodeIndex (negative : Bool) : Prog false DecodeInput w :=
  .comp (.fork decodeLabel (decodeBase negative)) (.atom (.int .sub))
def decodeBank : Prog false DecodeInput PairBank := .comp (.atom .snd) (.atom .fst)
def decodeAt (negative : Bool) : Prog false DecodeInput (p sc sc) :=
  .comp (.fork decodeBank (decodeIndex negative)) (.atom .look)
def negatePair : Prog false (p sc sc) (p sc sc) :=
  .fork (negative (.atom .fst)) (negative (.atom .snd))
def decodeNegative : Prog false DecodeInput (p sc sc) := .comp (decodeAt true) negatePair
def decodeConstant : Prog false DecodeInput (p sc sc) :=
  .comp (.comp (.fork
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
    (.comp (.fork decodeLabel decodeConstantsBase) (.atom (.int .sub)))) (.atom .look))
    (.fork (.atom .id) (.atom .id))
def isBelowNegative : Prog false DecodeInput w :=
  .comp (.fork decodeLabel (decodeBase true)) (.atom (.int .lt))
def isBelowConstants : Prog false DecodeInput w :=
  .comp (.fork decodeLabel decodeConstantsBase) (.atom (.int .lt))
def decode : Prog false DecodeInput (p sc sc) :=
  .ifz isBelowNegative (.ifz isBelowConstants decodeConstant decodeNegative) (decodeAt false)

def rawHeight : Prog false Input w := .comp (.atom .fst) (.atom .fst)
def setup : Prog false Input Seed := .fork (.atom .id) (.comp rawHeight constants)
def rows : Prog false Seed (Ty.a Row) := .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def currentRow : Prog false Cell Row :=
  .comp (.fork (.comp (.atom .fst) rows) (.atom .snd)) (.atom .look)
def label : Prog false Cell w := .comp currentRow (.comp (.atom .snd) (.atom .snd))
def decodeArgument : Prog false Cell DecodeInput :=
  .fork
    (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))))
    (.fork
      (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))))
      (.fork (.comp (.atom .fst) (.atom .snd)) label))
def cell : Prog false Cell (p sc sc) := .comp decodeArgument decode
def count : Prog false Seed w := .comp rows (.atom .len)
def finish : Prog false Seed Output :=
  .fork (.atom .fst) (.fork (.atom .snd) (.tab count cell))
/-- Raw physical labels are decoded in the actual row order. All supplied
banks/rows and metadata are retained unchanged; constants are computed here. -/
def program : Prog false Input Output := .comp setup finish

def argument (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) : DecodeInput.T :=
  ((C,(T,P)),(b,(cs,d)))
def args (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) : Input.T :=
  ((K,(C,(T,P))),(b,rs))

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
