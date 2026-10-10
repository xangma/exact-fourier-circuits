import DFTModelCacheSelectedCoefficientsProduced
import DFTModelCacheMatchingNatClosed
import DFTModelCConstants

set_option autoImplicit false

/-! Closed composition of the actual coefficient, matching, C-constant and
nine-lane factor producers. The only row tape input is raw physical Row3.
All four producers run once; charged projections retain every intermediate. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w DFTModelCacheSelectedCoefficients.ProducedInput
abbrev Seed := p Input DFTModelCacheSelectedCoefficients.ProducedOutput
abbrev Matched := p Seed DFTModelCacheMatchingNat.Output
abbrev Ready := p Matched DFTModelCConstants.Output
abbrev Output := p Ready (Ty.a sc)

def rawRows : Prog false Input (Ty.a DFTModelCacheSelectedCoefficients.Row) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def matchingArgument : Prog false Input DFTModelCacheMatchingNat.Input := .fork (.atom .fst) rawRows
def masterArgument : Prog false Input DFTModelCConstants.Input :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
def coefficients : Prog false Input Seed :=
  .fork (.atom .id) (.comp (.atom .snd) DFTModelCacheSelectedCoefficients.produced)
def matching : Prog false Seed Matched :=
  .fork (.atom .id) (.comp (.comp (.atom .fst) matchingArgument) DFTModelCacheMatchingNat.program)
def constants : Prog false Matched Ready :=
  .fork (.atom .id) (.comp (.comp (.comp (.atom .fst) (.atom .fst)) masterArgument) DFTModelCConstants.program)
def ambient : Prog false Ready w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst)))
def permutation : Prog false Ready (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def coefficientPairs : Prog false Ready DFTModelCacheSelectedCoefficients.PairBank :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd)
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
def constantCell (j : ℕ) : Prog false Ready sc :=
  .comp (.fork (.atom .snd) (.atom (.lit j))) (.atom .look)
def factorArgument : Prog false Ready DFTModelCacheMatchingFactors.Input :=
  .fork ambient (.fork permutation (.fork coefficientPairs
    (.fork (constantCell 3) (constantCell 2))))
def finish : Prog false Ready Output :=
  .fork (.atom .id) (.comp factorArgument DFTModelCacheMatchingFactors.program)
def program : Prog false Input Output :=
  .comp coefficients (.comp matching (.comp constants finish))

def args (r K C T P : ℕ) (raw : DFTModelCacheSpectrum.Input.T) (rs : Tape DFTModelCacheSelectedCoefficients.Row.T) : Input.T :=
  (r,DFTModelCacheSelectedCoefficients.producedArgs K C T P raw rs)
def seedValue (x : Input.T) : Seed.T := (x,(run DFTModelCacheSelectedCoefficients.produced x.2).val)
def matchedValue (x : Input.T) : Matched.T :=
  (seedValue x,(run DFTModelCacheMatchingNat.program (x.1,x.2.2.2)).val)
def readyValue (x : Input.T) : Ready.T :=
  (matchedValue x,(run DFTModelCConstants.program x.2.2.1.2).val)
def factorArgs (v : Ready.T) : DFTModelCacheMatchingFactors.Input.T :=
  DFTModelCacheMatchingFactors.args v.1.1.1.1 v.1.2.2 v.1.1.2.2.2.2 (v.2.look 3 0) (v.2.look 2 0)

end
end ExactFourierCircuits.DFTModelCacheMatchingProduced
