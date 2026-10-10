import DFTModelCacheMatchingNatBounds
import DFTModelCacheNatDispatchFinite
import UniformGreedyColorMachine

set_option autoImplicit false

/-! Charged raw-endpoint client of the literal native greedy-coloring program.
The third coefficient word is retained in the input and projected to charged
zero in the native endpoint arena. Exhaustion returns sentinel 11. -/
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

abbrev Row := DFTModelCacheMatchingNat.Row
abbrev Input := DFTModelCacheMatchingNat.Input
abbrev Indexed := p Input w
abbrev nat := @DFTModelCacheMatchingNat.nat
abbrev select := @DFTModelCacheMatchingNat.select
abbrev count := DFTModelCacheMatchingNat.count
abbrev radix := DFTModelCacheMatchingNat.radix

def instructions : List Instruction := [
  .literal 810 0,.literal 811 1,.literal 812 3,.literal 813 11,.literal 814 0,
  .branch 814 800 6 50,.literal 816 0,.branch 816 813 8 12,
  .binary .add 817 803 816,.store 817 810,.binary .add 816 816 811,.jump 7,
  .binary .mul 817 814 812,.binary .add 817 801 817,.load 818 817,
  .binary .add 817 817 811,.load 819 817,.literal 815 0,
  .branch 815 814 19 39,.binary .mul 817 815 812,.binary .add 817 801 817,
  .load 820 817,.binary .add 817 817 811,.load 821 817,
  .branch 820 818 26 25,.branch 818 820 26 34,
  .branch 820 819 28 27,.branch 819 820 28 34,
  .branch 821 818 30 29,.branch 818 821 30 34,
  .branch 821 819 32 31,.branch 819 821 32 34,
  .binary .add 815 815 811,.jump 18,.binary .add 817 802 815,.load 822 817,
  .binary .add 817 803 822,.store 817 811,.jump 32,
  .literal 816 0,.branch 816 813 41 46,.binary .add 817 803 816,.load 823 817,
  .branch 823 811 46 44,.binary .add 816 816 811,.jump 40,
  .binary .add 817 802 814,.store 817 816,.binary .add 814 814 811,.jump 5,.halt]

theorem instructions_length : instructions.length=51 := rfl
theorem instructions_native : instructions.map Instruction.native=
    UniformGreedyColorMachine.program := rfl

theorem instructions_footprint :
    ∀i∈instructions,DFTModelCacheNatDispatchFinite.Footprint 824 824 i := by
  intro i hi
  simp only [instructions,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst i;simp [DFTModelCacheNatDispatchFinite.Footprint]

def colorBase : Prog false Input w := nat .mul (.atom (.lit 3)) count
def paletteBase : Prog false Input w := nat .mul (.atom (.lit 4)) count
def heapLength : Prog false Input w :=
  nat .add (.atom (.lit 913)) (nat .add radix paletteBase)
def registerCell : Prog false Indexed w :=
  select (.atom .snd) 800 (.comp (.atom .fst) count)
  (select (.atom .snd) 802 (.comp (.atom .fst) colorBase)
  (select (.atom .snd) 803 (.comp (.atom .fst) paletteBase) (.atom (.lit 0))))
def initializeProgram : Prog false Input Local :=
  .fork (.atom (.lit 0))
    (.fork (.tab (.atom (.lit 824)) registerCell)
      (.tab heapLength DFTModelCacheMatchingNat.heapCell))

def C (M : ℕ) := 3*M
def U (M : ℕ) := 4*M
def B (r M : ℕ) := 912+r+U M
def H (r M : ℕ) := B r M+1
def registerValue (M j : ℕ) :=
  if j=800 then M else if j=802 then C M else if j=803 then U M else 0
def initialValue (r : ℕ) (z : Tape Row.T) : LocalValue :=
  (0,(Tape.tab 824 (registerValue z.len),Tape.tab (H r z.len) (DFTModelCacheMatchingNat.heapValue z)))

def runtimeProgram : Prog false Input w :=
  nat .mul (.atom (.lit 200))
    (nat .mul (nat .add count (.atom (.lit 1))) (nat .add count (.atom (.lit 1))))
def compiled : Prog false Input Local :=
  .comp (.fork runtimeProgram initializeProgram)
    (DFTModelCacheNatDispatch.fuelProgram instructions)

end
end ExactFourierCircuits.DFTModelCacheColor
