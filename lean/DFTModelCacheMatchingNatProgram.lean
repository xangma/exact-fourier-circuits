import DFTModelCacheNatControl
import UniformMatchingAxisTableMachine

set_option autoImplicit false

/-! Literal natural-only client of the local typed compiler. Selection of the
input rows is an explicit caller boundary; no permutation is supplied. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

def instructions : List DFTModelCacheNatControl.Instruction := [
  .literal 850 0,.literal 851 1,.literal 852 2,.literal 853 3,.literal 854 0,
  .branch 854 840 6 10,
  .binary .add 857 845 854,.store 857 850,.binary .add 854 854 851,.jump 5,
  .literal 854 0,.literal 855 0,.literal 856 0,.branch 854 841 14 33,
  .binary .mul 857 854 853,.binary .add 857 842 857,.load 858 857,
  .binary .add 857 857 851,.load 859 857,.binary .add 857 843 855,
  .store 857 858,.binary .add 857 857 851,.store 857 859,
  .binary .add 857 845 858,.store 857 851,.binary .add 857 845 859,.store 857 851,
  .binary .add 857 844 856,.store 857 852,.binary .add 854 854 851,
  .binary .add 855 855 852,.binary .add 856 856 851,.jump 13,
  .literal 860 0,.branch 860 840 35 46,.binary .add 857 845 860,.load 861 857,
  .branch 861 851 38 44,.binary .add 857 843 855,.store 857 860,
  .binary .add 857 844 856,.store 857 851,.binary .add 855 855 851,
  .binary .add 856 856 851,.binary .add 860 860 851,.jump 34,
  .binary .add 857 846 850,.store 857 856,.binary .add 857 857 851,.store 857 844,
  .binary .add 857 857 851,.store 857 840,.binary .add 857 857 851,.store 857 843,.halt]

theorem instructions_length : instructions.length=55 := rfl
theorem instructions_native : instructions.map Instruction.native=
    UniformMatchingAxisTableMachine.program := rfl

abbrev Row := p w (p w w)
abbrev Input := p w (Ty.a Row)
abbrev Indexed := p Input w

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def count : Prog false Input w := .comp (.atom .snd) (.atom .len)
def radix : Prog false Input w := .atom .fst
def permutationBase : Prog false Input w := nat .mul (.atom (.lit 3)) count
def widthsBase : Prog false Input w := nat .add permutationBase radix
def markersBase : Prog false Input w := nat .add widthsBase radix
def axisBase : Prog false Input w := nat .add markersBase radix
def heapLength : Prog false Input w := nat .add (.atom (.lit 867)) axisBase

def eqTest {s : Ty} (f : Prog false s w) (n : ℕ) : Prog false s w :=
  nat .add (nat .sub f (.atom (.lit n))) (nat .sub (.atom (.lit n)) f)
def select {s t : Ty} (f : Prog false s w) (n : ℕ)
    (yes no : Prog false s t) : Prog false s t := .ifz (eqTest f n) yes no

def registerCell : Prog false Indexed w :=
  select (.atom .snd) 840 (.comp (.atom .fst) radix)
  (select (.atom .snd) 841 (.comp (.atom .fst) count)
  (select (.atom .snd) 843 (.comp (.atom .fst) permutationBase)
  (select (.atom .snd) 844 (.comp (.atom .fst) widthsBase)
  (select (.atom .snd) 845 (.comp (.atom .fst) markersBase)
  (select (.atom .snd) 846 (.comp (.atom .fst) axisBase) (.atom (.lit 0)))))))

def rowIndex : Prog false Indexed w := nat .div (.atom .snd) (.atom (.lit 3))
def rowOffset : Prog false Indexed w := nat .mod (.atom .snd) (.atom (.lit 3))
def row : Prog false Indexed Row :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) rowIndex) (.atom .look)
/-- The ignored coefficient field is deliberately initialized by a charged zero
literal; only the two source endpoint projections are copied. -/
def endpoint : Prog false Indexed w :=
  select rowOffset 0 (.comp row (.atom .fst))
    (select rowOffset 1 (.comp row (.comp (.atom .snd) (.atom .fst))) (.atom (.lit 0)))
def sourceTest : Prog false Indexed w :=
  nat .lt (.atom .snd) (.comp (.atom .fst) permutationBase)
def heapCell : Prog false Indexed (p w w) :=
  .ifz sourceTest (.fork (.atom (.lit 0)) (.atom (.lit 0)))
    (.fork (.atom (.lit 1)) endpoint)
def initializeProgram : Prog false Input Local :=
  .fork (.atom (.lit 0))
    (.fork (.tab (.atom (.lit 862)) registerCell) (.tab heapLength heapCell))

def P (M : ℕ) := 3*M
def W (r M : ℕ) := P M+r
def U (r M : ℕ) := W r M+r
def A (r M : ℕ) := U r M+r
def wordBound (r M : ℕ) := 866+A r M
def heapSize (r M : ℕ) := wordBound r M+1
def registerValue (r M j : ℕ) : ℕ :=
  if j=840 then r else if j=841 then M else if j=843 then P M
  else if j=844 then W r M else if j=845 then U r M else if j=846 then A r M else 0
def endpointValue (z : Tape Row.T) (j : ℕ) : ℕ :=
  if j%3=0 then (z.look (j/3) (0,(0,0))).1
  else if j%3=1 then (z.look (j/3) (0,(0,0))).2.1 else 0
def heapValue (z : Tape Row.T) (j : ℕ) : ℕ × ℕ :=
  if j<3*z.len then (1,endpointValue z j) else (0,0)
def initialValue (r : ℕ) (z : Tape Row.T) : LocalValue :=
  (0,(Tape.tab 862 (registerValue r z.len),Tape.tab (heapSize r z.len) (heapValue z)))

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
