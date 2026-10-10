import DFTModelGlobalSectorPreparationLocal

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] sumProgram findProgram

abbrev AxisCell := p Axis w
abbrev DigitContext := p AxisCell Found

def widths : Prog false Axis (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def permutation : Prog false Axis (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def blockCount : Prog false Axis w := .comp widths (.atom .len)
def localWidths : Prog false AxisCell (Ty.a w) := .comp (.atom .fst) widths
def localWidth : Prog false AxisCell w := .comp (.fork localWidths (.atom .snd)) (.atom .look)
def localBefore : Prog false AxisCell w := .comp (.fork (.atom .snd) localWidths) sumProgram
def blockCell : Prog false AxisCell Block :=
 .fork (nat .sub localWidth (.atom (.lit 1))) (.fork localWidth localBefore)
def blockProgram : Prog false Axis (Ty.a Block) := .tab blockCount blockCell

def localFound : Prog false AxisCell Found := .comp (.fork (.atom .snd) localWidths) findProgram
def foundWidth : Prog false DigitContext w := .comp (.atom .snd) (.atom .fst)
def foundPosition : Prog false DigitContext w := .comp (.atom .snd) (.atom .snd)
def originalIndex : Prog false DigitContext w := .comp (.atom .fst) (.atom .snd)
def originalDigit : Prog false DigitContext w :=
 .comp (.fork (.comp (.atom .fst) (.comp (.atom .fst) permutation)) originalIndex) (.atom .look)
def digitFinish : Prog false DigitContext Digit :=
 .fork foundWidth (.fork (nat .sub originalIndex foundPosition)
   (.fork foundPosition originalDigit))
def digitCell : Prog false AxisCell Digit := .comp (.fork (.atom .id) localFound) digitFinish
def digitProgram : Prog false Axis (Ty.a Digit) := .tab (.atom .fst) digitCell

def prepareAxis : Prog false Axis PreparedAxis :=
 .fork (.atom .fst) (.fork blockProgram digitProgram)

def localBlockValue (x : Axis.T) (j : ℕ) : Block.T :=
 let w:=x.2.1.look j 0
 (w-1,(w,sumValue j 0 x.2.1))
def localDigitValue (x : Axis.T) (j : ℕ) : Digit.T :=
 let z:=findValue x.2.1.len 0 j x.2.1
 (z.1,(j-z.2,(z.2,x.2.2.look j 0)))
def preparedAxisValue (x : Axis.T) : PreparedAxis.T :=
 (x.1,(Tape.tab x.2.1.len (localBlockValue x),Tape.tab x.1 (localDigitValue x)))

theorem blockCell_run (x : Axis.T) (j : ℕ) :
 run blockCell (x,j)=⟨localBlockValue x j,20*j+41,
   max 1 (max ((x.2.1.look j 0)-1) (max j (sumPeak j 0 x.2.1))),True⟩ := by
 simp [blockCell,localWidth,localWidths,localBefore,widths,nat,run,Code.run,
   Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
 have hs:=sumProgram_run j x.2.1
 dsimp only [run] at hs
 rw [hs]
 simp [localBlockValue]
 omega

theorem digitFinish_run (x : Axis.T) (j : ℕ) (z : Found.T) :
 run digitFinish ((x,j),z)=
   ⟨(z.1,(j-z.2,(z.2,x.2.2.look j 0))),31,j-z.2,True⟩ := by
 simp [digitFinish,foundWidth,foundPosition,originalIndex,originalDigit,permutation,nat,
   run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem digitCell_run (x : Axis.T) (j : ℕ) :
 run digitCell (x,j)=
  ((run findProgram (j,x.2.1)).pass
    (fun z=>run digitFinish ((x,j),z))).pay 11 0 := by
 simp only [digitCell,localFound,localWidths,widths,run,Code.run,Atom.run,
   Bill.pass,Bill.pay,Bill.one]
 congr 1
 all_goals simp
 all_goals omega

theorem digitCell_value (x : Axis.T) (j : ℕ) :
 (run digitCell (x,j)).val=localDigitValue x j := by
 rw [digitCell_run,findProgram_run]
 simp only [Bill.pass,Bill.pay]
 rw [digitFinish_run,find_depth_value]
 rfl

theorem digitCell_valid (x : Axis.T) (j : ℕ) : (run digitCell (x,j)).valid := by
 rw [digitCell_run,findProgram_run]
 simp only [Bill.pass,Bill.pay]
 rw [digitFinish_run]
 exact ⟨find_depth_valid _ _ _ _,trivial⟩

theorem digitCell_work (x : Axis.T) (j : ℕ) :
 (run digitCell (x,j)).work≤42*x.2.1.len+56 := by
 rw [digitCell_run,findProgram_run]
 simp only [Bill.pass,Bill.pay]
 rw [digitFinish_run]
 have h:=find_depth_work x.2.1.len 0 j x.2.1
 dsimp only [Bill.work]
 omega

theorem blockProgram_value (x : Axis.T) :
 (run blockProgram x).val=Tape.tab x.2.1.len (localBlockValue x) := by
 change (Bill.tab (run blockCount x).val Block.blank (fun j=>run blockCell (x,j))).val=_
 have hc:(run blockCount x).val=x.2.1.len := by
  simp [blockCount,widths,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [hc,ModelEquivalenceInterpreter.tab_value]
 exact congrArg (Tape.tab _) (funext (fun j=>congrArg Bill.val (blockCell_run x j)))

theorem digitProgram_value (x : Axis.T) :
 (run digitProgram x).val=Tape.tab x.1 (localDigitValue x) := by
 change (Bill.tab x.1 Digit.blank (fun j=>run digitCell (x,j))).val=_
 rw [ModelEquivalenceInterpreter.tab_value]
 exact congrArg (Tape.tab _) (funext (digitCell_value x))

theorem prepareAxis_value (x : Axis.T) :
 (run prepareAxis x).val=preparedAxisValue x := by
 change (x.1,((run blockProgram x).val,(run digitProgram x).val))=_
 rw [blockProgram_value,digitProgram_value]
 rfl

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
