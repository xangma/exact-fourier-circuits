import UniformGlobalCalendarPhaseDirectory
import UniformGlobalCalendarFactorMergeTable
import UniformGlobalCalendarUnionRowsTable
import UniformGlobalCalendarPrinterFrames
import UniformGlobalScalePoolMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- Persistent outer inputs6766..6772 are selected-bank/count, ambient radix,
fresh9r pool, row output/count and fresh phase directory. Every selected entry
is visited. Scratch6740..6752 belongs to the charged merger/row printer. -/
def boot : List Op := [.literal 6774 1,.literal 6775 2,.literal 6776 0,
 .literal 6773 0,.literal 6771 0,.mul 2600 6772 6774]
def initSetup : List Op := [.mul 4330 6769 6774,.mul 4331 6768 6774]
def readEntry : List Op := [.mul 6777 6773 6775,.add 6777 6766 6777,
 .getNat 6778 6777,.add 6777 6777 6774,.getNat 6779 6777,
 .add 6785 6778 6776,.literal 6787 2,.add 6785 6785 6787,.getNat 6781 6785,
 .add 6785 6785 6774,.getNat 6784 6785,.literal 6787 2,.add 6785 6785 6787,
 .getNat 6783 6785,.add 6785 6785 6774,.getNat 6780 6785,.sub 6782 6768 6784]
def phaseSetup : List Op := [.mul 6760 6772 6774,.mul 6761 6779 6774]
def factorSetup : List Op := [.mul 6740 6781 6774,.mul 6741 6768 6774,
 .mul 6742 6765 6774,.mul 6743 6769 6774]
def rowsSetup : List Op := [.mul 6740 6783 6774,.mul 6741 6782 6774,
 .mul 6742 6770 6774,.mul 6743 6771 6774]
def rowsReturn : List Op := [.mul 6771 6743 6774]
def advance : List Op := [.add 6773 6773 6774]

def main : Program := boot.map Op.code++[.jump 52]++
 initSetup.map Op.code++[.jump 224,.branchLT 6773 6767 11 51]++
 readEntry.map Op.code++[.branchLT 6780 6774 30 29,.branchLT 6780 6775 34 42]++
 phaseSetup.map Op.code++[.jump 235,.branchLT 6764 6774 36 42,
 .natLiteral 6765 0,.jump 36]++factorSetup.map Op.code++[.jump 243,.jump 49]++
 rowsSetup.map Op.code++[.jump 258]++rowsReturn.map Op.code++[.jump 49]++
 advance.map Op.code++[.jump 10,.halt]

def phasePrinter : Program := UniformFixedNetworkScheduleMachine.program UniformGlobalCalendarPhaseDirectory.words
/-- One literal281-instruction calendar dispatcher constructs its decoder and
fresh factor pool, then merges every selected diagonal or ordered C-pair bank.
Kind0 uses the true28-phase decoder; kind1 is a one-tick scale; kind2 is reserved
for a genuine bare C event. No82 scalar shear is treated as a bare C call. -/
def program : Program := main++phasePrinter.map (relocate 52 7)++
 UniformGlobalScalePoolMachine.program.map (relocate 224 10)++
 UniformGlobalCalendarPhaseDirectory.program.map (relocate 235 33)++
 UniformGlobalCalendarFactorMerge.program.map (relocate 243 41)++
 UniformGlobalCalendarUnionRows.program.map (relocate 258 47)

lemma main_length : main.length=52 := rfl
lemma phasePrinter_length : phasePrinter.length=172 := by
 rw [phasePrinter,UniformFixedNetworkScheduleMachine.program_length,UniformGlobalCalendarPhaseDirectory.words_length]
lemma program_length : program.length=281 := by
 simp only [program,List.length_append,List.length_map,main_length,phasePrinter_length,
  UniformGlobalScalePoolMachine.program_length,UniformGlobalCalendarPhaseDirectory.program_length,
  UniformGlobalCalendarFactorMerge.program_length,UniformGlobalCalendarUnionRows.program_length]



lemma code_10 : program[10]?=some (.branchLT 6773 6767 11 51) := rfl
lemma code_28 : program[28]?=some (.branchLT 6780 6774 30 29) := rfl
lemma code_29 : program[29]?=some (.branchLT 6780 6775 34 42) := rfl
lemma code_33 : program[33]?=some (.branchLT 6764 6774 36 42) := rfl
lemma code_34 : program[34]?=some (.natLiteral 6765 0) := rfl
lemma code_35 : program[35]?=some (.jump 36) := rfl
lemma code_41 : program[41]?=some (.jump 49) := rfl
lemma code_51 : program[51]?=some .halt := rfl

lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
lemma readEntry_code : BlockAt readEntry program 11 := by intro i hi;change i<17 at hi;interval_cases i <;> rfl
lemma phaseSetup_code : BlockAt phaseSetup program 30 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma factorSetup_code : BlockAt factorSetup program 36 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma rowsSetup_code : BlockAt rowsSetup program 42 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma rowsReturn_code : BlockAt rowsReturn program 47 := by intro i hi;change i<1 at hi;interval_cases i; rfl
lemma advance_code : BlockAt advance program 49 := by intro i hi;change i<1 at hi;interval_cases i; rfl

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
