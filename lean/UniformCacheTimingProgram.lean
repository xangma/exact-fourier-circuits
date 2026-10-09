import UniformCacheRowDurationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingProgram
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op BlockAt)

def boot : List Op := [.literal 6508 0,
 .literal 6509 1,
 .literal 6510 2,
 .literal 6511 3,
 .literal 6512 5,
 .literal 6513 6,
 .literal 6514 7,
 .literal 6515 14,
 .literal 6505 0,
 .add 6506 4281 6508,
 .sub 6507 4282 6501]
def initSetup : List Op := [.literal 6516 0]
def initCell : List Op := [.add 6518 6502 6516,
 .putNat 6518 6508,
 .add 6516 6516 6509]
def reverseSetup : List Op := [.add 6516 6506 6508]
def loadReverse : List Op := [.sub 6516 6516 6509,
 .mul 6518 6516 6514,
 .add 6518 6500 6518,
 .getNat 6519 6518,
 .add 6518 6518 6510,
 .getNat 6520 6518,
 .add 6518 6518 6509,
 .getNat 6521 6518,
 .add 6518 6518 6510,
 .getNat 6522 6518,
 .add 6518 6518 6509,
 .getNat 6523 6518,
 .add 6524 6502 6516,
 .getNat 6527 6524,
 .add 6525 6503 6516,
 .literal 6528 0,
 .sub 6529 6522 6501]
def rowSetup : List Op := [.literal 6530 0]
def rowRead : List Op := [.mul 6531 6530 6514,
 .add 6531 6522 6531,
 .add 6531 6531 6510,
 .getNat 6540 6531,
 .add 6531 6531 6509,
 .getNat 6541 6531,
 .add 6535 6504 6529,
 .putNat 6535 6528]
def rowAdvance : List Op := [.add 6528 6528 6542,
 .add 6529 6529 6509,
 .add 6530 6530 6509]
def direct : List Op := [.sub 6526 6519 6509,
 .mul 6526 6519 6526,
 .mul 6526 6526 6515,
 .add 6526 6519 6526]
def split : List Op := [.add 6526 6527 6528]
def storeDuration : List Op := [.putNat 6524 6526,
 .putNat 6525 6528]
def parentRead : List Op := [.add 6535 6502 6521,
 .getNat 6536 6535]
def parentWrite : List Op := [.putNat 6535 6526]
def forwardSetup : List Op := [.literal 6516 0]
def loadForward : List Op := [.mul 6518 6516 6514,
 .add 6518 6500 6518,
 .add 6518 6518 6511,
 .getNat 6521 6518,
 .add 6518 6518 6510,
 .getNat 6522 6518,
 .add 6518 6518 6509,
 .getNat 6523 6518,
 .add 6524 6502 6516,
 .getNat 6526 6524,
 .add 6525 6503 6516,
 .getNat 6528 6525]
def parentStart : List Op := [.add 6535 6503 6521,
 .getNat 6533 6535]
def rootStart : List Op := [.add 6533 6505 6508]
def startSetup : List Op := [.add 6534 6533 6526,
 .sub 6534 6534 6528,
 .sub 6529 6522 6501]
def startRowSetup : List Op := [.literal 6530 0]
def startRow : List Op := [.add 6535 6504 6529,
 .getNat 6532 6535,
 .add 6532 6534 6532,
 .putNat 6535 6532,
 .add 6529 6529 6509,
 .add 6530 6530 6509]
def storeStart : List Op := [.putNat 6525 6533,
 .add 6516 6516 6509]

/-- Three literal passes over the real stored directory. The first initializes
durations; the second propagates child maxima in reverse preorder; the third
converts temporary correction totals and row prefixes into absolute starts. -/
def program : Program :=
 boot.map Op.code ++
 [.natBinary .div 6507 6507 6514] ++
 initSetup.map Op.code ++
 [.branchLT 6516 6506 14 18] ++
 initCell.map Op.code ++
 [.jump 13] ++
 reverseSetup.map Op.code ++
 [.branchLT 6508 6516 20 86] ++
 loadReverse.map Op.code ++
 [.natBinary .div 6529 6529 6514] ++
 rowSetup.map Op.code ++
 [.branchLT 6519 6510 72 40] ++
 [.branchLT 6508 6520 41 72] ++
 [.branchLT 6530 6523 42 77] ++
 rowRead.map Op.code ++
 UniformCacheRowDurationMachine.program.map (relocate 50 68) ++
 rowAdvance.map Op.code ++
 [.jump 41] ++
 direct.map Op.code ++
 [.jump 78] ++
 split.map Op.code ++
 storeDuration.map Op.code ++
 [.branchLT 6508 6516 81 19] ++
 parentRead.map Op.code ++
 [.branchLT 6536 6526 84 19] ++
 parentWrite.map Op.code ++
 [.jump 19] ++
 forwardSetup.map Op.code ++
 [.branchLT 6516 6506 88 121] ++
 loadForward.map Op.code ++
 [.branchLT 6508 6516 101 104] ++
 parentStart.map Op.code ++
 [.jump 105] ++
 rootStart.map Op.code ++
 startSetup.map Op.code ++
 [.natBinary .div 6529 6529 6514] ++
 startRowSetup.map Op.code ++
 [.branchLT 6530 6523 111 118] ++
 startRow.map Op.code ++
 [.jump 110] ++
 storeStart.map Op.code ++
 [.jump 87] ++
 [.halt]
lemma program_length : program.length=122 := by
 simp only [program,List.length_append,List.length_map,UniformCacheRowDurationMachine.program_length]
 rfl

lemma boot_code : BlockAt boot program 0 := by
 intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma code_11 : program[11]?=some (.natBinary .div 6507 6507 6514) := rfl
lemma initSetup_code : BlockAt initSetup program 12 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_13 : program[13]?=some (.branchLT 6516 6506 14 18) := rfl
lemma initCell_code : BlockAt initCell program 14 := by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma code_17 : program[17]?=some (.jump 13) := rfl
lemma reverseSetup_code : BlockAt reverseSetup program 18 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_19 : program[19]?=some (.branchLT 6508 6516 20 86) := rfl
lemma loadReverse_code : BlockAt loadReverse program 20 := by
 intro i hi;change i<17 at hi;interval_cases i <;>rfl
lemma code_37 : program[37]?=some (.natBinary .div 6529 6529 6514) := rfl
lemma rowSetup_code : BlockAt rowSetup program 38 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_39 : program[39]?=some (.branchLT 6519 6510 72 40) := rfl
lemma code_40 : program[40]?=some (.branchLT 6508 6520 41 72) := rfl
lemma code_41 : program[41]?=some (.branchLT 6530 6523 42 77) := rfl
lemma rowRead_code : BlockAt rowRead program 42 := by
 intro i hi;change i<8 at hi;interval_cases i <;>rfl
lemma row_code : CodeAt UniformCacheRowDurationMachine.program program 50 68 := by
 intro i hi;rw [UniformCacheRowDurationMachine.program_length] at hi;interval_cases i <;>rfl
lemma rowAdvance_code : BlockAt rowAdvance program 68 := by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma code_71 : program[71]?=some (.jump 41) := rfl
lemma direct_code : BlockAt direct program 72 := by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma code_76 : program[76]?=some (.jump 78) := rfl
lemma split_code : BlockAt split program 77 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma storeDuration_code : BlockAt storeDuration program 78 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma code_80 : program[80]?=some (.branchLT 6508 6516 81 19) := rfl
lemma parentRead_code : BlockAt parentRead program 81 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma code_83 : program[83]?=some (.branchLT 6536 6526 84 19) := rfl
lemma parentWrite_code : BlockAt parentWrite program 84 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_85 : program[85]?=some (.jump 19) := rfl
lemma forwardSetup_code : BlockAt forwardSetup program 86 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_87 : program[87]?=some (.branchLT 6516 6506 88 121) := rfl
lemma loadForward_code : BlockAt loadForward program 88 := by
 intro i hi;change i<12 at hi;interval_cases i <;>rfl
lemma code_100 : program[100]?=some (.branchLT 6508 6516 101 104) := rfl
lemma parentStart_code : BlockAt parentStart program 101 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma code_103 : program[103]?=some (.jump 105) := rfl
lemma rootStart_code : BlockAt rootStart program 104 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma startSetup_code : BlockAt startSetup program 105 := by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma code_108 : program[108]?=some (.natBinary .div 6529 6529 6514) := rfl
lemma startRowSetup_code : BlockAt startRowSetup program 109 := by
 intro i hi
 change i<1 at hi
 have eq:i=0:=by omega
 subst i
 rfl
lemma code_110 : program[110]?=some (.branchLT 6530 6523 111 118) := rfl
lemma startRow_code : BlockAt startRow program 111 := by
 intro i hi;change i<6 at hi;interval_cases i <;>rfl
lemma code_117 : program[117]?=some (.jump 110) := rfl
lemma storeStart_code : BlockAt storeStart program 118 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma code_120 : program[120]?=some (.jump 87) := rfl
lemma code_121 : program[121]?=some (.halt) := rfl

end ExactFourierCircuits.UniformCacheTimingProgram
