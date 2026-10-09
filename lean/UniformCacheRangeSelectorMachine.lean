import UniformGlobalCalendarSelectorLoop
import UniformBoundedAssembly
import UniformChunkRowTableMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace Selector
abbrev program:=UniformGlobalCalendarSelector.program
end Selector
/-- Read real forest counts, derive the ABI stride, and reset the actual output count. -/
def boot:List Op := [.literal 7100 0,.literal 7101 1,.literal 7102 2,
 .literal 7103 3,.literal 7104 4,.literal 7105 11,
 .mul 7110 6800 7103,.add 6700 6813 7110,.add 6700 6700 7104,
 .add 7110 7110 7105,.add 6701 7110 7100,
 .mul 7111 6800 7104,.add 7111 7111 7104,.add 7111 6810 7111,
 .getNat 6702 7111,.add 7111 7111 7101,.getNat 7107 7111,
 .add 6704 7050 7100,.literal 6705 0,.literal 7106 0,.add 7108 6810 7100]
def loadRange:List Op := [.getNat 6700 7108,.add 7112 7108 7101,
 .getNat 6702 7112,.add 6701 7110 7100]
def advance:List Op := [.add 7106 7106 7101,.add 7108 7108 7102]
def beforeLoop:Program := boot.map Op.code++Selector.program.map (relocate 21 51)
def beforeNode:Program := beforeLoop++[.branchLT 7106 7107 52 89]++loadRange.map Op.code
def program:Program := beforeNode++Selector.program.map (relocate 56 86)++advance.map Op.code++[.jump 51,.halt]
lemma program_length:program.length=90:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<21 at hi;interval_cases i <;>rfl
lemma load_code:BlockAt loadRange program 52:=by intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma advance_code:BlockAt advance program 86:=by intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma rectangle_code:CodeAt Selector.program program 21 51:=by
 have eq:program=boot.map Op.code++Selector.program.map (relocate 21 51)++
  ([.branchLT 7106 7107 52 89]++loadRange.map Op.code++Selector.program.map (relocate 56 86)++
   advance.map Op.code++[.jump 51,.halt]):=by
  simp only[program,beforeNode,beforeLoop,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code _ _ _ 21 51 rfl
lemma node_code:CodeAt Selector.program program 56 86:=
 UniformChunkRowTableMachine.segment_code beforeNode (advance.map Op.code++[.jump 51,.halt]) _ 56 86 rfl
lemma code_51:program[51]?=some (.branchLT 7106 7107 52 89):=rfl
lemma code_88:program[88]?=some (.jump 51):=rfl
lemma code_89:program[89]?=some .halt:=rfl
end ExactFourierCircuits.UniformCacheRangeSelector
