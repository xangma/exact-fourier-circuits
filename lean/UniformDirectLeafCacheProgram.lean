import UniformDirectLeafFactorTail
import UniformMatchingSlotDirectoryFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheProgram
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Physical descriptor decode and all helper arguments are charged. -/
def install : List Op := [.add 1620 6647 6647,.add 1621 6647 6647,
 .add 1622 6643 6647,.add 1623 6652 6647,.add 4330 6603 6647,
 .add 4331 6645 6647,.add 2140 6604 6647,.add 2141 6647 6647,
 .add 6650 6604 6647,.putNat 6650 6641,.add 6650 6650 6648,
 .putNat 6650 6642,.add 6650 6650 6648,.putNat 6650 6643,
 .add 5840 6610 6647,.add 5841 6645 6647,.add 5842 6603 6647,
 .add 5843 6605 6647,.add 5844 6606 6647,.add 5845 6607 6647,
 .add 5846 6608 6647,.add 5847 6604 6647,.add 5848 6609 6647]
def scale : List Op := [.getScalar 126 6643,.add 6650 6603 6641,
 .putScalar 6650 126,.literal 894 0,.literal 5849 1]
def choose : Program := [.branchLT 6640 6648 54 60]++scale.map Op.code++
 [.jump 183,.natLiteral 894 1,.natLiteral 5849 0,.jump 92]
def program : Program := UniformDirectLeafCacheReader.read.map Op.code++install.map Op.code++
 UniformGlobalScalePoolMachine.program.map (relocate 42 53)++choose++
 UniformGlobalMatchingScaleMachine.rowProgram.map (relocate 63 183)++
 UniformLocalMatchingSlotDirectory.program.map (relocate 183 263)++[.halt]
lemma install_length : install.length=23 := rfl
lemma scale_length : scale.length=5 := rfl
lemma choose_length : choose.length=10 := rfl
lemma program_length : program.length=264 := by
 simp only [program,List.length_append,List.length_map,UniformDirectLeafCacheReader.read_length,
  install_length,UniformGlobalScalePoolMachine.program_length,choose_length,
  UniformGlobalMatchingScaleMachine.rowProgram_length,UniformLocalMatchingSlotDirectory.program_length];rfl
lemma read_code : BlockAt UniformDirectLeafCacheReader.read program 0 := by
 intro i hi;change i<19 at hi;interval_cases i <;>rfl
lemma install_code : BlockAt install program 19 := by
 intro i hi;change i<23 at hi;interval_cases i <;>rfl
lemma scale_code : BlockAt scale program 54 := by
 intro i hi;change i<5 at hi;interval_cases i <;>rfl
lemma pool_code : CodeAt UniformGlobalScalePoolMachine.program program 42 53 := by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (UniformDirectLeafCacheReader.read.map Op.code++install.map Op.code)
  (choose++UniformGlobalMatchingScaleMachine.rowProgram.map (relocate 63 183)++
   UniformLocalMatchingSlotDirectory.program.map (relocate 183 263)++[.halt])
  UniformGlobalScalePoolMachine.program 42 53
  (by simp only[List.length_append,List.length_map,UniformDirectLeafCacheReader.read_length,install_length])
 simpa only [program,List.append_assoc] using h
lemma factor_code : CodeAt UniformGlobalMatchingScaleMachine.rowProgram program 63 183 := by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (UniformDirectLeafCacheReader.read.map Op.code++install.map Op.code++
   UniformGlobalScalePoolMachine.program.map (relocate 42 53)++choose)
  (UniformLocalMatchingSlotDirectory.program.map (relocate 183 263)++[.halt])
  UniformGlobalMatchingScaleMachine.rowProgram 63 183
  (by simp only[List.length_append,List.length_map,UniformDirectLeafCacheReader.read_length,
    install_length,UniformGlobalScalePoolMachine.program_length,choose_length])
 simpa only [program,List.append_assoc] using h
lemma directory_code : CodeAt UniformLocalMatchingSlotDirectory.program program 183 263 := by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (UniformDirectLeafCacheReader.read.map Op.code++install.map Op.code++
   UniformGlobalScalePoolMachine.program.map (relocate 42 53)++choose++
   UniformGlobalMatchingScaleMachine.rowProgram.map (relocate 63 183)) [.halt]
  UniformLocalMatchingSlotDirectory.program 183 263
  (by simp only[List.length_append,List.length_map,UniformDirectLeafCacheReader.read_length,
    install_length,UniformGlobalScalePoolMachine.program_length,choose_length,
    UniformGlobalMatchingScaleMachine.rowProgram_length])
 simpa only [program,List.append_assoc] using h
lemma branch_at : program[53]?=some (.branchLT 6640 6648 54 60) := rfl
lemma scale_jump : program[59]?=some (.jump 183) := rfl
lemma shear_count : program[60]?=some (.natLiteral 894 1) := rfl
lemma shear_kind : program[61]?=some (.natLiteral 5849 0) := rfl
lemma shear_jump : program[62]?=some (.jump 92) := rfl
lemma halt_at : program[263]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
  UniformDirectLeafCacheReader.read_length,install_length,UniformGlobalScalePoolMachine.program_length,
  choose_length,UniformGlobalMatchingScaleMachine.rowProgram_length,
  UniformLocalMatchingSlotDirectory.program_length];omega)]
 simp only [List.length_append,List.length_map,UniformDirectLeafCacheReader.read_length,
  install_length,UniformGlobalScalePoolMachine.program_length,choose_length,
  UniformGlobalMatchingScaleMachine.rowProgram_length,UniformLocalMatchingSlotDirectory.program_length];rfl
end
end ExactFourierCircuits.UniformDirectLeafCacheProgram
