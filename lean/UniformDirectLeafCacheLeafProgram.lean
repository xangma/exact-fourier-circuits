import UniformDirectLeafCacheProducedSource
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLeafProgram
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
/-- Set the actual82 original-directory argument, print both orientations,
consume the chosen real bank with303, then halt. -/
def setup:List Op:=[.literal 6612 0,.add 5601 6601 6612]
def program:Program:=setup.map Op.code++
 UniformStoredDirectLeafOrientations.program.map (relocate 2 84)++
 UniformDirectLeafCacheLoopProgram.program.map (relocate 84 387)++[.halt]
lemma setup_length:setup.length=2:=rfl
lemma program_length:program.length=388:=by
 simp only[program,List.length_append,List.length_map,setup_length,
  UniformStoredDirectLeafOrientations.program_length,UniformDirectLeafCacheLoopProgram.program_length];rfl
lemma setup_code:BlockAt setup program 0:=by intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma orientations_code:CodeAt UniformStoredDirectLeafOrientations.program program 2 84:=by
 exact UniformRankCrossPreparationMachine.segment_code (setup.map Op.code)
  (UniformDirectLeafCacheLoopProgram.program.map (relocate 84 387)++[.halt])
  UniformStoredDirectLeafOrientations.program 2 84 rfl
lemma loop_code:CodeAt UniformDirectLeafCacheLoopProgram.program program 84 387:=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (setup.map Op.code++UniformStoredDirectLeafOrientations.program.map (relocate 2 84))
  [.halt] UniformDirectLeafCacheLoopProgram.program 84 387
  (by simp only[List.length_append,List.length_map,setup_length,UniformStoredDirectLeafOrientations.program_length])
 simpa only[program,List.append_assoc] using h
lemma halt_at:program[387]?=some .halt:=by
 have len:(setup.map Op.code++UniformStoredDirectLeafOrientations.program.map (relocate 2 84)++
  UniformDirectLeafCacheLoopProgram.program.map (relocate 84 387)).length=387:=by
  simp only[List.length_append,List.length_map,setup_length,UniformStoredDirectLeafOrientations.program_length,
   UniformDirectLeafCacheLoopProgram.program_length]
 have eq:program=(setup.map Op.code++UniformStoredDirectLeafOrientations.program.map (relocate 2 84)++
  UniformDirectLeafCacheLoopProgram.program.map (relocate 84 387))++[.halt]:=by simp only[program,List.append_assoc]
 rw[eq,List.getElem?_append_right (by omega),len];rfl
end
end ExactFourierCircuits.UniformDirectLeafCacheLeafProgram
