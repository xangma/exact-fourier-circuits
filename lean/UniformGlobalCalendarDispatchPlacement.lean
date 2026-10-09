import UniformGlobalCalendarDispatch

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
noncomputable section

lemma embed_code_at (pre helper post : Program) (base ret : ℕ) (eq : pre.length=base) :
 CodeAt helper (pre++helper.map (relocate base ret)++post) base ret := by
 rw [←eq]
 exact embed_code pre helper post ret

lemma phasePrinter_code : CodeAt phasePrinter program 52 7 := by
 have h:=embed_code_at main phasePrinter
  (UniformGlobalScalePoolMachine.program.map (relocate 224 10)++
   UniformGlobalCalendarPhaseDirectory.program.map (relocate 235 33)++
   UniformGlobalCalendarFactorMerge.program.map (relocate 243 41)++
   UniformGlobalCalendarUnionRows.program.map (relocate 258 47)) 52 7 main_length
 simpa only [program,List.append_assoc] using h

lemma init_code : CodeAt UniformGlobalScalePoolMachine.program program 224 10 := by
 let pre:=main++phasePrinter.map (relocate 52 7)
 have size : pre.length=224 := by simp only [pre,List.length_append,List.length_map,main_length,phasePrinter_length]
 have h:=embed_code_at pre UniformGlobalScalePoolMachine.program
  (UniformGlobalCalendarPhaseDirectory.program.map (relocate 235 33)++
   UniformGlobalCalendarFactorMerge.program.map (relocate 243 41)++
   UniformGlobalCalendarUnionRows.program.map (relocate 258 47)) 224 10 size
 simpa only [pre,program,List.append_assoc] using h

lemma phase_code : CodeAt UniformGlobalCalendarPhaseDirectory.program program 235 33 := by
 let pre:=main++phasePrinter.map (relocate 52 7)++UniformGlobalScalePoolMachine.program.map (relocate 224 10)
 have size : pre.length=235 := by simp only [pre,List.length_append,List.length_map,main_length,phasePrinter_length,UniformGlobalScalePoolMachine.program_length]
 have h:=embed_code_at pre UniformGlobalCalendarPhaseDirectory.program
  (UniformGlobalCalendarFactorMerge.program.map (relocate 243 41)++
   UniformGlobalCalendarUnionRows.program.map (relocate 258 47)) 235 33 size
 simpa only [pre,program,List.append_assoc] using h

lemma factor_code : CodeAt UniformGlobalCalendarFactorMerge.program program 243 41 := by
 let pre:=main++phasePrinter.map (relocate 52 7)++UniformGlobalScalePoolMachine.program.map (relocate 224 10)++
  UniformGlobalCalendarPhaseDirectory.program.map (relocate 235 33)
 have size : pre.length=243 := by simp only [pre,List.length_append,List.length_map,main_length,phasePrinter_length,UniformGlobalScalePoolMachine.program_length,UniformGlobalCalendarPhaseDirectory.program_length]
 have h:=embed_code_at pre UniformGlobalCalendarFactorMerge.program
  (UniformGlobalCalendarUnionRows.program.map (relocate 258 47)) 243 41 size
 simpa only [pre,program,List.append_assoc] using h

lemma rows_code : CodeAt UniformGlobalCalendarUnionRows.program program 258 47 := by
 let pre:=main++phasePrinter.map (relocate 52 7)++UniformGlobalScalePoolMachine.program.map (relocate 224 10)++
  UniformGlobalCalendarPhaseDirectory.program.map (relocate 235 33)++UniformGlobalCalendarFactorMerge.program.map (relocate 243 41)
 have size : pre.length=258 := by simp only [pre,List.length_append,List.length_map,main_length,phasePrinter_length,UniformGlobalScalePoolMachine.program_length,UniformGlobalCalendarPhaseDirectory.program_length,UniformGlobalCalendarFactorMerge.program_length]
 have h:=embed_code_at pre UniformGlobalCalendarUnionRows.program [] 258 47 size
 simpa only [pre,program,List.append_assoc,List.append_nil] using h

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
