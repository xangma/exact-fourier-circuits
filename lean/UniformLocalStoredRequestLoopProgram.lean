import UniformLocalRequestFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAssembly
namespace I
abbrev program:=UniformLocalRequestCursorMachine.program
end I
namespace C
abbrev program:=UniformLocalStoredRectanglePreparation.program
end C
namespace A
abbrev program:=UniformLocalRequestAdvanceMachine.program
end A

/-- A single fixed loop uses the actual produced request count and advances
the measured cache ends. The axis copy is a charged instruction on every pass. -/
def beforeCache:Program:=I.program.map (relocate 0 21)++
 [.branchLT 6174 6179 22 3775,.natLiteral 6190 0,.natBinary .add 4200 6906 6190]
def beforeAdvance:Program:=beforeCache++C.program.map (relocate 24 3762)
def program:Program:=beforeAdvance++A.program.map (relocate 3762 21)++[.halt]
lemma beforeCache_length:beforeCache.length=24:=by
 simp only [beforeCache,List.length_append,List.length_map,UniformLocalRequestCursorMachine.program_length]
 rfl
lemma beforeAdvance_length:beforeAdvance.length=3762:=by
 simp only [beforeAdvance,List.length_append,List.length_map,beforeCache_length,
  UniformLocalStoredRectanglePreparation.program_length]
lemma program_length:program.length=3776:=by
 simp only [program,List.length_append,List.length_map,beforeAdvance_length,
  UniformLocalRequestAdvanceMachine.program_length,List.length_singleton]

attribute [local irreducible] UniformLocalRequestCursorMachine.program
 UniformLocalStoredRectanglePreparation.program UniformLocalRequestAdvanceMachine.program
lemma cursor_code:CodeAt I.program program 0 21:=by
 let rest:Program:=[.branchLT 6174 6179 22 3775,.natLiteral 6190 0,.natBinary .add 4200 6906 6190]++
  C.program.map (relocate 24 3762)++A.program.map (relocate 3762 21)++[.halt]
 have eq:program=[]++I.program.map (relocate 0 21)++rest:=by
  simp only [program,beforeAdvance,beforeCache,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code [] rest _ 0 21 rfl
lemma cache_code:CodeAt C.program program 24 3762:=by
 have eq:program=beforeCache++C.program.map (relocate 24 3762)++
  (A.program.map (relocate 3762 21)++[.halt]):=by
  simp only [program,beforeAdvance,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeCache _ _ 24 3762 beforeCache_length
lemma advance_code:CodeAt A.program program 3762 21:=
 UniformChunkRowTableMachine.segment_code beforeAdvance [.halt] _ 3762 21 beforeAdvance_length
lemma branch_at:program[21]?=some (.branchLT 6174 6179 22 3775):=by
 have append:program=I.program.map (relocate 0 21)++
  ([.branchLT 6174 6179 22 3775,.natLiteral 6190 0,.natBinary .add 4200 6906 6190]++
   C.program.map (relocate 24 3762)++A.program.map (relocate 3762 21)++[.halt]):=by
  simp only [program,beforeAdvance,beforeCache,List.append_assoc]
 rw [append,List.getElem?_append_right (by
  simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];omega)]
 simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];rfl
lemma zero_at:program[22]?=some (.natLiteral 6190 0):=by
 have append:program=I.program.map (relocate 0 21)++
  ([.branchLT 6174 6179 22 3775,.natLiteral 6190 0,.natBinary .add 4200 6906 6190]++
   C.program.map (relocate 24 3762)++A.program.map (relocate 3762 21)++[.halt]):=by
  simp only [program,beforeAdvance,beforeCache,List.append_assoc]
 rw [append,List.getElem?_append_right (by
  simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];omega)]
 simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];rfl
lemma axis_at:program[23]?=some (.natBinary .add 4200 6906 6190):=by
 have append:program=I.program.map (relocate 0 21)++
  ([.branchLT 6174 6179 22 3775,.natLiteral 6190 0,.natBinary .add 4200 6906 6190]++
   C.program.map (relocate 24 3762)++A.program.map (relocate 3762 21)++[.halt]):=by
  simp only [program,beforeAdvance,beforeCache,List.append_assoc]
 rw [append,List.getElem?_append_right (by
  simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];omega)]
 simp only [List.length_map,UniformLocalRequestCursorMachine.program_length];rfl
lemma halt_at:program[3775]?=some .halt:=by
 rw [program,List.getElem?_append_right (by
  simp only [List.length_append,List.length_map,beforeAdvance_length,
   UniformLocalRequestAdvanceMachine.program_length];omega)]
 simp only [List.length_append,List.length_map,beforeAdvance_length,
  UniformLocalRequestAdvanceMachine.program_length];rfl
end ExactFourierCircuits.UniformLocalStoredRequestLoop
