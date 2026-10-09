import UniformDirectLeafCacheFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopProgram
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Reads stored width and the real radix directory, computes the exact
record count, and computes both persistent-cache strides. -/
def bootLeft : List Op := [.literal 6620 0,.literal 6621 1,.literal 6622 2,.literal 6623 4,
 .literal 6624 9,.literal 6625 3,.literal 6626 11,.getNat 6627 5600,
 .sub 6628 6627 6621,.mul 6628 6627 6628]
def bootRight : List Op := [.add 6628 6628 6627,
 .literal 6629 0,.literal 6630 28,.add 6631 6601 6621,.getNat 6632 6631,
 .mul 6633 6632 6624,.mul 6634 6632 6625,.add 6634 6634 6626]
def boot : Program := bootLeft.map Op.code++[.natBinary .div 6628 6628 6622]++bootRight.map Op.code
def choose : Program := [.branchLT 6611 6621 20 22,.natBinary .add 6600 5602 6620,
 .jump 23,.natBinary .add 6600 5603 6620]
def readKind : List Op := [.getNat 6635 6600]
def scaleTime : List Op := [.add 6610 6610 6621]
def shearTime : List Op := [.add 6610 6610 6630]
def advance : List Op := [.add 6603 6603 6633,.add 6605 6605 6634,
 .add 6606 6606 6634,.add 6607 6607 6634,.add 6608 6608 6634,
 .add 6609 6609 6634,.add 6600 6600 6623,.add 6629 6629 6621]
def program : Program := boot++choose++[.branchLT 6629 6628 24 302]++
 UniformDirectLeafCacheProgram.program.map (relocate 24 288)++readKind.map Op.code++
 [.branchLT 6635 6621 290 292]++scaleTime.map Op.code++[.jump 293]++shearTime.map Op.code++
 advance.map Op.code++[.jump 23,.halt]
lemma bootLeft_length : bootLeft.length=10 := rfl
lemma bootRight_length : bootRight.length=8 := rfl
lemma boot_length : boot.length=19 := rfl
lemma choose_length : choose.length=4 := rfl
lemma advance_length : advance.length=8 := rfl
lemma program_length : program.length=303 := by
 simp only[program,List.length_append,List.length_map,boot_length,choose_length,
  UniformDirectLeafCacheProgram.program_length];rfl
lemma bootLeft_code : BlockAt bootLeft program 0 := by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma bootRight_code : BlockAt bootRight program 11 := by
 intro i hi;change i<8 at hi;interval_cases i <;>rfl
lemma boot_div : program[10]?=some (.natBinary .div 6628 6628 6622) := rfl
lemma descriptor_code : CodeAt UniformDirectLeafCacheProgram.program program 24 288 := by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (boot++choose++[.branchLT 6629 6628 24 302])
  (readKind.map Op.code++[.branchLT 6635 6621 290 292]++scaleTime.map Op.code++
   [.jump 293]++shearTime.map Op.code++advance.map Op.code++[.jump 23,.halt])
  UniformDirectLeafCacheProgram.program 24 288
  (by simp only[List.length_append,boot_length,choose_length];rfl)
 simpa only[program,List.append_assoc] using h
lemma choose_branch : program[19]?=some (.branchLT 6611 6621 20 22) := rfl
lemma choose_forward : program[20]?=some (.natBinary .add 6600 5602 6620) := rfl
lemma choose_jump : program[21]?=some (.jump 23) := rfl
lemma choose_transpose : program[22]?=some (.natBinary .add 6600 5603 6620) := rfl
lemma branch_at : program[23]?=some (.branchLT 6629 6628 24 302) := rfl
lemma suffix_code (i:ℕ) (hi:i<15) : program[288+i]?=
 (readKind.map Op.code++[.branchLT 6635 6621 290 292]++scaleTime.map Op.code++
 [.jump 293]++shearTime.map Op.code++advance.map Op.code++[.jump 23,.halt])[i]? := by
 have eq:program=(boot++choose++[.branchLT 6629 6628 24 302]++
  UniformDirectLeafCacheProgram.program.map (relocate 24 288))++
  (readKind.map Op.code++[.branchLT 6635 6621 290 292]++scaleTime.map Op.code++
   [.jump 293]++shearTime.map Op.code++advance.map Op.code++[.jump 23,.halt]) := by
  simp only[program,List.append_assoc]
 have len:(boot++choose++[Instruction.branchLT 6629 6628 24 302]++
  UniformDirectLeafCacheProgram.program.map (relocate 24 288)).length=288 := by
  simp only[List.length_append,List.length_map,boot_length,choose_length,
   UniformDirectLeafCacheProgram.program_length];rfl
 rw[eq,List.getElem?_append_right (by rw[len];omega),len]
 simp only[Nat.add_sub_cancel_left]
lemma kind_code : BlockAt readKind program 288 := by
 intro i hi;change i<1 at hi
 have iz:i=0:=by omega
 subst i;exact suffix_code 0 (by omega)
lemma time_branch : program[289]?=some (.branchLT 6635 6621 290 292) := suffix_code 1 (by omega)
lemma scale_code : BlockAt scaleTime program 290 := by
 intro i hi;change i<1 at hi;have iz:i=0:=by omega
 subst i;exact suffix_code 2 (by omega)
lemma time_jump : program[291]?=some (.jump 293) := suffix_code 3 (by omega)
lemma shear_code : BlockAt shearTime program 292 := by
 intro i hi;change i<1 at hi;have iz:i=0:=by omega
 subst i;exact suffix_code 4 (by omega)
lemma advance_code : BlockAt advance program 293 := by
 intro i hi;change i<8 at hi
 have h:=suffix_code (5+i) (by omega)
 interval_cases i <;>exact h
lemma loop_jump : program[301]?=some (.jump 23) := suffix_code 13 (by omega)
lemma halt_at : program[302]?=some .halt := suffix_code 14 (by omega)

end
end ExactFourierCircuits.UniformDirectLeafCacheLoopProgram
