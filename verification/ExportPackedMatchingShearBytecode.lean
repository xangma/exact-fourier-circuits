import UniformPackedMatchingShearMachine
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine Lean
def natOpName : NatOp→String
 | .add=>"add" | .sub=>"sub" | .mul=>"mul" | .div=>"div" | .mod=>"mod"
def fieldOpName : FieldOp→String
 | .add=>"fadd" | .sub=>"fsub" | .mul=>"fmul" | .div=>"fdiv"
def insJson : Instruction→Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary op d l r=>.arr #[.str (natOpName op),toJson d,toJson l,toJson r]
 | .loadNat d a=>.arr #[.str "getnat",toJson d,toJson a]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .scalarLiteral d q=>.arr #[.str "rat",toJson d,toJson q.num,toJson q.den]
 | .fieldBinary op d l r=>.arr #[.str (fieldOpName op),toJson d,toJson l,toJson r]
 | .loadScalar d a=>.arr #[.str "getscalar",toJson d,toJson a]
 | .storeScalar a r=>.arr #[.str "putscalar",toJson a,toJson r]
 | .branchLT l r y n=>.arr #[.str "branch",toJson l,toJson r,toJson y,toJson n]
 | .jump j=>.arr #[.str "jump",toJson j]
 | .halt=>.arr #[.str "halt"]
 | .length d=>.arr #[.str "length",toJson d]
 | .root d r=>.arr #[.str "root",toJson d,toJson r]
 | .input d j=>.arr #[.str "input",toJson d,toJson j]
 | .output j r=>.arr #[.str "output",toJson j,toJson r]


#eval IO.FS.createDirAll "../logs/uniform-bytecode/packed-matching-shear"
#eval IO.FS.writeFile "../logs/uniform-bytecode/packed-matching-shear/programs.json" (Json.compress (Json.mkObj [
 ("joined",.arr (UniformPackedMatchingShearMachine.program.map insJson).toArray),
 ("rowLoader",.arr (UniformMatchingConjugateLoadMachine.rowProgram.map insJson).toArray),
 ("sixC",.arr (UniformZeroFreePairShearMachine.program.map insJson).toArray),
 ("scatter",.arr (UniformScalarScatterMachine.program.map insJson).toArray)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/packed-matching-shear/spec.json" (Json.compress (Json.mkObj [
 ("pairs",toJson ([0,1,2,3,6]:List ℕ)),("tails",toJson ([0,1,3]:List ℕ)),
 ("K",toJson ([0,1,3]:List ℕ)),("fields",toJson ([4,8,12]:List ℕ))]))
example : UniformPackedMatchingShearMachine.program.length=422 := UniformPackedMatchingShearMachine.program_length
