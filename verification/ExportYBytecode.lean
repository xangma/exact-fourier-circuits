import UniformPreparedYTranslationMachine
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


#eval IO.FS.writeFile "../logs/uniform-bytecode/y-translation/programs.json"
 (Json.compress (Json.mkObj [
 ("preparedY",.arr (UniformPreparedYTranslationMachine.program.map insJson).toArray),
 ("translation",.arr (UniformXorTranslationMachine.program.map insJson).toArray),
 ("mask",.arr (UniformRepeatedMaskMachine.program.map insJson).toArray),
 ("blockXor",.arr (UniformBlockXorMachine.program.map insJson).toArray)]))

#eval IO.FS.writeFile "../logs/uniform-bytecode/y-translation/spec.json"
 (Json.compress (.arr (([(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(4,1)] : List (Nat×Nat)).map (fun p=>
 Json.mkObj [("q",toJson p.1),("width",toJson p.2),
 ("runtime",toJson (UniformPreparedYTranslationMachine.runtime p.1 p.2))])).toArray))
example : UniformPreparedYTranslationMachine.program.length=116 := UniformPreparedYTranslationMachine.program_length
example : UniformRepeatedMaskMachine.program.length=16 := UniformRepeatedMaskMachine.program_length
example : UniformBlockXorMachine.program.length=22 := UniformBlockXorMachine.program_length
example : UniformXorTranslationMachine.program.length=52 := UniformXorTranslationMachine.program_length
