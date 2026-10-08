import UniformHighDataPackingPreparation
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


#eval IO.FS.createDirAll "../logs/uniform-bytecode/high-data-packing"
#eval IO.FS.writeFile "../logs/uniform-bytecode/high-data-packing/programs.json" (Json.compress (Json.mkObj [
 ("highData",.arr (UniformHighDataPackingPreparation.program.map insJson).toArray),
 ("copy",.arr (UniformScalarCopyMachine.program.map insJson).toArray),
 ("seedChunkPacking",.arr (UniformSeedChunkPackingPreparation.program.map insJson).toArray),
 ("continuation",.arr (UniformSeedChunkPackingPreparation.continuation.map insJson).toArray),
 ("seedChunk",.arr (UniformSeedChunkPreparation.program.map insJson).toArray),
 ("height",.arr (UniformSeedHeightPreparation.program.map insJson).toArray),
 ("chunk",.arr (UniformChunkMatchingPreparation.program.map insJson).toArray),
 ("packing",.arr (UniformSectorPackingMachine.program.map insJson).toArray)]))
namespace Spec
open UniformToeplitzCrossDAG UniformConvolutionTopologyMachine
def rowJson (r : Row) : Json:=toJson [r.opcode,r.left,r.right,r.kind,r.payload]
#eval IO.FS.writeFile "../logs/uniform-bytecode/high-data-packing/spec.json" (Json.compress (Json.mkObj [
 ("K",toJson UniformSeedChunkPreparation.unitSeed.exponent),
 ("G",toJson UniformSeedChunkPreparation.unitSeed.gates),
 ("capacity",toJson (UniformSeedChunkPreparation.unitSeed.gates+2)),
 ("rows",.arr ((UniformToeplitzCrossTopologyMachine.crossRows 2 1 1).map rowJson).toArray)]))
end Spec
example:UniformSeedChunkPackingPreparation.program.length=1438:=UniformSeedChunkPackingPreparation.program_length
example:UniformSeedChunkPackingPreparation.continuation.length=152:=UniformSeedChunkPackingPreparation.continuation_length

example : UniformHighDataPackingPreparation.program.length=167 := UniformHighDataPackingPreparation.program_length
