import UniformCanonicalSeedChunkPreparation
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


def fixtureHeaders : List UniformTensorMonomialMachine.Op :=
 [.literal 1120 0,.literal 1122 1,.literal 1123 1,.literal 1124 1,.literal 1125 0,
  .literal 1126 1,.literal 1224 0,.literal 1238 0,.literal 1239 0]++
 ([1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1220,1221,1222,1223,
   1230,1231,1232,1233,1234,1235,1236,1237].map (fun q=>.literal q (q+17)))
def startupHeader : Program :=
 UniformAllAxisSeedPreparation.fullProgram.map (UniformAssembly.relocate 0 935)++
 fixtureHeaders.map UniformTensorMonomialMachine.Op.code++
 UniformCanonicalSeedChunkPreparation.headerProgram.map (UniformAssembly.relocate 967 998)++[.halt]
example : fixtureHeaders.length=32 := rfl
example : startupHeader.length=999 := by
 simp [startupHeader,UniformAllAxisSeedPreparation.fullProgram_length,
  show fixtureHeaders.length=32 from rfl,UniformCanonicalSeedChunkPreparation.headerProgram_length]

#eval IO.FS.writeFile "../logs/uniform-bytecode/canonical-seed-chunk/programs.json" (Json.compress (Json.mkObj [
 ("canonicalSeedChunk",.arr (UniformCanonicalSeedChunkPreparation.program.map insJson).toArray),
 ("canonicalHeader",.arr (UniformCanonicalSeedChunkPreparation.headerProgram.map insJson).toArray),
 ("seedChunk",.arr (UniformSeedChunkPreparation.program.map insJson).toArray),
 ("seedStartup",.arr (UniformAllAxisSeedPreparation.fullProgram.map insJson).toArray),
 ("startupHeader",.arr (startupHeader.map insJson).toArray)]))
namespace Spec
open UniformToeplitzCrossDAG UniformConvolutionTopologyMachine
def rowJson (r : Row) : Json:=toJson [r.opcode,r.left,r.right,r.kind,r.payload]
#eval IO.FS.writeFile "../logs/uniform-bytecode/canonical-seed-chunk/spec.json" (Json.compress (Json.mkObj [
 ("K",toJson UniformSeedChunkPreparation.unitSeed.exponent),
 ("G",toJson UniformSeedChunkPreparation.unitSeed.gates),
 ("capacity",toJson (UniformSeedChunkPreparation.unitSeed.gates+2)),
 ("rows",.arr ((UniformToeplitzCrossTopologyMachine.crossRows 2 1 1).map rowJson).toArray)]))
end Spec
example : UniformCanonicalSeedChunkPreparation.program.length=1317 :=
 UniformCanonicalSeedChunkPreparation.program_length
example : UniformCanonicalSeedChunkPreparation.headerProgram.length=31 :=
 UniformCanonicalSeedChunkPreparation.headerProgram_length
