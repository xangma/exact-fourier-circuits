import UniformRecursivePaddingControl
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformAssembly Lean
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




-- These are the same proved slices at finite addresses, plus diagnostic
-- continuation90→Next79 and halt89. No actual SavingProgram is evaluated.
namespace C
export UniformRecursivePaddingControl (initOps testOps patchOps nextOps finishOps)
end C
def smallProgram : Program :=
 C.initOps.map UniformNatBlockMachine.Op.code++[.jump 11]++
 C.testOps.map UniformNatBlockMachine.Op.code++[.branchLT 4175 4176 17 85]++
 C.patchOps.map UniformNatBlockMachine.Op.code++[.jump 27]++
 UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 27 90)++
 C.nextOps.map UniformNatBlockMachine.Op.code++[.jump 11]++
 C.finishOps.map UniformNatBlockMachine.Op.code++[.jump 89,.halt,.jump 79]
example:smallProgram.length=91:=rfl
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/padding/program.json"
 (Json.compress (.arr (smallProgram.map insJson).toArray))
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/padding/slices.json"
 (Json.compress (Json.mkObj (([("init",C.initOps),("test",C.testOps),("patch",C.patchOps),
 ("next",C.nextOps),("finish",C.finishOps)].map fun (name,ops)=>(name,.arr ((ops.map UniformNatBlockMachine.Op.code).map insJson).toArray))++
 [("reader",.arr (UniformFixedNetworkOpcodeMachine.headProgram.map insJson).toArray)])))
