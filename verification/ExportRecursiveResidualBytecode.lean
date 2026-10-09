import UniformRecursiveResidualControl
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




-- Same symbolic CodeAt-linked fragments at finite addresses. Gather87
-- only jumps to Next78; stops86/88 stand for external destinations.
namespace C
export UniformRecursiveResidualControl (markOps initOps nextOps edgeOps advanceOps)
end C
def smallTargets:Fin 7→Nat:=![68,88,88,88,88,88,88]
def smallProgram:Program:=
 UniformRecursiveRecordControl.loopBlock.map UniformNatBlockMachine.Op.code++[.branchLT 2850 3301 4 86]++
 UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 4 56)++
 UniformRecursiveRecordControl.dispatchCode 56 smallTargets++
 C.markOps.map UniformNatBlockMachine.Op.code++
 C.initOps.map UniformNatBlockMachine.Op.code++[.jump 77]++
 [.branchLT 4134 4132 87 80]++
 C.nextOps.map UniformNatBlockMachine.Op.code++[.jump 77]++
 C.edgeOps.map UniformNatBlockMachine.Op.code++[.branchLT 4177 4153 84 88]++
 C.advanceOps.map UniformNatBlockMachine.Op.code++[.jump 0,.halt,.jump 78,.halt]
example:smallProgram.length=89:=rfl
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/residual/program.json"
 (Json.compress (.arr (smallProgram.map insJson).toArray))
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/residual/slices.json"
 (Json.compress (Json.mkObj (([("mark",C.markOps),("init",C.initOps),("next",C.nextOps),("edge",C.edgeOps),
 ("advance",C.advanceOps),("loop",UniformRecursiveRecordControl.loopBlock)].map fun (name,ops)=>(name,.arr ((ops.map UniformNatBlockMachine.Op.code).map insJson).toArray))++
 [("reader",.arr (UniformFixedNetworkOpcodeMachine.headProgram.map insJson).toArray),
 ("dispatch",.arr ((UniformRecursiveRecordControl.dispatchCode 56 smallTargets).map insJson).toArray)])))
