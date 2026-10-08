import UniformFixedNetworkYRecordLoopMachine
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


#eval IO.FS.writeFile "../logs/uniform-bytecode/y-record/programs.json"
 (Json.compress (Json.mkObj [("recordY",.arr (UniformFixedNetworkYRecordMachine.program.map insJson).toArray),
 ("mixedY",.arr (UniformFixedNetworkYRecordLoopMachine.program.map insJson).toArray)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/y-record/spec.json"
 (Json.compress (.arr (([(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(4,1)] : List (Nat×Nat)).map (fun p=>
 Json.mkObj [("q",toJson p.1),("width",toJson p.2),("oneRow",toJson (UniformFixedNetworkYRecordMachine.runtime p.1 p.2 1)),
 ("threeRows",toJson (UniformFixedNetworkYRecordMachine.runtime p.1 p.2 3)),("emptyRows",toJson (UniformFixedNetworkYRecordMachine.runtime p.1 p.2 0))])).toArray))
example : UniformFixedNetworkYRecordMachine.program.length=197 := UniformFixedNetworkYRecordMachine.program_length

namespace Fixture
open UniformFixedNetworkYRecordLoopMachine
def sampleDirection (w:Nat) (role:Fin 4) (alt:Bool) : UniformFixedNetworkYRecordMachine.Direction 4 w :=
 ⟨role,fun j=>if alt then (j.val%2 : ZMod 2) else 0⟩
def items (w:Nat) : List (Item 4 w) := [
 .scalar 0 1 (by decide) 0,.scalar 0 1 (by decide) 1,.scalar 0 1 (by decide) 2,
 .scalar 0 1 (by decide) 3,.scalar 0 1 (by decide) 4,
 .translation [sampleDirection w 2 true,sampleDirection w 1 false,sampleDirection w 2 true],
 .exchange [⟨0,1,by decide⟩,⟨1,2,by decide⟩],.padding 0 3 (by decide),
 .translation [],.exchange [],.padding 4 0 (by decide)]
end Fixture
#eval IO.FS.writeFile "../logs/uniform-bytecode/y-record/mixed-spec.json"
 (Json.compress (.arr (([(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)] : List (Nat×Nat)).map (fun p=>
 Json.mkObj [("q",toJson p.1),("width",toJson p.2),
 ("data",toJson (((Fixture.items p.2).map (UniformFixedNetworkYRecordLoopMachine.Item.record p.1 p.2)).map UniformFixedNetworkScheduleMachine.Record.data |>.flatten)),
 ("runtime",toJson (UniformFixedNetworkYRecordLoopMachine.cost p.1 p.2 (Fixture.items p.2)+7))])).toArray))
example : UniformFixedNetworkYRecordLoopMachine.program.length=535 := UniformFixedNetworkYRecordLoopMachine.program_length
