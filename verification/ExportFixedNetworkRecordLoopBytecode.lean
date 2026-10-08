import UniformFixedNetworkRecordLoopMachine
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


#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-record-loop/programs.json"
 (Json.compress (Json.mkObj [
  ("recordLoop",.arr (UniformFixedNetworkRecordLoopMachine.program.map insJson).toArray),
  ("exchangeRecord",.arr (UniformFixedNetworkExchangeRecordMachine.program.map insJson).toArray),
  ("exchange",.arr (UniformFixedNetworkExchangeChildMachine.program.map insJson).toArray),
  ("mixed",.arr (UniformFixedNetworkScalarPaddingLoopMachine.program.map insJson).toArray),
  ("scalar",.arr (UniformFixedNetworkChildDispatchMachine.scalarProgram.map insJson).toArray),
  ("padding",.arr (UniformFixedNetworkPaddingChildMachine.dispatchProgram.map insJson).toArray),
  ("volume",.arr (UniformFixedNetworkChildDispatchMachine.volumeProgram.map insJson).toArray)]))

open UniformFixedNetworkRecordLoopMachine in
def fixtureItems : List (Item 4) :=
 [.scalar 0 1 (by decide) 0,
 .exchange [⟨0,1,by decide⟩,⟨1,2,by decide⟩],
 .padding 0 3 (by decide),
 .scalar 2 3 (by decide) 2,
 .exchange [],.padding 4 0 (by decide)]

#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-record-loop/spec.json"
 (Json.compress (.arr (([(0,3),(1,0),(1,1),(2,1),(1,3)] : List (Nat×Nat)).map (fun p=>
 Json.mkObj [("q",toJson p.1),("width",toJson p.2),
 ("data",toJson (UniformFixedNetworkScheduleMachine.serialize (fixtureItems.map (UniformFixedNetworkRecordLoopMachine.Item.record p.1 p.2)))),
 ("runtime",toJson (UniformFixedNetworkRecordLoopMachine.cost p.1 p.2 fixtureItems+6))])).toArray))
example : UniformFixedNetworkRecordLoopMachine.program.length=335 := UniformFixedNetworkRecordLoopMachine.program_length
