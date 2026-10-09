import UniformRecursiveNativeRecords
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




-- Only these small slices are evaluated. The common SavingProgram and its
-- enormous addresses, seed and unit payloads remain symbolic.
def smallTargets : Fin 7→Nat := ![523,68,469,272,174,523,469]
def smallSlices : List (String × Program) :=
 [("loop",UniformRecursiveRecordControl.loopBlock.map UniformNatBlockMachine.Op.code ++ [.branchLT 2850 3301 4 523]),
 ("head",UniformFixedNetworkOpcodeMachine.headProgram),
 ("dispatch",UniformRecursiveRecordControl.dispatchCode 56 smallTargets),
 ("scalar",UniformNativeScalarRecordMachine.scalarProgram),
 ("exchange",UniformNativeExchangeRecordMachine.program),
 ("translation",UniformNativeYRecordMachine.program),
 ("marker",UniformFixedNetworkMarkerMachine.program)]
def smallProgram : Program :=
 UniformRecursiveRecordControl.loopBlock.map UniformNatBlockMachine.Op.code ++ [.branchLT 2850 3301 4 523] ++
 UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 4 56) ++
 UniformRecursiveRecordControl.dispatchCode 56 smallTargets ++
 UniformNativeScalarRecordMachine.scalarProgram.map (relocate 68 0) ++
 UniformNativeExchangeRecordMachine.program.map (relocate 174 0) ++
 UniformNativeYRecordMachine.program.map (relocate 272 0) ++
 UniformFixedNetworkMarkerMachine.program.map (relocate 469 0) ++ [.halt]
example : smallProgram.length=524 := by
 simp only [smallProgram,List.length_append,List.length_map,
  UniformFixedNetworkOpcodeMachine.headProgram_length,UniformNativeScalarRecordMachine.scalarProgram_length,
  UniformNativeExchangeRecordMachine.program_length,UniformNativeYRecordMachine.program_length,
  UniformFixedNetworkMarkerMachine.program_length]
 rfl
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/native/slices.json"
 (Json.compress (Json.mkObj (smallSlices.map (fun (name,code)=>(name,.arr (code.map insJson).toArray)))))
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/native/small-program.json"
 (Json.compress (.arr (smallProgram.map insJson).toArray))
