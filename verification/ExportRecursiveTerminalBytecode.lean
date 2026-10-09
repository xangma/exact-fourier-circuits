import UniformRecursiveSpectatorFinish
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




-- The giant W, common SavingProgram, actual addresses and seed are never
-- evaluated. Only identical helper/control slices at tiny fixed addresses.
def smallSpectatorProgram (count:Nat) (childHalt:Bool) : Program :=
 UniformRecursiveRecordControl.loopBlock.map UniformNatBlockMachine.Op.code ++
 [.branchLT 2850 3301 80 4] ++
 (UniformRecursiveSpectatorFinish.setupOps count).map UniformNatBlockMachine.Op.code ++ [.jump 10] ++
 UniformBinarySpectatorCMachine.program.map (relocate 10 79) ++
 [.branchLT 4151 4153 80 81,.halt] ++ (if childHalt then [.halt] else [])
example : (smallSpectatorProgram 0 false).length=81 := by
 simp only [smallSpectatorProgram,List.length_append,List.length_map,UniformBinarySpectatorCMachine.program_length]
 rfl
example : (smallSpectatorProgram 4 true).length=82 := by
 simp only [smallSpectatorProgram,List.length_append,List.length_map,UniformBinarySpectatorCMachine.program_length]
 rfl
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/terminal/programs.json"
 (Json.compress (Json.mkObj ((List.range 5).flatMap fun count=>
 [(("root"++toString count),.arr ((smallSpectatorProgram count false).map insJson).toArray),
 (("child"++toString count),.arr ((smallSpectatorProgram count true).map insJson).toArray)])))
#eval IO.FS.writeFile "../logs/uniform-bytecode/recursive-foundations/terminal/slices.json"
 (Json.compress (Json.mkObj [("spectator",.arr (UniformBinarySpectatorCMachine.program.map insJson).toArray),
 ("loop",.arr (UniformRecursiveRecordControl.loopBlock.map UniformNatBlockMachine.Op.code |>.map insJson).toArray),
 ("setup",.arr ((UniformRecursiveSpectatorFinish.setupOps 4).map UniformNatBlockMachine.Op.code |>.map insJson).toArray)]))
