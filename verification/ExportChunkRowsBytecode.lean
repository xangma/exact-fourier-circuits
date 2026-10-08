import UniformChunkRowTableMachine
import Lean
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

#eval IO.FS.writeFile "../logs/uniform-bytecode/chunk-rows/programs.json" (Json.compress (Json.mkObj [
 ("port",.arr (UniformChunkPortMachine.program.map insJson).toArray),
 ("rows",.arr (UniformChunkRowTableMachine.program.map insJson).toArray),
 ("borrowedRows",.arr ((UniformBorrowedCoordinateMachine.program.map (UniformAssembly.relocate 0 17) ++
   UniformChunkRowTableMachine.program.map (UniformAssembly.relocate 17 76) ++ [Instruction.halt]).map insJson).toArray)]))

open Lean ExactFourierCircuits

def shapes : List (ℕ×ℕ×ℕ×ℕ×ℕ×ℕ) := [(9,2,3,2,1,5),(9,2,3,2,6,1),(37,3,7,4,6,23),(4,0,1,2,0,2),(4,1,0,2,0,2)]
def spec (v e g a s t : ℕ) : Json :=
 let borrowed:=((List.range v).filter (fun i=>decide (UniformBorrowedCoordinateMachine.Eligible s e t a i))).take g
 let ports:=List.range e ++ (List.range (g+a)).map (fun j=>e+1+j)
 Json.mkObj [("shape",toJson [v,e,g,a,s,t]),("borrowed",toJson borrowed),
  ("ports",toJson ports),
  ("mapped",toJson (ports.map (UniformChunkPortMachine.mapped e g s t (fun j=>borrowed[j]?.getD 0)))),
  ("runtimes",toJson (ports.map (UniformChunkPortMachine.runtime e g)))]
#eval IO.FS.writeFile "../logs/uniform-bytecode/chunk-rows/lean-spec.json" (Json.compress
 (.arr ((shapes.map (fun (v,e,g,a,s,t)=>spec v e g a s t)).toArray)))
