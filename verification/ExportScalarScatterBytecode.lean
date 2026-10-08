import UniformScalarScatterMachine
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


#eval IO.FS.createDirAll "../logs/uniform-bytecode/scalar-scatter"
#eval IO.FS.writeFile "../logs/uniform-bytecode/scalar-scatter/program.json"
 (Json.compress (.arr (UniformScalarScatterMachine.program.map insJson).toArray))
def spec (L shift:ℕ) (rev:Bool) : Json:=
 let phi:=(List.range L).map (fun j=>(if rev then L-1-j+shift else j+shift)%L)
 let inverse:=(List.range L).map (fun j=>phi.idxOf j)
 Json.mkObj [("L",toJson L),("shift",toJson shift),("reversed",toJson rev),
 ("permutation",toJson phi),("inverse",toJson inverse)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/scalar-scatter/specs.json"
 (Json.compress (.arr (([0,1,2,3,5,7,16,31].flatMap fun L=>
 [0,1,3].flatMap fun shift=>[false,true].map fun rev=>spec L shift rev).toArray)))
example:UniformScalarScatterMachine.program.length=12:=UniformScalarScatterMachine.program_length
