import UniformAllSectorTransposeMachine
import UniformSectorChildEntryPreparation
import UniformSectorRestoringScatterPreparation
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformTensorMonomialMachine Lean
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
#eval IO.FS.createDirAll "../logs/uniform-bytecode/operational-kernels/transpose-bytecode"
#eval IO.FS.writeFile "../logs/uniform-bytecode/operational-kernels/transpose-bytecode/programs.json"
 (Json.compress (toJson ([1,2,3,5].map (fun W=>Json.mkObj [("W",toJson W),
  ("forward34",toJson ((UniformSectorTransposeMachine.programFor W false).map insJson)),
  ("reverse34",toJson ((UniformSectorTransposeMachine.programFor W true).map insJson)),
  ("child39",toJson ((UniformSectorChildEntryPreparation.programFor W).map insJson)),
  ("restoring51",toJson ((UniformSectorRestoringScatterPreparation.programFor W).map insJson)),
  ("forward41",toJson ((UniformAllSectorTransposeMachine.programFor W false).map insJson)),
  ("reverse41",toJson ((UniformAllSectorTransposeMachine.programFor W true).map insJson))]))))
