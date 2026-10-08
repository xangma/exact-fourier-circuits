import UniformAllAxisMatchingTablePreparation
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

def edge (M seed : ℕ) (i : Fin M) : UniformColoring.Edge :=
 let a:=2*((i.val+seed)%M)
 ⟨a,a+1,by omega⟩
def axisModel (r mode seed:ℕ):Json:=
 let M:=if mode=0 then 0 else if mode=1 then r/2 else if mode=2 then r/3 else min 1 (r/2)
 let E:=edge M seed
 Json.mkObj [("r",toJson r),("count",toJson M),
  ("edges",toJson ((List.finRange M).map (fun i=>[(E i).left,(E i).right]))),
  ("order",toJson (UniformMatchingAxisTableMachine.ordered r E)),
  ("widths",toJson (UniformMatchingAxisTableMachine.widths r M))]
def model (n mode seed:ℕ):Json:=
 let rs:=List.ofFn (UniformSelectedCRT.radices n)
 Json.mkObj [("n",toJson n),("length",toJson (UniformInitialPreparation.len n)),
  ("copyBase",toJson (UniformInitialPreparation.copyBase n)),
  ("protectedAmount",toJson (UniformGlobalNatPreparation.amount (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n))),
  ("axes",toJson (rs.map (fun r=>axisModel r mode seed)))]
#eval IO.FS.createDirAll "../logs/uniform-bytecode/all-axis-matching-table"
#eval IO.FS.writeFile "../logs/uniform-bytecode/all-axis-matching-table/programs.json"
 (Json.compress (Json.mkObj [("matching",.arr (UniformAllAxisMatchingTablePreparation.program.map insJson).toArray)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/all-axis-matching-table/spec.json"
 (Json.compress (Json.mkObj [("models",toJson (([1,2,3,4,8,16,32,64,100,257]:List ℕ).flatMap
  (fun n=>(List.range 4).flatMap (fun mode=>(List.range 2).map (fun seed=>model n mode seed)))))]))
example:UniformAllAxisMatchingTablePreparation.program.length=79:=UniformAllAxisMatchingTablePreparation.program_length
