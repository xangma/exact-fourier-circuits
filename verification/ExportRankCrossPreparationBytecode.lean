import UniformRankCrossPreparationMachine
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

#eval IO.FS.writeFile "../logs/uniform-bytecode/rank-cross-preparation/program.json" (Json.compress (.arr (UniformRankCrossPreparationMachine.program.map insJson).toArray))

def rowJson (r : UniformConvolutionTopologyMachine.Row) : Json :=
 .arr #[toJson r.opcode,toJson r.left,toJson r.right,toJson r.kind,toJson r.payload]
def model (K a e : Nat) (ha : a ≤ UniformRadixTwoDAG.width K) (he : e ≤ UniformRadixTwoDAG.width K) : Json :=
 let p:=(UniformToeplitzCrossDAG.crossDAG K a e ha he).program
 Json.mkObj [("height",toJson K),("a",toJson a),("e",toJson e),
  ("rows",.arr ((UniformToeplitzCrossDAG.programRecords p).map (fun x=>rowJson (UniformConvolutionTopologyMachine.encode x))).toArray)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/rank-cross-preparation/models.json" (Json.compress (.arr #[
 model 0 1 1 (by decide) (by decide),
 model 1 1 1 (by decide) (by decide),model 1 2 2 (by decide) (by decide),model 1 1 2 (by decide) (by decide),
 model 2 1 1 (by decide) (by decide),model 2 4 4 (by decide) (by decide),model 2 3 2 (by decide) (by decide),
 model 3 1 1 (by decide) (by decide),model 3 8 8 (by decide) (by decide),model 3 7 4 (by decide) (by decide),
 model 4 1 1 (by decide) (by decide),model 4 16 16 (by decide) (by decide),model 4 15 8 (by decide) (by decide)]))


def fixtureParameters (K a e S A d C V tape depth seed : Nat) : UniformRankCrossPreparationMachine.Parameters :=
 let j0:=seed%2
 let split:=j0+e+1
 let i0:=split+1
 ⟨K,10,200,i0+a,split+2,a,e,i0,j0,split,S,A,d,C,4*2^K,V,tape,depth⟩
#eval IO.FS.writeFile "../logs/uniform-bytecode/rank-cross-preparation/runtime-budgets.json"
 (Json.compress (.arr (([(0,1,1),(1,1,1),(1,2,2),(1,1,2),(2,1,1),(2,4,4),(2,3,2),(3,1,1),(3,8,8),(3,7,4),(4,1,1),(4,16,16),(4,15,8)] : List (Nat×Nat×Nat)).flatMap (fun (K,a,e)=>
  ([(1000,2000,30000,10000,40000,100000,200000),(2000,4000,70000,20000,100000,300000,400000)] : List (Nat×Nat×Nat×Nat×Nat×Nat×Nat)).flatMap (fun (S,A,d,C,V,tape,depth)=>
  [17,99].map (fun seed=>toJson ([K,a,e,S,A,d,C,V,tape,depth,seed,
    UniformRankCrossPreparationMachine.runtimeBudget (fixtureParameters K a e S A d C V tape depth seed)] : List Nat))))).toArray))
