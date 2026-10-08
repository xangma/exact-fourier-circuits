import UniformDyadicConvolutionMachine
import UniformInitialTraversalPreparation
import UniformCRTTransferMachine
open ExactFourierCircuits UniformMachine UniformRadixTwoDAG UniformPreparationMachine
open Lean

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
def rowJson (row:Row) : Json:=.arr #[toJson (opcode row.op),toJson row.left,toJson row.right]
def fixture (k:ℕ) : Json:=Json.mkObj [("height",toJson k),("width",toJson (width k)),("count",toJson (count k)),
 ("runtime",toJson (UniformDyadicConvolutionMachine.runtime (4*width k) k)),
 ("normRuntime",toJson (UniformNormalizationMachine.runtime (width k))),
 ("layouts",.arr (#[(1024,8192),(32768,262144)].map (fun (a,d)=>Json.mkObj [
    ("arena",toJson a),("table",toJson d),("wordBudget",toJson (UniformDyadicConvolutionMachine.wordBudget k a d))]))),
 ("rows",.arr ((List.finRange (count k)).map (fun j=>rowJson (UniformRadixTwoMachine.row k j))).toArray)]
def programJson (p:Program) : Json:=.arr (p.map insJson).toArray
#eval IO.FS.writeFile "../logs/uniform-bytecode/programs.json" (Json.compress (Json.mkObj [
  ("convolution",programJson UniformDyadicConvolutionMachine.program),
  ("seedStartup",programJson UniformAllAxisSeedPreparation.fullProgram),
  ("traversalStartup",programJson UniformInitialTraversalPreparation.program),
  ("transfer",programJson UniformCRTTransferMachine.program)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/expected.json"
  (Json.compress (.arr ((List.range 7).map fixture).toArray))
