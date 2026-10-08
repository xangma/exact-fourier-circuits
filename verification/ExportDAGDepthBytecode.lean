import UniformDAGDepthMachine
import UniformConvolutionTopologyMachine
import Lean
open ExactFourierCircuits UniformMachine

def natCode : NatOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3 | .mod=>4

def fieldCode : FieldOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3

def encodeInstruction : Instruction→String
  | .natLiteral d v=>s!"[0,{d},{v}]"
  | .natBinary op d a b=>s!"[1,{natCode op},{d},{a},{b}]"
  | .loadNat d a=>s!"[2,{d},{a}]"
  | .storeNat a r=>s!"[3,{a},{r}]"
  | .branchLT a b y n=>s!"[4,{a},{b},{y},{n}]"
  | .jump t=>s!"[5,{t}]"
  | .halt=>"[6]"
  | .loadScalar d a=>s!"[7,{d},{a}]"
  | .storeScalar a r=>s!"[8,{a},{r}]"
  | .scalarLiteral d v=>s!"[9,{d},{v.num},{v.den}]"
  | .fieldBinary op d a b=>s!"[10,{fieldCode op},{d},{a},{b}]"
  | .length d=>s!"[11,{d}]"
  | .root d q=>s!"[12,{d},{q}]"
  | .input d j=>s!"[13,{d},{j}]"
  | .output j s=>s!"[14,{j},{s}]"


open Lean
#eval IO.FS.writeFile "../logs/uniform-bytecode/dag-depth/program.json"
 ("["++String.intercalate "," (UniformDAGDepthMachine.program.map encodeInstruction)++"]")
def plainFixture (N : ℕ) (rs : List UniformDAGDepthMachine.Row) : Json := Id.run do
 let tape:=rs.map fun row=>Json.arr #[toJson row.opcode,toJson row.left,toJson row.right,toJson (0:ℕ),toJson (0:ℕ)]
 let labels:=UniformDAGDepthMachine.evaluate (N+1) rs (fun _=>0)
 let depths:=(List.range (N+1+rs.length)).map fun i=>toJson (labels i)
 return Json.mkObj [("K",Json.null),("inputs",toJson N),("gates",toJson rs.length),
   ("tape",Json.arr tape.toArray),("depths",Json.arr depths.toArray)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/dag-depth/plain-specs.json"
 (Json.compress (Json.arr #[plainFixture 0 [],plainFixture 3 [],
   plainFixture 0 [.scale 0],plainFixture 0 [.add 0 0],plainFixture 0 [.sub 0 0],
   plainFixture 0 [.scale 0,.add 0 1,.sub 0 2],
   plainFixture 0 [.scale 0,.sub 1 0,.add 2 0],
   plainFixture 0 [.add 0 0,.sub 1 1,.scale 2]]))
