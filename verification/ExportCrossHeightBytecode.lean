import UniformCrossHeightPreparationMachine
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


open UniformCrossDepthReplayPreparation UniformToeplitzCrossDAG UniformConvolutionTopologyMachine

def rowJson (r:UniformConvolutionTopologyMachine.Row):String:=s!"[{r.opcode},{r.left},{r.right},{r.kind},{r.payload}]"
def inPlaceJson (r:UniformInPlaceMachine.Row):String:=s!"[{r.dst},{r.src},{r.coefficient}]"
def listJson {α : Type} (f:α→String)(xs:List α):String:="["++String.intercalate "," (xs.map f)++"]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-height/program.json"
 (listJson encodeInstruction UniformCrossHeightPreparationMachine.program)

def typedSpec (K a e : ℕ) (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K) (enabled:Bool):String:=
 let D:=crossDAG K a e ha he
 let p:=D.program
 let levels:=fun i=>UniformDAGBucketMachine.typedDepth p i
 let order:=UniformDAGBucketMachine.order D.size levels
 let offsets:=(List.range (D.size+2)).map (fun q=>UniformDAGBucketMachine.offset D.size q levels)
 let specs:=(List.range (8*K+7)).map fun d=>
   let W:=bucket p enabled d
   let rows:=W.map (UniformCrossShearTableMachine.shiftedRow 0
     (UniformCrossShearTableMachine.locations (bankSize K) 20000 40000 30000))
   let colors:=List.ofFn (UniformColoring.coloring (shiftedEdges 0 W) 6)
   "["++listJson inPlaceJson rows++","++toString colors++"]"
 s!"[{K},{a},{e},{if enabled then 1 else 0},{listJson rowJson (UniformToeplitzCrossTopologyMachine.crossRows K a e)},{toString order},{toString offsets},{listJson id specs}]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-height/typed.json"
 (listJson id ([false,true].flatMap (fun enabled=>
 [typedSpec 0 0 0 (by decide) (by decide) enabled,
  typedSpec 0 1 1 (by decide) (by decide) enabled])))
example:UniformCrossHeightPreparationMachine.program.length=186:=rfl
