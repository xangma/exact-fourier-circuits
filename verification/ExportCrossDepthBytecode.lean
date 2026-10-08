import UniformCrossDepthReplayPreparation
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

def rowJson (r:UniformConvolutionTopologyMachine.Row):String:=
 s!"[{r.opcode},{r.left},{r.right},{r.kind},{r.payload}]"
def inPlaceJson (r:UniformInPlaceMachine.Row):String:=s!"[{r.dst},{r.src},{r.coefficient}]"
def listJson {α : Type} (f:α→String)(xs:List α):String:="["++String.intercalate "," (xs.map f)++"]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-depth/program.json"
  (listJson encodeInstruction UniformCrossDepthReplayPreparation.program)

def p1 : UniformReplayPrint.Program 7 2 1 := .step .nil (.add 0 0)
def p2 : UniformReplayPrint.Program 7 2 2 := .step p1 (.scale (.prepared 0 false) 1)
def p3 : UniformReplayPrint.Program 7 2 3 := .step p2 (.sub 3 4)
def p4 : UniformReplayPrint.Program 7 2 4 := .step p3 (.scale (.rational 1) 5)

def typedSpec (enabled:Bool)(d:ℕ):String:=
 let p:=p4
 let levels:=fun i=>UniformDAGBucketMachine.typedDepth p i
 let order:=UniformDAGBucketMachine.order 4 levels
 let offsets:=(List.range 6).map (fun q=>UniformDAGBucketMachine.offset 4 q levels)
 let W:=bucket p enabled d
 let rows:=W.map (UniformCrossShearTableMachine.shiftedRow 10000
   (UniformCrossShearTableMachine.locations 7 20000 40000 30000))
 let colors:=List.ofFn (UniformColoring.coloring (shiftedEdges 10000 W) 6)
 let rs:=(UniformToeplitzCrossDAG.programRecords p).map UniformConvolutionTopologyMachine.encode
 s!"[0,1,2,{if enabled then 1 else 0},{d},{listJson rowJson rs},{toString order},{toString offsets},{listJson inPlaceJson rows},{toString colors}]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-depth/typed.json"
 (listJson id ((List.range 5).flatMap (fun d=>[false,true].map (fun enabled=>typedSpec enabled d))))

example : activeDepths 0=[0,1,2,3,4,5,6] := by decide
example : UniformCrossDepthReplayPreparation.program.length=132 := rfl
