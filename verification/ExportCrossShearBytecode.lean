import UniformCrossShearTableMachine
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


open UniformCrossShearTableMachine UniformToeplitzCrossDAG UniformConvolutionTopologyMachine

def rowJson (r:UniformConvolutionTopologyMachine.Row):String:=
 s!"[{r.opcode},{r.left},{r.right},{r.kind},{r.payload}]"
def rowsJson (rs:List UniformConvolutionTopologyMachine.Row):String:="["++String.intercalate "," (rs.map rowJson)++"]"
def inPlaceJson (r:UniformInPlaceMachine.Row):String:=s!"[{r.dst},{r.src},{r.coefficient}]"
def inPlacesJson (rs:List UniformInPlaceMachine.Row):String:="["++String.intercalate "," (rs.map inPlaceJson)++"]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/program.json"
  ("["++String.intercalate "," (UniformCrossShearTableMachine.program.map encodeInstruction)++"]")

def genericRows:List UniformConvolutionTopologyMachine.Row :=
 [⟨0,0,0,0,0⟩,⟨1,0,0,0,0⟩,⟨2,0,0,1,0⟩,⟨2,1,0,0,1⟩,
  ⟨2,2,0,0,2⟩,⟨0,3,3,0,0⟩,⟨1,4,1,0,0⟩,⟨2,2,0,1,7⟩]
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/generic.json"
 ("["++String.intercalate "," ((List.range 4).flatMap (fun n=>[false,true].map (fun enabled=>
   let order:=(List.range genericRows.length).reverse
   let rows:=(order.flatMap (fun j=>expansion n 10000 20000 30000 j enabled (genericRows[j]?.getD ⟨0,0,0,0,0⟩)))
   s!"[{n},{if enabled then 1 else 0},{rowsJson genericRows},{toString order},{inPlacesJson rows}]")))++"]")

def depthRow (r:UniformConvolutionTopologyMachine.Row):UniformDAGDepthMachine.Row:=
 if r.opcode=0 then .add r.left r.right else if r.opcode=1 then .sub r.left r.right else .scale r.left
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/physical.json"
 ("["++String.intercalate "," (([(0,0,0),(0,1,1),(1,1,1),(1,2,2),(2,1,3),(2,4,4),(3,2,5),(3,8,8),(4,7,11)] : List (ℕ×ℕ×ℕ)).flatMap (fun (K,a,e)=>
 [false,true].map (fun enabled=>
 let rs:=UniformToeplitzCrossTopologyMachine.crossRows K a e
 let G:=rs.length
 let d:=UniformDAGDepthMachine.evaluate (e+1) (rs.map depthRow) (fun _=>0)
 let depths:=(List.range G).map (fun j=>d (e+1+j))
 let da:=depths.toArray
 let level:=fun j=>(da[j]?).getD 0
 let order:=UniformDAGBucketMachine.order G level
 let output:=order.flatMap (fun j=>expansion e 10000 20000 30000 j enabled (rs[j]?.getD ⟨0,0,0,0,0⟩))
 s!"[{K},{a},{e},{if enabled then 1 else 0},{rowsJson rs},{toString order},{inPlacesJson output},{toString depths}]")))++"]")

-- Typed K0 references are bounded; larger references above use actual physical tapes.
def p0_0:= (crossDAG 0 0 0 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-0-0.json"
 (let p:=p0_0
  let order:=UniformDAGBucketMachine.order (crossDAG 0 0 0 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p false).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,0,0,0,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 0 0)},{toString order},{inPlacesJson output},{toString levels}]")

def p0_1:= (crossDAG 0 0 0 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-0-1.json"
 (let p:=p0_1
  let order:=UniformDAGBucketMachine.order (crossDAG 0 0 0 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p true).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,0,0,1,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 0 0)},{toString order},{inPlacesJson output},{toString levels}]")

def p1_0:= (crossDAG 0 1 0 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-1-0.json"
 (let p:=p1_0
  let order:=UniformDAGBucketMachine.order (crossDAG 0 1 0 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p false).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,1,0,0,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 1 0)},{toString order},{inPlacesJson output},{toString levels}]")

def p1_1:= (crossDAG 0 1 0 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-1-1.json"
 (let p:=p1_1
  let order:=UniformDAGBucketMachine.order (crossDAG 0 1 0 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p true).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,1,0,1,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 1 0)},{toString order},{inPlacesJson output},{toString levels}]")

def p2_0:= (crossDAG 0 1 1 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-2-0.json"
 (let p:=p2_0
  let order:=UniformDAGBucketMachine.order (crossDAG 0 1 1 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p false).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,1,1,0,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 1 1)},{toString order},{inPlacesJson output},{toString levels}]")

def p2_1:= (crossDAG 0 1 1 (by decide) (by decide)).program
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/cross-2-1.json"
 (let p:=p2_1
  let order:=UniformDAGBucketMachine.order (crossDAG 0 1 1 (by decide) (by decide)).size (UniformDAGBucketMachine.typedDepth p)
  let output:=(orderedSweep p true).map (shiftedRow 10000 (locations (bankSize 0) 20000 40000 30000))
  let levels:=order.map (UniformDAGBucketMachine.typedDepth p)
  s!"[0,1,1,1,{rowsJson (UniformToeplitzCrossTopologyMachine.crossRows 0 1 1)},{toString order},{inPlacesJson output},{toString levels}]")


#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/depth-program.json"
  ("["++String.intercalate "," (UniformDAGDepthMachine.program.map encodeInstruction)++"]")

#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-shear/bucket-program.json"
  ("["++String.intercalate "," (UniformDAGBucketMachine.program.map encodeInstruction)++"]")
