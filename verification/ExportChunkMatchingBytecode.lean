import UniformChunkMatchingPreparation
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

#eval IO.FS.writeFile "../logs/uniform-bytecode/chunk-matching/programs.json" (Json.compress (Json.mkObj [
 ("chunk",.arr (UniformChunkMatchingPreparation.program.map insJson).toArray),
 ("heightChunk",.arr ((UniformCrossHeightPreparationMachine.program.map (UniformAssembly.relocate 0 186) ++
 UniformChunkMatchingPreparation.program.map (UniformAssembly.relocate 186 401) ++ [Instruction.halt]).map insJson).toArray)]))

namespace TypedReference
open Lean ExactFourierCircuits
open UniformToeplitzCrossDAG UniformConvolutionTopologyMachine UniformCrossDepthReplayPreparation

def rowJson (x:UniformConvolutionTopologyMachine.Row) : Json:=toJson [x.opcode,x.left,x.right,x.kind,x.payload]
def inPlaceJson (x:UniformInPlaceMachine.Row) : Json:=toJson [x.dst,x.src,x.coefficient]
def typedSpec (K a e : ℕ) (ha:a ≤ UniformRadixTwoDAG.width K) (he:e ≤ UniformRadixTwoDAG.width K) (enabled:Bool) : Json:=
 let d:=crossDAG K a e ha he
 let p:=d.program
 let levels:=fun i=>UniformDAGBucketMachine.typedDepth p i
 let order:=UniformDAGBucketMachine.order d.size levels
 let offsets:=(List.range (d.size+2)).map (fun q=>UniformDAGBucketMachine.offset d.size q levels)
 let slices:=(List.range (8*K+7)).map fun depth=>
  let W:=bucket p enabled depth
  let rows:=W.map (UniformCrossShearTableMachine.shiftedRow 0
   (UniformCrossShearTableMachine.locations (bankSize K) 200000 400000 300000))
  let colors:=List.ofFn (UniformColoring.coloring (shiftedEdges 0 W) 6)
  Json.mkObj [("rows",.arr (rows.map inPlaceJson).toArray),("colors",toJson colors)]
 Json.mkObj [("K",toJson K),("a",toJson a),("e",toJson e),("enabled",toJson enabled),
  ("typed",.arr ((UniformToeplitzCrossTopologyMachine.crossRows K a e).map rowJson).toArray),
  ("order",toJson order),("offsets",toJson offsets),("slices",.arr slices.toArray)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/chunk-matching/typed.json" (Json.compress (.arr (([false,true].flatMap fun enabled=>
 [typedSpec 0 0 0 (by decide) (by decide) enabled,
  typedSpec 0 1 1 (by decide) (by decide) enabled]).toArray)))
end TypedReference

namespace CachedReference
open Lean ExactFourierCircuits
open UniformToeplitzCrossDAG UniformConvolutionTopologyMachine UniformCrossDepthReplayPreparation

def rowJson (x:UniformConvolutionTopologyMachine.Row) : Json:=toJson [x.opcode,x.left,x.right,x.kind,x.payload]
def inPlaceJson (x:UniformInPlaceMachine.Row) : Json:=toJson [x.dst,x.src,x.coefficient]
def depthRow (x:UniformConvolutionTopologyMachine.Row) : UniformDAGDepthMachine.Row:=
 if x.opcode=0 then .add x.left x.right else if x.opcode=1 then .sub x.left x.right else .scale x.left
def rowEdge (x:UniformInPlaceMachine.Row) : UniformColoring.Edge:=
 if h:x.dst ≠ x.src then ⟨x.dst,x.src,h⟩ else ⟨0,1,by decide⟩
def fastLabels (e : ℕ) (rs:List UniformConvolutionTopologyMachine.Row) : Array ℕ:=
 rs.foldl (fun labels row=>labels.push (if row.opcode<2 then max (labels[row.left]?.getD 0) (labels[row.right]?.getD 0)+1 else (labels[row.left]?.getD 0)+1)) (Array.replicate (e+1) 0)
def conflictRows (x y:UniformInPlaceMachine.Row) : Bool:=decide (x.dst=y.dst ∨ x.dst=y.src ∨ x.src=y.dst ∨ x.src=y.src)
def fastColors (W:List UniformInPlaceMachine.Row) : Array ℕ:=
 (List.range W.length).foldl (fun cs i=>
  let row:UniformInPlaceMachine.Row:=W[i]?.getD ⟨0,0,0⟩
  let used:List ℕ:=((List.range i).filter (fun j=>conflictRows row (W[j]?.getD ⟨0,0,0⟩))).map (fun j=>cs[j]?.getD 0)
  cs.push (((List.range 11).find? (fun c=> !used.contains c)).getD 11)) #[]
def fastSpec (K a e : ℕ) (enabled:Bool) : Json:=
 let rs:List UniformConvolutionTopologyMachine.Row:=UniformToeplitzCrossTopologyMachine.crossRows K a e
 let labels:Array ℕ:=fastLabels e rs
 let levels:ℕ → ℕ:=fun i=>labels[e+1+i]?.getD 0
 let order:List ℕ:=UniformDAGBucketMachine.order rs.length levels
 let offsets:List ℕ:=(List.range (rs.length+2)).map (fun q=>UniformDAGBucketMachine.offset rs.length q levels)
 let slices:List Json:=(List.range (8*K+7)).map fun depth=>
  let W:List UniformInPlaceMachine.Row:=(order.filter (fun j=>decide (levels j=depth))).flatMap fun j=>
   UniformCrossShearTableMachine.expansion e 0 200000 300000 j enabled (rs[j]?.getD ⟨0,0,0,0,0⟩)
  Json.mkObj [("rows",.arr (W.map inPlaceJson).toArray),("colors",toJson (fastColors W))]
 Json.mkObj [("K",toJson K),("a",toJson a),("e",toJson e),("enabled",toJson enabled),
  ("typed",.arr (rs.map rowJson).toArray),("order",toJson order),("offsets",toJson offsets),("slices",.arr slices.toArray)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/chunk-matching/typed-fast.json" (Json.compress (.arr (([false,true].flatMap fun enabled=>
 [fastSpec 0 0 0 enabled,fastSpec 0 1 1 enabled,fastSpec 1 1 2 enabled,fastSpec 1 2 1 enabled,fastSpec 2 3 2 enabled]).toArray)))
end CachedReference
