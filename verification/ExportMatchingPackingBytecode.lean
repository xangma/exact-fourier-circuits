import UniformMatchingPackingPreparation
import Lean
open ExactFourierCircuits UniformMachine Lean
set_option autoImplicit false

/-! Fresh actual bytecode and bounded independent pure references. K0 cross
references use the actual typed DAG, depth buckets, and greedy coloring. -/
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


#eval IO.FS.createDirAll "../logs/uniform-bytecode/matching-packing"
#eval IO.FS.writeFile "../logs/uniform-bytecode/matching-packing/program.json"
 (Json.compress (.arr (UniformMatchingPackingPreparation.program.map insJson).toArray))

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

#eval IO.FS.writeFile "../logs/uniform-bytecode/matching-packing/typed.json" (Json.compress (.arr (([false,true].flatMap fun enabled=>
 [typedSpec 0 0 0 (by decide) (by decide) enabled,
  typedSpec 0 1 1 (by decide) (by decide) enabled]).toArray)))
end TypedReference

namespace MatchingReference
open UniformColoring UniformMatchingAxisTableMachine

def rowEdge (row:UniformInPlaceMachine.Row) : Edge:=
 if h:row.dst≠row.src then ⟨row.dst,row.src,h⟩ else ⟨0,1,by decide⟩
def genericRows (e G:ℕ) : List UniformInPlaceMachine.Row:=
 [⟨e+1,0,200000⟩,⟨e+1+G,e+2,300000⟩,⟨e+3,e+4,200003⟩,⟨0,e+1+G,400000⟩]
def genericSpec (K a e:ℕ) : Json:=
 let N:=2^K
 let G:=6*(3*K*N+2*N)+2*a
 let W:=genericRows e G
 let E:=fun i:Fin W.length=>rowEdge (W.get i)
 Json.mkObj [("K",toJson K),("a",toJson a),("e",toJson e),
  ("rows",.arr (W.map TypedReference.inPlaceJson).toArray),
  ("colors",toJson (List.ofFn (fun i:Fin W.length=>greedy E 11 W.length i.val)))]
#eval IO.FS.writeFile "../logs/uniform-bytecode/matching-packing/generic.json"
 (Json.compress (.arr ([genericSpec 0 1 1,genericSpec 1 2 1,genericSpec 2 2 1].toArray)))
end MatchingReference
