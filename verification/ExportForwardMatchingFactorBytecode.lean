import UniformForwardMatchingFactorHeaderExecution
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



namespace ForwardFactorReference

open Lean ExactFourierCircuits
open UniformToeplitzCrossDAG UniformConvolutionTopologyMachine UniformCrossDepthReplayPreparation

def rowJson (x:UniformConvolutionTopologyMachine.Row) : Json:=toJson [x.opcode,x.left,x.right,x.kind,x.payload]
def inPlaceJson (x:UniformInPlaceMachine.Row) : Json:=toJson [x.dst,x.src,x.coefficient]
def typedSpec (K a e : ℕ) (ha:a ≤ UniformRadixTwoDAG.width K) (he:e ≤ UniformRadixTwoDAG.width K) (enabled:Bool) : Json:=
 let d:=crossDAG K a e ha he
 let p:=d.program
 -- evaluate_typed/natLevel_evaluate prove these cached labels are the
 -- constructor-longest-path labels; avoid recursively unfolding runDepth.
 let labels:=UniformDAGDepthMachine.evaluate (e+1) (UniformDAGDepthMachine.rows p) (fun _=>0)
 let levels:=fun i=>labels (e+1+i)
 let order:=UniformDAGBucketMachine.order d.size levels
 let offsets:=(List.range (d.size+2)).map (fun q=>UniformDAGBucketMachine.offset d.size q levels)
 let slices:=(List.range (8*K+7)).map fun depth=>
  let W:=(UniformDAGLayers.natSweep p enabled).filter (fun s=>decide (labels s.dst=depth))
  let rows:=W.map (UniformCrossShearTableMachine.shiftedRow 0
   (UniformCrossShearTableMachine.locations (bankSize K) 200000 210000 220000))
  let colors:=List.ofFn (UniformColoring.coloring (shiftedEdges 0 W) 6)
  Json.mkObj [("rows",.arr (rows.map inPlaceJson).toArray),("colors",toJson colors)]
 Json.mkObj [("K",toJson K),("a",toJson a),("e",toJson e),("enabled",toJson enabled),
  ("typed",.arr ((UniformToeplitzCrossTopologyMachine.crossRows K a e).map rowJson).toArray),
  ("order",toJson order),("offsets",toJson offsets),("slices",.arr slices.toArray)]


#eval IO.FS.createDirAll "../logs/uniform-bytecode/forward-matching-factor"
#eval IO.FS.writeFile "../logs/uniform-bytecode/forward-matching-factor/programs.json"
 (Json.compress (Json.mkObj [("body",toJson (UniformForwardMatchingFactorPreparation.program.map insJson)),
 ("reload",toJson (UniformForwardMatchingFactorHeaderPreparation.program.map insJson)),
 ("height",toJson (UniformCrossHeightPreparationMachine.program.map insJson))]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/forward-matching-factor/specs.json"
 (Json.compress (toJson ([false,true].flatMap fun en=>
 [typedSpec 0 0 0 (by decide) (by decide) en,
  typedSpec 0 1 1 (by decide) (by decide) en,
  typedSpec 0 1 0 (by decide) (by decide) en,
  typedSpec 0 0 1 (by decide) (by decide) en])))
end ForwardFactorReference
