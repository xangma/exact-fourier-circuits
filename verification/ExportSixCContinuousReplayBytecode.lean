import UniformSixCFullProgram
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine Lean
def writeArtifact (name:String) (data:Json) : IO Unit := do
 let directory:=System.FilePath.mk ((←IO.getEnv "UNIFORM_SIX_C_OUTPUT_DIR").getD "../logs/uniform-bytecode/six-c-continuous")
 IO.FS.createDirAll directory
 IO.FS.writeFile (directory / name) (Json.compress data)

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

def rowJson (r:UniformConvolutionTopologyMachine.Row):Json:=.arr #[toJson r.opcode,toJson r.left,toJson r.right,toJson r.kind,toJson r.payload]
/-- Actual lossless cross rows (crossRows_typed), with an independent cached
integer longest-path reference. This avoids materializing the dependent typed
AST in the diagnostic evaluator; the source theorem is audited separately. -/
def typedSpec (K a e:ℕ) (_ha:a≤UniformRadixTwoDAG.width K) (_he:e≤UniformRadixTwoDAG.width K):Json:=
 let rows:=UniformToeplitzCrossTopologyMachine.crossRows K a e
 let G:=rows.length
 let depths:=rows.foldl (fun (levels:Array ℕ) row=>
  levels.push ((if row.opcode<2 then max (levels.getD row.left 0) (levels.getD row.right 0)
   else levels.getD row.left 0)+1)) (Array.replicate (e+1) 0)
 let levels:=fun i=>depths.getD (e+1+i) 0
 Json.mkObj [("K",toJson K),("a",toJson a),("e",toJson e),("G",toJson G),
  ("rows",.arr (rows.map rowJson).toArray),
  ("order",toJson (UniformDAGBucketMachine.order G levels)),
  ("offsets",toJson ((List.range (G+2)).map (fun d=>UniformDAGBucketMachine.offset G d levels)))]
#eval writeArtifact "programs.json"
 (Json.mkObj [("full",.arr (UniformSixCFullProgram.program.map insJson).toArray),
  ("ascending",.arr ((UniformSixCDepthColorController.traversalProgram false).map insJson).toArray),
  ("descending",.arr ((UniformSixCDepthColorController.traversalProgram true).map insJson).toArray),
  ("positiveBroadcast",.arr ((UniformSixCBroadcast.program true).map insJson).toArray),
  ("negativeBroadcast",.arr ((UniformSixCBroadcast.program false).map insJson).toArray)])
#eval writeArtifact "specs.json"
 (.arr #[typedSpec 0 0 0 (by decide) (by decide),typedSpec 0 0 1 (by decide) (by decide),
  typedSpec 0 1 0 (by decide) (by decide),typedSpec 0 1 1 (by decide) (by decide),
  typedSpec 1 1 1 (by decide) (by decide),typedSpec 1 2 2 (by decide) (by decide),typedSpec 2 1 1 (by decide) (by decide)])

example {r e G:ℕ} (p:UniformReplayPrint.Program r e G) (i:Fin G) :
 UniformDAGBucketMachine.typedDepth p i.val=UniformDAGDepthMachine.evaluate (e+1)
  (UniformDAGDepthMachine.rows p) (fun _=>0) (e+1+i.val):=
 UniformDAGBucketMachine.natLevel_evaluate p _ (by have:=i.isLt;omega)
