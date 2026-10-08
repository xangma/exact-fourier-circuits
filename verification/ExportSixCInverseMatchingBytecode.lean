import UniformSixCInverseMatchingPreparation
import UniformDAGDepthMachine
import Lean
set_option autoImplicit false
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

def coeffJson {R:ℕ} : UniformReplayPrint.Coefficient R→Json
 | .rational q=>.arr #[toJson "rational",toJson q.num,toJson q.den]
 | .prepared i neg=>.arr #[toJson "prepared",toJson i.val,toJson neg]
def rowJson (row:UniformInPlaceMachine.Row) : Json:=
 .arr #[toJson row.dst,toJson row.src,toJson row.coefficient]
def logicalJson {R:ℕ} (row:UniformReplayPrint.ShearCode ℕ R):Json:=
 .arr #[toJson row.dst,toJson row.src,coeffJson row.coefficient]
def caseJson {R:ℕ} (name:String) (K r:ℕ) (W:List (UniformReplayPrint.ShearCode ℕ R)):Json:=
 Json.mkObj [("name",toJson name),("K",toJson K),("radix",toJson r),("R",toJson R),
   ("logical",.arr (W.map logicalJson).toArray),
   ("forward",.arr ((UniformSixCInverseMatchingPreparation.forwardRows 32 128 224 W).map rowJson).toArray),
   ("inverse",.arr ((UniformInverseShearTableMachine.inverseRows 32 128 224
     (UniformSixCInverseMatchingPreparation.forwardRows 32 128 224 W)).map rowJson).toArray)]

def cachedBucket {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool) (depth:ℕ) :=
 let levels:=UniformDAGDepthMachine.evaluate (n+1) (UniformDAGDepthMachine.rows p) (fun _=>0)
 (UniformDAGLayers.natSweep p enabled).filter (fun s=>decide (levels s.dst=depth))
lemma cachedBucket_eq {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool) (depth:ℕ) :
 cachedBucket p enabled depth=UniformCrossDepthReplayPreparation.bucket p enabled depth := by
 unfold cachedBucket UniformCrossDepthReplayPreparation.bucket
 apply List.filter_congr
 intro row member
 have small:row.dst<n+1+t:=(UniformDAGLayers.natSweep_bounds p enabled row member).2.1
 rw [UniformDAGDepthMachine.evaluate_typed p ⟨row.dst,small⟩,UniformDAGLayers.natLevel_at p ⟨row.dst,small⟩]

def crossCases (K a e:ℕ) (enabled:Bool) : List Json :=
 if ha:a≤UniformRadixTwoDAG.width K then
  if he:e≤UniformRadixTwoDAG.width K then
   let graph:=UniformToeplitzCrossDAG.crossDAG K a e ha he
   (List.range (8*K+7)).flatMap (fun d=>
     let bucket:=cachedBucket graph.program enabled d
     let colors:=UniformChunkMatchingPreparation.colors bucket
     (List.range 11).filterMap (fun color=>
       let chosen:=(UniformColorLayerTableMachine.selected bucket.length color colors).filterMap
         (fun i=>bucket[i]?)
       if chosen.isEmpty then none else some (caseJson
         s!"typed-cross-K{K}-a{a}-e{e}-{enabled}-d{d}-c{color}" K (graph.size+e+a+3) chosen)))
  else []
 else []

#eval IO.FS.createDirAll "../logs/uniform-bytecode/six-c-inverse-matching"
#eval IO.FS.writeFile "../logs/uniform-bytecode/six-c-inverse-matching/programs.json"
 (Json.compress (Json.mkObj [("joined",.arr (UniformSixCInverseMatchingPreparation.program.map insJson).toArray),
 ("inverse",.arr (UniformInverseShearTableMachine.program.map insJson).toArray),
 ("matchingAxis",.arr (UniformMatchingAxisTableMachine.program.map insJson).toArray),
 ("packing",.arr (UniformSectorPackingMachine.program.map insJson).toArray),
 ("matchingShear",.arr (UniformPackedMatchingShearMachine.program.map insJson).toArray)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/six-c-inverse-matching/spec.json"
 (Json.compress (Json.mkObj [("typedCases",.arr ((List.range 1).flatMap (fun K=>
   let N:=UniformRadixTwoDAG.width K
   [(0,0),(N,N)].flatMap (fun p=>[false,true].flatMap (crossCases K p.1 p.2)))).toArray),
 ("fields",toJson ([4,8,12]:List ℕ)),("pairs",toJson ([0,1,2,3,6]:List ℕ)),
 ("tails",toJson ([0,1,3]:List ℕ)),("K",toJson ([0,1,3]:List ℕ))]))
example : UniformSixCInverseMatchingPreparation.program.length=683 :=
 UniformSixCInverseMatchingPreparation.program_length
