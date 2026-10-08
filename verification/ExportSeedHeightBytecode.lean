import UniformSeedHeightPreparation
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


#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-height/program.json"
  (Json.compress (.arr (UniformSeedHeightPreparation.program.map insJson).toArray))
def rowJson (r : UniformConvolutionTopologyMachine.Row) : Json :=
 .arr #[toJson r.opcode,toJson r.left,toJson r.right,toJson r.kind,toJson r.payload]
def model (n j a e split i0 j0 : Nat) : Json :=
 let K:=UniformWorkspacePlanner.exponent a e
 if hj:j<UniformAllAxisSeedPreparation.axisCount n then
 if ha:a≤UniformRadixTwoDAG.width K then
 if he:e≤UniformRadixTwoDAG.width K then
 let axis:Fin (UniformAllAxisSeedPreparation.axisCount n):=⟨j,hj⟩
 let p:=(UniformToeplitzCrossDAG.crossDAG K a e ha he).program
 let c:UniformSeedHeightPreparation.Config:=⟨a,e,i0,j0,split,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,true⟩
 Json.mkObj [("n",toJson n),("axis",toJson j),("height",toJson K),("a",toJson a),("e",toJson e),
  ("split",toJson split),("i0",toJson i0),("j0",toJson j0),
  ("runtimeBudget",toJson (UniformSeedHeightPreparation.runtimeBudget n axis c)),
  ("radix",toJson (UniformAllAxisSeedPreparation.radix n axis)),
  ("axisBase",toJson (UniformAllAxisSeedPreparation.axisBase n j)),
  ("directoryBase",toJson (UniformAllAxisSeedPreparation.directoryBase n)),
  ("directoryEnd",toJson (UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n)),
  ("poolEnd",toJson (UniformAllAxisSeedPreparation.axisBase n (UniformAllAxisSeedPreparation.axisCount n))),
  ("masterOrder",toJson (UniformMasterRootMachine.order n)),
  ("radices",toJson ((List.range (UniformAllAxisSeedPreparation.axisCount n)).map (UniformAllAxisSeedPreparation.radixAt n))),
  ("rows",.arr ((UniformToeplitzCrossDAG.programRecords p).map (fun x=>rowJson (UniformConvolutionTopologyMachine.encode x))).toArray)]
 else .null else .null else .null
#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-height/models.json" (Json.compress (.arr #[
 model 1 0 1 1 1 1 0,
 model 4 0 1 1 1 1 0,
 model 4 0 2 1 1 1 0,
 model 4 0 1 2 2 2 0,
 model 4 1 1 1 2 2 1,
 model 4 1 2 2 2 2 0,
 model 4 1 3 1 1 1 0]))
example:UniformSeedHeightPreparation.program.length=1046:=UniformSeedHeightPreparation.program_length
