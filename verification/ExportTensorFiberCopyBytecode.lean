import UniformSelectedAxisFiberPreparation
import UniformAllAxisSeedPreparation
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

def startupHeaders : List UniformTensorMonomialMachine.Op :=
 [.literal 1910 0,.literal 1911 0,.literal 1930 7,.literal 1931 2,
  .mul 1932 101 1931,.add 1912 102 1930,.add 1912 1912 1932,.literal 1913 100000]
def startupGather : Program := UniformAllAxisSeedPreparation.fullProgram.map (UniformAssembly.relocate 0 935)++
 startupHeaders.map UniformTensorMonomialMachine.Op.code++
 (UniformSelectedAxisFiberPreparation.program false).map (UniformAssembly.relocate 943 992)++[.halt]
def roundTrip : Program := (UniformSelectedAxisFiberPreparation.program false).map (UniformAssembly.relocate 0 49)++
 (UniformSelectedAxisFiberPreparation.program true).map (UniformAssembly.relocate 49 98)++[.halt]
example : startupGather.length=993 := by simp [startupGather,startupHeaders,UniformAllAxisSeedPreparation.fullProgram_length,
 UniformSelectedAxisFiberPreparation.program_length]
example : roundTrip.length=99 := by simp [roundTrip,UniformSelectedAxisFiberPreparation.program_length]
#eval IO.FS.writeFile "../logs/uniform-bytecode/tensor-fiber-copy/programs.json" (Json.compress (Json.mkObj [
 ("copy",.arr (UniformTensorFiberCopyMachine.program.map insJson).toArray),
 ("gather",.arr ((UniformSelectedAxisFiberPreparation.program false).map insJson).toArray),
 ("scatter",.arr ((UniformSelectedAxisFiberPreparation.program true).map insJson).toArray),
 ("roundTrip",.arr (roundTrip.map insJson).toArray),
 ("startupGather",.arr (startupGather.map insJson).toArray)]))
def axisSpec {k:ℕ} (rs:Fin k→ℕ) (i:Fin k) : Json :=
 let p:=UniformCRTTraversalCycle.place rs i.val
 let r:=rs i
 let q:=UniformTensorAddressMachine.upperCount rs i
 Json.mkObj [("axis",toJson i.val),("P",toJson p),("r",toJson r),("Q",toJson q),
 ("positions",toJson ((List.range (p*q)).map (fun j=>(List.range r).map (UniformTensorAddressMachine.address p r j))))]
def spec (n:ℕ) : Json :=
 let rs:=UniformSelectedCRT.radices n
 Json.mkObj [("n",toJson n),("radices",toJson (List.ofFn rs)),("L",toJson (UniformWorkingLength.workingLength n)),
 ("ell",toJson (UniformWorkingLength.axisCount n)),("M",toJson (UniformInitialPreparation.copyBase n)),
 ("D",toJson (UniformMasterRootMachine.order n)),
 ("axisSpecs",.arr ((List.finRange (UniformWorkingLength.axisCount n+1)).map (axisSpec rs)).toArray)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/tensor-fiber-copy/spec.json" (Json.compress (.arr
 (([1,2,3,5,11,40].map spec).toArray)))
example : UniformTensorAddressMachine.address 3 5 5 4=29 := rfl
example : UniformTensorAddressMachine.address 1 1 0 0=0 := rfl
