import UniformEmptyStartupBranchPreparation
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



#eval IO.FS.createDirAll "../logs/uniform-bytecode/empty-startup-matching"
#eval IO.FS.writeFile "../logs/uniform-bytecode/empty-startup-matching/programs.json" (Json.compress (Json.mkObj [
 ("selected",.arr (UniformEmptyStartupMatchingPreparation.program.map insJson).toArray),
 ("branch",.arr (UniformEmptyStartupBranchPreparation.program.map insJson).toArray),
 ("fallback",.arr (UniformRetainedDirectDFTFallback.program.map insJson).toArray),
 ("body",.arr (UniformRetainedDirectDFTFallback.body.map insJson).toArray),
 ("initializer",.arr (UniformEmptyStartupMatchingPreparation.initializer.map UniformTensorMonomialMachine.Op.code |>.map insJson).toArray),
 ("startup",.arr (UniformAllAxisConjugatePreparation.fullProgram.map insJson).toArray)]))
def model (n : Nat) : Json := Json.mkObj [
 ("n",toJson n),("axisCount",toJson (UniformAllAxisSeedPreparation.axisCount n)),
 ("ell",toJson (UniformInitialPreparation.ell n)),("L",toJson (UniformInitialPreparation.len n)),
 ("copyBase",toJson (UniformInitialPreparation.copyBase n)),
 ("amount",toJson (UniformGlobalNatPreparation.amount (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n))),
 ("directory",toJson (UniformAllAxisSeedPreparation.directoryBase n)),
 ("pool",toJson (UniformLocalSeedTableMachine.poolBase n)),
 ("destination",toJson (UniformSeedConjugatePreparation.destination n)),
 ("conjugatePool",toJson (UniformAllAxisConjugatePreparation.pool n)),
 ("conjugateDirectory",toJson (UniformAllAxisConjugatePreparation.directoryBase n)),
 ("masterOrder",toJson (UniformMasterRootMachine.order n)),
 ("nextPrime",toJson (UniformWorkingLength.nextPrime n)),
 ("radices",toJson ((List.range (UniformAllAxisSeedPreparation.axisCount n)).map (UniformAllAxisSeedPreparation.radixAt n))),
 ("runtime",toJson (UniformAllAxisConjugatePreparation.preparationRuntime n)),
 ("budget",toJson (UniformAllAxisConjugatePreparation.preparationBudget n))]

#eval IO.FS.writeFile "../logs/uniform-bytecode/empty-startup-matching/spec.json"
 (Json.compress (Json.mkObj [("models",.arr #[model 1,model 4]),
 ("threshold",toJson (194:Nat)),("selectedAxis",toJson (193:Nat)),
 ("scales",toJson UniformEmptyStartupMatchingPreparation.allScales)]))
example:UniformEmptyStartupMatchingPreparation.program.length=4255:=UniformEmptyStartupMatchingPreparation.program_length
example:UniformRetainedDirectDFTFallback.program.length=49:=UniformRetainedDirectDFTFallback.program_length
example:UniformEmptyStartupBranchPreparation.program.length=4306:=UniformEmptyStartupBranchPreparation.program_length
