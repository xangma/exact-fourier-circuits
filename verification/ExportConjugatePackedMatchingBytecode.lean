import UniformConjugatePackedMatchingPreparation
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


#eval IO.FS.createDirAll "../logs/uniform-bytecode/conjugate-packed-matching"
#eval IO.FS.writeFile "../logs/uniform-bytecode/conjugate-packed-matching/programs.json"
 (Json.compress (Json.mkObj [
  ("originalRank",.arr (UniformSeedRankCrossPreparation.program.map insJson).toArray),
  ("producer",.arr (UniformConjugatePackedMatchingPreparation.program.map insJson).toArray),
  ("spectrum",.arr (UniformConjugateRankSpectrumPreparation.program.map insJson).toArray),
  ("matching",.arr (UniformPackedMatchingShearMachine.program.map insJson).toArray),
  ("reverse",.arr (UniformSpectrumReversalMachine.program.map insJson).toArray),
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

#eval IO.FS.writeFile "../logs/uniform-bytecode/conjugate-packed-matching/spec.json"
 (Json.compress (Json.mkObj [
 ("models",.arr #[model 1,model 4]),
 ("widths",toJson ((List.range 4).map UniformRadixTwoDAG.width)),
 ("counts",toJson ((List.range 4).map UniformRadixTwoDAG.count)),
 ("convolutionGates",toJson ((List.range 4).map UniformToeplitzCrossTopologyMachine.G))]))
example : UniformConjugateRankSpectrumPreparation.program.length=763 := UniformConjugateRankSpectrumPreparation.program_length
example : UniformSpectrumReversalMachine.program.length=18 := UniformSpectrumReversalMachine.program_length
example (p:UniformRankCrossPreparationMachine.Parameters) :
 (UniformConjugateRankSpectrumPreparation.selected 1 (0:Fin (UniformAllAxisSeedPreparation.axisCount 1)) p).H=
 UniformAllAxisConjugatePreparation.axisBase 1 0+3*UniformAllAxisSeedPreparation.radix 1 0 := rfl

example : UniformConjugatePackedMatchingPreparation.program.length=1198 := UniformConjugatePackedMatchingPreparation.program_length
