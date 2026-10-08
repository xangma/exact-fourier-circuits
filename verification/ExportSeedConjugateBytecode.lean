import UniformSeedConjugatePreparation
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

#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-conjugate/program.json"
  (Json.compress (.arr (UniformSeedConjugatePreparation.program.map insJson).toArray))
#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-conjugate/startup.json"
  (Json.compress (.arr (UniformAllAxisSeedPreparation.fullProgram.map insJson).toArray))
#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-conjugate/original-axis-loop.json"
  (Json.compress (.arr (UniformAllAxisSeedPreparation.program.map insJson).toArray))
def model (n : Nat) : Json := Json.mkObj [
 ("n",toJson n),("axisCount",toJson (UniformAllAxisSeedPreparation.axisCount n)),
 ("ell",toJson (UniformInitialPreparation.ell n)),("L",toJson (UniformInitialPreparation.len n)),
 ("copyBase",toJson (UniformInitialPreparation.copyBase n)),
 ("amount",toJson (UniformGlobalNatPreparation.amount (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n))),
 ("directory",toJson (UniformAllAxisSeedPreparation.directoryBase n)),
 ("pool",toJson (UniformLocalSeedTableMachine.poolBase n)),
 ("destination",toJson (UniformSeedConjugatePreparation.destination n)),
 ("masterOrder",toJson (UniformMasterRootMachine.order n)),
 ("nextPrime",toJson (UniformWorkingLength.nextPrime n)),
 ("radices",toJson ((List.range (UniformAllAxisSeedPreparation.axisCount n)).map (UniformAllAxisSeedPreparation.radixAt n))),
 ("runtimes",toJson ((List.range (UniformAllAxisSeedPreparation.axisCount n)).map fun j=>
   let r:=UniformAllAxisSeedPreparation.radixAt n j
   UniformReciprocalMachine.completeRuntime r+40*r+148))]
#eval IO.FS.writeFile "../logs/uniform-bytecode/seed-conjugate/models.json"
  (Json.compress (.arr #[model 1,model 2,model 4,model 5]))
example:UniformSeedConjugatePreparation.program.length=466:=UniformSeedConjugatePreparation.program_length
