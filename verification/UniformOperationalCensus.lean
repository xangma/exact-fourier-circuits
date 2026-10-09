import UniformBinarySpectatorCMachine
import UniformNativeScalarRecordMachine
import UniformNativeExchangeRecordMachine
import UniformDirectLeafDescriptorMachine
import UniformTransposeDescriptorMachine
import UniformDirectLeafOrientationsMachine
import UniformPhysicalBinaryInverse
import UniformNativeCopiedInverse
import UniformGlobalTensorDiagonalMachine
import UniformGlobalTensorDiagonalLoop
import UniformSectorTransposeMachine
import UniformSectorChildEntryPreparation
import UniformSectorRestoringScatterPreparation
import UniformAllSectorTransposeMachine
import UniformSectorTransposeCoordinates
import UniformProducedSectorTransposePreparation
import UniformSectorPhysicalBinaryAction
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mods := ["UniformBinarySpectatorCMachine", "UniformNativeScalarRecordMachine", "UniformNativeExchangeRecordMachine", "UniformDirectLeafDescriptorMachine", "UniformTransposeDescriptorMachine", "UniformDirectLeafOrientationsMachine", "UniformPhysicalBinaryInverse", "UniformNativeCopiedInverse", "UniformGlobalTensorDiagonalMachine", "UniformGlobalTensorDiagonalLoop", "UniformSectorTransposeMachine", "UniformSectorChildEntryPreparation", "UniformSectorRestoringScatterPreparation", "UniformAllSectorTransposeMachine", "UniformSectorTransposeCoordinates", "UniformProducedSectorTransposePreparation", "UniformSectorPhysicalBinaryAction"]
 let mut entries:Array Json:=#[]
 for (name, _) in env.constants.toList do
  let source := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)
  if source.any (fun m => m ∈ mods) then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   entries:=entries.push (Json.mkObj [("module",toJson source),("name",toJson name.toString),("axioms",toJson (axioms.toList.map toString))])
 liftIO <| IO.FS.writeFile "../logs/uniform-operational-foundations/census.json" (Json.compress (.arr entries))
 logInfo m!"Audited {entries.size} declarations in {mods.length} modules"
