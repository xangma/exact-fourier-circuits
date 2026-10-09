import UniformRecursiveReturnStackMachine
import UniformRecursiveBaseCallMachine
import UniformRecursiveSelfCallMachine
import UniformResidualTraversalHeaders
import UniformResidualImagePreparation
import UniformResidualSpectators
import UniformResidualSpectatorBankMachine
import UniformResidualGeneralPreparation
import UniformResidualGeneralGatherPreparation
import UniformRecursiveResidualRecordPreparation
import UniformRecursiveRegisterFrames
import UniformResidualExtendedPermutation
import UniformRecursiveResidualGatherRecordMachine
import UniformRecursiveBatchGroupMachine
import UniformResidualNativeTranslationMachine
import UniformNativePreparedYTranslationMachine
import UniformNativeYRecordMachine
import UniformRecursiveSavingProgram
import UniformRecursiveNativeEntries
import UniformRecursiveSavingExecution
import UniformRecursiveNodePreparation
import UniformRecursiveNodeJoin
import UniformRecursiveParentReturn
import UniformRecursiveRecordControl
import UniformRecursiveNativeRecords
import UniformRecursiveSpectatorFinish
import UniformRecursiveSpectatorValues
import UniformRecursiveResidualControl
import UniformRecursivePaddingControl
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let wanted : Array String := #["UniformRecursiveReturnStackMachine","UniformRecursiveBaseCallMachine","UniformRecursiveSelfCallMachine","UniformResidualTraversalHeaders","UniformResidualImagePreparation","UniformResidualSpectators","UniformResidualSpectatorBankMachine","UniformResidualGeneralPreparation","UniformResidualGeneralGatherPreparation","UniformRecursiveResidualRecordPreparation","UniformRecursiveRegisterFrames","UniformResidualExtendedPermutation","UniformRecursiveResidualGatherRecordMachine","UniformRecursiveBatchGroupMachine","UniformResidualNativeTranslationMachine","UniformNativePreparedYTranslationMachine","UniformNativeYRecordMachine","UniformRecursiveSavingProgram","UniformRecursiveNativeEntries","UniformRecursiveSavingExecution","UniformRecursiveNodePreparation","UniformRecursiveNodeJoin","UniformRecursiveParentReturn","UniformRecursiveRecordControl","UniformRecursiveNativeRecords","UniformRecursiveSpectatorFinish","UniformRecursiveSpectatorValues","UniformRecursiveResidualControl","UniformRecursivePaddingControl"]
 let mut entries : Array Json := #[]
 for (name, _) in env.constants.toList do
  let origin := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)
  if origin.any wanted.contains then
   let axs ← collectAxioms name
   for ax in axs do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   entries := entries.push (Json.mkObj [("name",toJson name.toString),("module",toJson origin),("axioms",toJson (axs.toList.map toString))])
 liftIO <| IO.FS.writeFile "../logs/uniform-recursive-foundations-promotion-agent-20261009/census.json" (Json.compress (.arr entries))
 logInfo m!"Audited {entries.size} declarations"
