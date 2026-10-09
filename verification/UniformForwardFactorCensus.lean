import UniformForwardMatchingFactorHeaderExecution
import UniformForwardMatchingFactorTensorBridge
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let wanted : Array String := #["UniformForwardMatchingFactorPreparation","UniformForwardMatchingFactorGeometry","UniformForwardMatchingFactorSetup","UniformForwardMatchingFactorFrame","UniformForwardMatchingFactorChunk","UniformForwardMatchingFactorTranslation","UniformForwardMatchingFactorExecution","UniformForwardMatchingFactorValues","UniformForwardMatchingFactorHeaderPreparation","UniformForwardMatchingFactorHeaderExecution","UniformForwardMatchingFactorTensorBridge"]
 let mut entries : Array Json := #[]
 for (name, _) in env.constants.toList do
  let origin := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx]!.toString)
  if origin.any wanted.contains then
   let axs ← collectAxioms name
   for ax in axs do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   entries := entries.push (Json.mkObj [("name",toJson name.toString),("module",toJson origin),("axioms",toJson (axs.toList.map toString))])
 liftIO <| IO.FS.writeFile "../logs/uniform-forward-factor-normal-agent-20261009/census.json" (Json.compress (.arr entries))
 logInfo m!"Audited {entries.size} declarations"
