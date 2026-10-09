import UniformFinalCallerFacts
import UniformFinalKernelClockSave
import UniformActualCompleteClockExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalKernelAndDataEntry
open UniformMachine UniformFinalNumericJoin UniformSelectedPhysicalCRT UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
abbrev V(n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev W:ℕ:=UniformRecursiveSelfCallMachine.W
abbrev A(n:ℕ):ℕ:=UniformActualClockEntry.sourceBase n
abbrev DK(n:ℕ):ℕ:=A n+V n
abbrev Q(n:ℕ):ℕ:=UniformKernelSpectrumStorage.base c n
abbrev B(n:ℕ):ℕ:=UniformJointAllocation.envelope c n
attribute [local irreducible] UniformActualGlobalClockProgram.program

def stages:List Program:=[
 UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W true),UniformRoleInputMachine.program,
 UniformActualGlobalClockProgram.program,UniformKernelSpectrumCopy.program,
 UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W false),UniformRoleInputMachine.program,
 UniformPhysicalCRTConsumerMachine.alphaProgram]
def cost(n ticks:ℕ):ℕ:=(18+(5*(W*V n)+16*V n+24))+(ticks+7*V n+9)+
 (19+(5*(W*V n)+16*V n+24)+(9*V n+10))

structure Result {n:ℕ}[NeZero (V n)](hn:0<n)(x:Fin n→ℂ)(kernelIn kernelOut dataIn:State):Prop where
 kernelInput:NumericValues (DK n) (fun i=>kernel (n:=n) (physicalAlpha n i)) kernelIn
 kernelRun:HeapTransform (physicalAlpha n) (physicalBeta n) (DK n) (DK n) kernelIn kernelOut
 kernelTags:∀i,(scalars (V n) (DK n) kernelOut i).dependent=false
 kernelSaved:∀i:Fin (V n),dataIn.scalarHeap (Q n+i.val)=kernelOut.scalarHeap (DK n+i.val)
 saved:∀i:Fin (V n),dataIn.scalarHeap (Q n+i.val)=
  some (UniformPairMachine.prepared (kernelSpectrum (n:=n) (physicalBeta n i)))
 dataInput:NumericValues (A n) (fun i=>data x (physicalAlpha n i)) dataIn
 entry:UniformFinalClockEntries.Entry hn x
  (UniformFinalRoleAlpha.physical x (physicalAlpha n)) {dataIn with pc:=0}
 table:UniformFinalPhysicalTablePrefix.Result n x dataIn

/-- Execute the actual kernel loader, first complete clock, save15, data loader
and physical AP gather. The saved spectrum refers to that same first run. -/
theorem execution {n:ℕ}[NeZero (V n)](hn:0<n)(x:Fin n→ℂ)(cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (table:UniformFinalPhysicalTablePrefix.Result n x s)
 (prefixFrame:UniformFinalPhysicalTablePrefix.Frame n start s)(wb:WordBound (B n) s):
 ∃kernelIn kernelOut dataIn ticks,
 LocalStages n (B n) x stages s (cost n ticks) dataIn∧
 (ticks:ℝ)≤UniformFinalClockCost.clockEnvelope W n∧Result hn x kernelIn kernelOut dataIn:=by
 obtain ⟨kernelIn,loader,kEntry,kTable,prepared,kInput,_outer⟩:=
  UniformFinalRoleTableEntries.kernel hn x cacheEntry start s old table prefixFrame wb
 obtain ⟨kernelOut,ticks,clock,cheap,output⟩:=UniformActualCompleteClockExecution.execution hn x
  (UniformFinalRoleModel.values x true (physicalAlpha n)) {kernelIn with pc:=0}
  kEntry.input kEntry.inputs kEntry.cache
 have tableK:UniformFinalPhysicalTablePrefix.Result n x kernelIn:=kTable.withPC
 have cacheK:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) kernelIn:=by
  intro j hj
  exact UniformAxisCacheContents.transport (kEntry.cache j hj) ⟨by intros;rfl,by intros;rfl⟩
 obtain ⟨saved,saveRun,kept⟩:=UniformFinalKernelClockSave.execution_local hn x
  (UniformFinalRoleModel.values x true (physicalAlpha n)) kernelIn kernelOut
  clock output tableK cacheK kEntry.input.source prepared kInput
 obtain ⟨dataIn,dataRun,dEntry,dInput,dFrame,storage⟩:=UniformFinalRoleStorageEntries.data hn x
  cacheEntry start saved old kept.table (UniformFinalCallerFacts.saved_of_runtime old kept.runtime)
  kept.cache (UniformFinalRoleCaller.LocalStages.bound saveRun)
 have outer:=UniformFinalClockOuterRetention.Frame.role_of_table hn dFrame kept.table storage
 have dataTable:=outer.table hn kept.table
 have spectrum:=UniformFinalClockOuterRetention.Spectrum.role hn dFrame
 have joined:LocalStages n (B n) x stages s (cost n ticks) dataIn:=by
  exact (loader.append saveRun).append dataRun
 refine ⟨kernelIn,kernelOut,dataIn,ticks,joined,cheap,?_⟩
 refine ⟨kInput,kept.transform,?_,?_,?_,dInput,dEntry,dataTable⟩
 · intro i
   change ((kernelOut.scalarHeap (UniformFinalKernelClockSave.kernelBase n+i.val)).getD Scalar.zero).dependent=false
   rw[kept.kernelCells i]
   rfl
 · intro i
   exact (spectrum i).trans (kept.copied i)
 · intro i
   exact (spectrum i).trans (kept.saved i)
end
end ExactFourierCircuits.UniformFinalKernelAndDataEntry
