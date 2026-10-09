import UniformFinalKernelAndDataEntry
import UniformFinalDataClockProductExecution
import UniformFinalThirdClockOutput

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDFTExecution
open UniformMachine UniformFinalNumericJoin UniformSelectedPhysicalCRT UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
abbrev V(n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev W:ℕ:=UniformRecursiveSelfCallMachine.W
abbrev B(n:ℕ):ℕ:=UniformJointAllocation.envelope c n
attribute [local irreducible] Nat.add Nat.mul UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program

/-- One actual empty-start execution of the fixed twenty-stage program. The
three complete clock runs, saved spectrum and output are the same physical
states throughout; all preparation and continuation instructions are charged. -/
theorem execution {n:ℕ}(hn:0<n)(x:Fin n→ℂ):∃ticks:ℕ,∃u:State,
 BoundedExecution UniformFinalOuterProgram.program n x (B n) initial ticks u∧
 ComputesDFT n x u∧u.rootOrders=[UniformMasterRootMachine.order n]∧
 (ticks:ℝ)≤UniformFinalLinearTableCost.finalBudget c W n:=by
 let:NeZero (V n):=⟨Nat.ne_of_gt (UniformWorkingLength.workingLength_pos hn)⟩
 obtain ⟨s,ti,tc,tt,cacheEntry,start,prefixRun,initialCost,cacheCost,tableCost,pc,table,old,frame⟩:=
  UniformFinalPhysicalTablePrefix.execution hn x
 obtain ⟨kernelIn,kernelOut,dataIn,tk,first,kernelCost,history⟩:=
  UniformFinalKernelAndDataEntry.execution hn x cacheEntry start s old table frame prefixRun.final_bound
 let y:Fin (V n)→ℂ:=fun i=>kernelSpectrum (n:=n) (physicalBeta n i)
 let v:=UniformFinalRoleAlpha.physical x (physicalAlpha n)
 obtain ⟨dataOut,td,dataClock,dataCost,dataOutput⟩:=UniformActualCompleteClockExecution.execution hn x
  v {dataIn with pc:=0} history.entry.input history.entry.inputs history.entry.cache
 obtain ⟨productOut,thirdIn,middleReset,movement⟩:=UniformFinalDataClockProduct.execution hn x v y
  {dataIn with pc:=0} dataOut rfl dataClock dataOutput history.table.withPC history.entry.cache
  history.entry.input.source history.saved
 have middle:=UniformFinalKernelClockSave.stages_beforePC (p:=dataIn.pc) middleReset
 have saved:∀i:Fin (V n),dataOut.scalarHeap (UniformKernelSpectrumStorage.base c n+i.val)=
  kernelOut.scalarHeap (UniformFinalKernelAndDataEntry.DK n+i.val):=by
  intro i
  exact (dataOutput.spectrum i).trans (history.kernelSaved i)
 obtain ⟨thirdOut,tz,thirdClock,thirdCost,thirdOutput⟩:=UniformActualCompleteClockExecution.execution hn x
  (UniformFinalDataClockProduct.thirdValues (n:=n) dataOut y) {thirdIn with pc:=0}
  movement.entry.input movement.entry.inputs movement.entry.cache
 obtain ⟨u,last,dft,_roots,oneRoot,_pc⟩:=UniformFinalThirdClockOutput.execution hn x
  (UniformFinalDataClockProduct.thirdValues (n:=n) dataOut y) thirdIn thirdOut tz
  thirdClock thirdOutput movement.entry movement.table kernelIn kernelOut dataIn dataOut productOut
  history.kernelInput history.kernelRun history.kernelTags saved history.dataInput movement.transform movement.numeric movement.reindex
 have tail:LocalStages n (B n) x UniformFinalOuterSuffix.suffix s
  (UniformFinalOuterCostJoin.suffixCost n tk td tz) u:=by
  have joined:=(first.append middle).append last
  change LocalStages n (B n) x UniformFinalOuterSuffix.suffix s
   ((UniformFinalKernelAndDataEntry.cost n tk+(td+27*V n+27))+(tz+(18*V n+18)+(13*n+18))) u at joined
  convert joined using 1
  unfold UniformFinalOuterCostJoin.suffixCost UniformFinalKernelAndDataEntry.cost
  dsimp only[V,UniformFinalKernelAndDataEntry.W,UniformFinalKernelAndDataEntry.V,
   UniformFinalOuterCostJoin.W,UniformFinalOuterCostJoin.V]
  omega
 have run:=UniformFinalOuterSuffix.execution prefixRun pc tail
 have cheap:=UniformFinalOuterCostJoin.bound initialCost cacheCost tableCost kernelCost dataCost thirdCost
 exact ⟨_,_,run,dft,oneRoot,cheap⟩

/-- One fixed finite program computes the DFT at every positive length with
polynomially bounded machine words and the strictly sub-FFT asymptotic bound. -/
theorem uniformDFT:UniformDFTStatement UniformExponent.theta:=
 UniformFinalOuterEnvelope.of_execution (fun _ hn x=>execution hn x)

end
end ExactFourierCircuits.UniformFinalDFTExecution
