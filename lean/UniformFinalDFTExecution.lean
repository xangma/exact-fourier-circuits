import UniformFinalKernelAndDataEntry
import UniformFinalDataClockProductExecution
import UniformFinalThirdClockOutput

/-!
# The actual all-length DFT execution

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Theorem 1.1,
PDF p. 2 (`thm:main`); §5.2–§5.4, PDF pp. 22–24. The three clock calls
implement the three transforms of §5.3, (5.7), PDF pp. 22–23 (`eq:chirp`).
Explicit machine headers, saved heap banks, continuations and envelope
joins are implementation bookkeeping for that argument, without separate
one-to-one paper lemmas. The quantitative route uses the network/local/
synchronization interfaces of Theorem 2.6, Proposition 3.1 and
Proposition 4.2 (PDF pp. 11–12, 19–20), not the optional §A synthesis route.
-/

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
 /- §5.1–§5.3, (5.3)–(5.9), PDF pp. 21–23: choose L, prepare the
 single master root and local scalars, then build the physical CRT tables.
 This prefix starts with empty heaps and contributes its own tick cost. -/
 let:NeZero (V n):=⟨Nat.ne_of_gt (UniformWorkingLength.workingLength_pos hn)⟩
 obtain ⟨s,ti,tc,tt,cacheEntry,start,prefixRun,initialCost,cacheCost,tableCost,pc,table,old,frame⟩:=
  UniformFinalPhysicalTablePrefix.execution hn x
 /- §5.3, PDF p. 23: the fixed convolution operand is transformed first
 and its spectrum saved as prepared scalars, charging a full transform. -/
 obtain ⟨kernelIn,kernelOut,dataIn,tk,first,kernelCost,history⟩:=
  UniformFinalKernelAndDataEntry.execution hn x cacheEntry start s old table frame prefixRun.final_bound
 let y:Fin (V n)→ℂ:=fun i=>kernelSpectrum (n:=n) (physicalBeta n i)
 let v:=UniformFinalRoleAlpha.physical x (physicalAlpha n)
 /- §5.2–§5.3, (5.5)–(5.7), PDF pp. 22–23: transform the chirped
 variable input in the CRT ordering, multiply by the saved fixed spectrum,
 then permute back to the input ordering for the third forward transform. -/
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
 /- §5.2, PDF p. 22: F_L^{-1}=L^{-1}JF_L. The third clock is a forward
 transform; actual CRT/output stages perform reversal, scaling and the
 output chirp, establishing F_n x in the requested index order. -/
 obtain ⟨thirdOut,tz,thirdClock,thirdCost,thirdOutput⟩:=UniformActualCompleteClockExecution.execution hn x
  (UniformFinalDataClockProduct.thirdValues (n:=n) dataOut y) {thirdIn with pc:=0}
  movement.entry.input movement.entry.inputs movement.entry.cache
 obtain ⟨u,last,dft,_roots,oneRoot,_pc⟩:=UniformFinalThirdClockOutput.execution hn x
  (UniformFinalDataClockProduct.thirdValues (n:=n) dataOut y) thirdIn thirdOut tz
  thirdClock thirdOutput movement.entry movement.table kernelIn kernelOut dataIn dataOut productOut
  history.kernelInput history.kernelRun history.kernelTags saved history.dataInput movement.transform movement.numeric movement.reindex
 /- §5.3–§5.4, PDF pp. 23–24: compose the same physical endpoints and
 sum every preparation/continuation/transform/movement/output instruction.
 LocalStages.append and the suffix linker are bookkeeping, not assumed
 transform or child-cost oracles. -/
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
 /- Theorem 1.1 and (1.2), PDF p. 2; final argument §5.4, pp. 23–24.
 Corollary 1.2's decimal bound additionally absorbs (log log n)^(4-theta);
 that analytic absorption is not asserted by this declaration. -/
 UniformFinalOuterEnvelope.of_execution (fun _ hn x=>execution hn x)

end
end ExactFourierCircuits.UniformFinalDFTExecution
