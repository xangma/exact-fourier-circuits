import UniformFinalOuterStartup
import UniformFinalCacheSource

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 three-transform construction and §5.4 Theorem 1.1 proof,
PDF pp.22-24 (`eq:chirp`, `thm:main`), with the model in §1.1, PDF p.2 (`sec:model`).

Startup, header, continuation and output bookkeeping refines the fixed
deterministic program. There is no separate paper counterpart for these state
layouts; the surrounding paper argument requires their preparation/index cost.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterStartup
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformAxisCachePreparationRetention UniformFinalStartupData
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
/-- Additive strengthening of the frozen startup prefix.6904 is the source
pointer produced by the real cache boot and retained by its actual terminal axis. -/
theorem execution_with_source (table:Program){n:ℕ}(hn:0<n) (x:Fin n→ℂ)
 (tableFit:table.length≤UniformJointAllocation.fixed c):∃s ti tc cacheEntry,
 BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) initial (ti+62+67+tc) s∧
 ti≤UniformAllAxisConjugatePreparation.fullBudget n∧
 tc≤20+UniformAllAxisSeedPreparation.axisCount n*UniformAxisCacheLoopState.maxBudget c n+1∧
 s.pc=6243∧Result n hn x cacheEntry s∧s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n:=by
 obtain ⟨a,ti,prefixRun,budget,ap,core,bank,data,headers⟩:=
  UniformFinalStartupPrefix.execution table hn x tableFit
 have fit:=UniformFinalOuterProgram.code_envelope table n tableFit
 have length:=UniformFinalOuterProgram.programFor_length table
 have room:6243≤UniformJointAllocation.envelope c n:=by omega
 let a0:=setPC a 0
 have slab:a0.natReg 6020=UniformJointAllocation.slab c n:=by
  have h:=headers 0 (by decide)
  simpa only[a0,setPC,Nat.add_zero,UniformJointAllocationMachine.factors,List.getElem_cons_zero,Nat.one_mul] using h
 obtain ⟨u,tc,run,cost,_,out,low⟩:=UniformAxisCacheWholeExecution.execution_low c n hn x a0
  core.withPC slab bank rfl (changePC_bound _ a 0 prefixRun.final_bound (by omega))
 have source:=UniformFinalCacheSource.execution_source c n hn x a0 u tc core.withPC slab bank rfl
  (changePC_bound _ a 0 prefixRun.final_bound (by omega)) run
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed (UniformFinalStartupCode.cache_code table)
  (by rw[UniformAxisCacheWholeProgram.program_length];omega) (by omega:6243≤UniformJointAllocation.envelope c n) run
 have same:placed 1589 a0=a:=by
  change {a with pc:=1589+0}=a
  simp only[Nat.add_zero,←ap]
 rw[same] at placedRun
 let s:=setPC u 6243
 change BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) a tc s at placedRun
 have header:UniformAllAxisSeedPreparation.Header n (UniformAllAxisSeedPreparation.axisCount n) s:=by
  constructor
  all_goals first
  | exact (UniformFinalCacheRegisters.execution run 200 (Or.inl ⟨by omega,by omega⟩)).trans core.header.index
  | exact (UniformFinalCacheRegisters.execution run 201 (Or.inl ⟨by omega,by omega⟩)).trans core.header.offset
  | exact (UniformFinalCacheRegisters.execution run 202 (Or.inl ⟨by omega,by omega⟩)).trans core.header.count
  | exact (UniformFinalCacheRegisters.execution run 203 (Or.inl ⟨by omega,by omega⟩)).trans core.header.one
  | exact (UniformFinalCacheRegisters.execution run 204 (Or.inl ⟨by omega,by omega⟩)).trans core.header.directory
  | exact (UniformFinalCacheRegisters.execution run 209 (Or.inl ⟨by omega,by omega⟩)).trans core.header.zero
 have input:=out.input.withPC (pc:=6243)
 have finalCore:Core n x s:=⟨header,input.metadata,input.operands,input.original,input.conjugate⟩
 have lowFinal:UniformCacheLowRetention.Frame n a s:=⟨low.nat,low.scalar⟩
 have finalData:Data n x s:=⟨fun j=>(lowFinal.alpha_copied hn j).trans (data.gathered j),
  lowFinal.beta_inverse hn data.inverse,out.roots.trans data.roots,out.outputs.trans data.outputs⟩
 have cache:UniformAxisCacheWholeExecution.Output c n hn x a s:=
  ⟨input,out.bank,out.all.transport rfl rfl,out.clock,out.savedNat,out.savedScalar,
   out.natEnd,out.scalarEnd,out.outputs,out.roots⟩
 refine ⟨s,ti,tc,a,prefixRun.trans placedRun,budget,cost,rfl,⟨cache,ap,data.roots,data.outputs,finalCore,finalData,?_⟩,source⟩
 intro i hi
 exact (UniformFinalCacheRegisters.execution run (6020+i) (Or.inr ⟨by omega,by omega⟩)).trans (headers i hi)
end
end ExactFourierCircuits.UniformFinalOuterStartup
