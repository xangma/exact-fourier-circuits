import UniformFinalStartupPrefix
import UniformFinalCacheRegisters
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterStartup
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformAxisCachePreparationRetention UniformFinalStartupData
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
structure Result (n:ℕ) (hn:0<n) (x:Fin n→ℂ) (cacheEntry s:State):Prop where
 cache:UniformAxisCacheWholeExecution.Output c n hn x cacheEntry s
 cacheEntryPC:cacheEntry.pc=1589
 cacheEntryRoots:cacheEntry.rootOrders=[UniformMasterRootMachine.order n]
 cacheEntryOutputs:cacheEntry.outputs=initial.outputs
 core:Core n x s
 data:Data n x s
 headers:∀i,(hi:i<18)→s.natReg (6020+i)=UniformJointAllocationMachine.factors[i]*UniformJointAllocation.slab c n

/-- Actual empty-start execution of the first four stages of the single final
program. No prepared cache, table, permutation, or allocator header is assumed. -/
theorem execution (table:Program){n:ℕ}(hn:0<n) (x:Fin n→ℂ)
 (tableFit:table.length≤UniformJointAllocation.fixed c):∃s ti tc cacheEntry,
 BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) initial (ti+62+67+tc) s∧
 ti≤UniformAllAxisConjugatePreparation.fullBudget n∧
 tc≤20+UniformAllAxisSeedPreparation.axisCount n*UniformAxisCacheLoopState.maxBudget c n+1∧
 s.pc=6243∧Result n hn x cacheEntry s:=by
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
 refine ⟨s,ti,tc,a,prefixRun.trans placedRun,budget,cost,rfl,cache,ap,data.roots,data.outputs,finalCore,finalData,?_⟩
 intro i hi
 exact (UniformFinalCacheRegisters.execution run (6020+i) (Or.inr ⟨by omega,by omega⟩)).trans (headers i hi)
end
end ExactFourierCircuits.UniformFinalOuterStartup
