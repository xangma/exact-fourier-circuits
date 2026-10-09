import UniformFinalPhysicalTableExecution
import UniformSequentialExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPhysicalTablePrefix
open UniformMachine UniformTensorMonomialMachine UniformAssembly UniformSequentialAssembly
open UniformNatBlockMachine UniformFastPhysicalCRTMachine UniformFinalPhysicalTableGeometry
open UniformAxisCachePreparationRetention UniformFinalStartupData UniformSelectedPhysicalCRT
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
local notation "fast"=>UniformFastPhysicalCRTMachine.program
local notation "ops"=>UniformPhysicalCRTTableHeaders.operations
local notation "B" n=>UniformJointAllocation.envelope c n
attribute [local irreducible] UniformAllAxisConjugatePreparation.fullProgram
 UniformJointAllocationMachine.program UniformJointCacheWorkspaceMachine.program UniformAxisCacheWholeProgram.program

lemma header_code:CodeAt (natProgram ops) (UniformFinalOuterProgram.programFor fast) 6243 6263:=by
 let before:List Program:=[UniformAllAxisConjugatePreparation.fullProgram,
  UniformJointAllocationMachine.program c,UniformJointCacheWorkspaceMachine.program,UniformAxisCacheWholeProgram.program]
 have h:=stage_code before (natProgram ops) ((UniformFinalOuterProgram.stagesFor fast).drop 5)
 have shape:before++natProgram ops::(UniformFinalOuterProgram.stagesFor fast).drop 5=UniformFinalOuterProgram.stagesFor fast:=rfl
 rw[shape] at h
 simpa only[UniformFinalOuterProgram.programFor,before,size,Nat.add_zero,
  UniformAllAxisConjugatePreparation.fullProgram_length,UniformJointAllocationMachine.program_length,
  UniformJointCacheWorkspaceMachine.program_length,UniformAxisCacheWholeProgram.program_length,
  natProgram_length,UniformPhysicalCRTTableHeaders.operations_length,Nat.reduceAdd] using h
lemma table_code:CodeAt fast (UniformFinalOuterProgram.programFor fast) 6263 6316:=by
 let before:List Program:=[UniformAllAxisConjugatePreparation.fullProgram,
  UniformJointAllocationMachine.program c,UniformJointCacheWorkspaceMachine.program,UniformAxisCacheWholeProgram.program,natProgram ops]
 have h:=stage_code before fast ((UniformFinalOuterProgram.stagesFor fast).drop 6)
 have shape:before++fast::(UniformFinalOuterProgram.stagesFor fast).drop 6=UniformFinalOuterProgram.stagesFor fast:=rfl
 rw[shape] at h
 simpa only[UniformFinalOuterProgram.programFor,before,size,Nat.add_zero,
  UniformAllAxisConjugatePreparation.fullProgram_length,UniformJointAllocationMachine.program_length,
  UniformJointCacheWorkspaceMachine.program_length,UniformAxisCacheWholeProgram.program_length,
  natProgram_length,UniformPhysicalCRTTableHeaders.operations_length,UniformFastPhysicalCRTMachine.program_length,Nat.reduceAdd] using h

structure Frame(n:ℕ)(s u:State):Prop where
 natHeap:∀q,q<(addresses c n).physicalAlpha→u.natHeap q=s.natHeap q
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,¬UniformPhysicalCRTTableHeaders.Changed q→(q<7800∨7816<q)→u.natReg q=s.natReg q

structure Result(n:ℕ)(x:Fin n→ℂ)(s:State):Prop where
 core:Core n x s
 data:Data n x s
 headers:∀i,(hi:i<18)→s.natReg (6020+i)=UniformJointAllocationMachine.factors[i]*UniformJointAllocation.slab c n
 source:s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n
 tableArgs:UniformPhysicalCRTTableHeaders.Args c n s
 alpha:UniformGlobalNatPreparation.PermutationBank (UniformInitialPreparation.len n)
  (UniformKernelSpectrumStorage.alphaBase c n) s.natHeap (physicalAlpha n)
 inverse:UniformGlobalNatPreparation.PermutationBank (UniformInitialPreparation.len n)
  (UniformKernelSpectrumStorage.betaInverseBase c n) s.natHeap (physicalBeta n).symm

lemma table_args_frame{n:ℕ}{s u:State}(h:UniformPhysicalCRTTableHeaders.Args c n s)
 (f:UniformFastPhysicalCRTMachine.Frame s u):UniformPhysicalCRTTableHeaders.Args c n u:=by
 constructor
 all_goals first
 | exact (f.natReg _ (by omega)).trans h.alpha
 | exact (f.natReg _ (by omega)).trans h.inverse
 | exact (f.natReg _ (by omega)).trans h.storage
 | exact (f.natReg _ (by omega)).trans h.axes
 | exact (f.natReg _ (by omega)).trans h.volume
 | exact ((f.natReg _ (by omega)).trans h.seed).trans (f.natReg 6904 (by omega)).symm
 | exact (f.natReg _ (by omega)).trans h.sourceAlpha
 | exact (f.natReg _ (by omega)).trans h.sourceBeta
 | exact (f.natReg _ (by omega)).trans h.destAlpha
 | exact (f.natReg _ (by omega)).trans h.destInverse
 | exact (f.natReg _ (by omega)).trans h.work

lemma header_args_pc{C:UniformJointAllocation.Constants}{n:ℕ}{s:State}
 (h:UniformPhysicalCRTTableHeaders.Args C n s)(pc:ℕ):
 UniformPhysicalCRTTableHeaders.Args C n (setPC s pc):=
 ⟨h.alpha,h.inverse,h.storage,h.axes,h.volume,h.seed,h.sourceAlpha,h.sourceBeta,h.destAlpha,h.destInverse,h.work⟩

/-- One continuous prefix of the actual final program: empty-start startup,
charged header20, then the actual selected fast53. No host table installation
or free program-counter reset appears in the resulting run. -/
theorem execution{n:ℕ}(hn:0<n)(x:Fin n→ℂ):∃s ti tc tt cacheEntry start,
 BoundedRuns (UniformFinalOuterProgram.programFor fast) n x (B n) initial (ti+62+67+tc+20+tt) s∧
 ti≤UniformAllAxisConjugatePreparation.fullBudget n∧
 tc≤20+UniformAllAxisSeedPreparation.axisCount n*UniformAxisCacheLoopState.maxBudget c n+1∧
 tt≤60*(UniformInitialPreparation.len n+UniformAllAxisSeedPreparation.axisCount n+1)∧
 s.pc=6316∧Result n x s∧UniformFinalOuterStartup.Result n hn x cacheEntry start∧Frame n start s:=by
 have tableFit:(fast).length≤UniformJointAllocation.fixed c:=by
  rw[UniformFastPhysicalCRTMachine.program_length];have h:=UniformJointAllocation.fixed_large c;omega
 obtain ⟨a,ti,tc,cacheEntry,run,icost,ccost,ap,out,source⟩:=
  UniformFinalOuterStartup.execution_with_source fast hn x tableFit
 have codefit:=UniformFinalOuterProgram.code_envelope fast n tableFit
 have length:=UniformFinalOuterProgram.programFor_length fast
 have room:6316≤B n:=by rw[UniformFastPhysicalCRTMachine.program_length] at length;omega
 have hsource:a.natReg 6026=2*UniformJointAllocation.slab c n:=by
  have h:=out.headers 6 (by decide)
  simpa only[Nat.reduceAdd,UniformJointAllocationMachine.factors,List.getElem_cons_succ,List.getElem_cons_zero] using h
 let a0:=setPC a 0
 have safety:=UniformFinalPhysicalTableInputs.safe c hn x a0 out.core.withPC hsource source
 have headerRun:=nat_execution ops x a0 rfl
  (changePC_bound _ a 0 run.final_bound (by omega))
  (by rw[UniformPhysicalCRTTableHeaders.operations_length];omega) safety.1 safety.2
 have placedHeader:=UniformBoundedAssembly.boundedExecution_placed header_code
  (by rw[natProgram_length,UniformPhysicalCRTTableHeaders.operations_length];omega)
  (by omega:6263≤B n) headerRun
 have same:placed 6243 a0=a:=by
  change {a with pc:=6243+0}=a
  simp only[Nat.add_zero,←ap]
 rw[same] at placedHeader
 let h:=applyBlock ops a0
 let h0:=setPC h 0
 have hcore:Core n x h:=UniformFinalPhysicalTableInputs.header_core c hn x a0 out.core.withPC
 have hdata:Data n x h:=UniformFinalPhysicalTableInputs.header_data a0 out.data.withPC
 have args:=UniformFinalPhysicalTableInputs.installed c hn x a0 out.core.withPC hsource source
 obtain ⟨tt,u,tableRun,tcost,up,ua,uc,uf,uh,alpha,inverse⟩:=
  UniformFinalPhysicalTableExecution.execution c hn x h0 rfl (args_pc args 0) hcore.withPC
   (changePC_bound _ h 0 headerRun.final_bound (by omega))
 have placedTable:=UniformBoundedAssembly.boundedExecution_placed table_code
  (by rw[UniformFastPhysicalCRTMachine.program_length];omega) (by omega:6316≤B n) tableRun
 have joined:=placedHeader.trans placedTable
 let s:=setPC u 6316
 change BoundedRuns (UniformFinalOuterProgram.programFor fast) n x (B n) a (20+tt) s at joined
 have hf:=UniformPhysicalCRTTableHeaders.frame a0
 have finalFrame:Frame n a s:=by
  refine ⟨?_,uf.scalarHeap.trans hf.2.1,uf.scalarReg.trans hf.2.2.1,
   uf.outputs.trans hf.2.2.2.1,uf.roots.trans hf.2.2.2.2.1,?_⟩
  · intro q hq
    exact (UniformFinalPhysicalTableExecution.below hn uh q hq).trans (congrFun hf.1 q)
  · intro q hq hr
    exact (uf.natReg q hr).trans (hf.2.2.2.2.2 q hq)
 have coreU:=UniformFinalPhysicalTableExecution.retained_core c hn x h0 u hcore.withPC uf uh
 have dataU:=UniformFinalPhysicalTableExecution.retained_data c hn hdata.withPC uf uh
 have headerArgs:=UniformPhysicalCRTTableHeaders.values c n a0 out.core.withPC.metadata hsource
 have headerArgs0:UniformPhysicalCRTTableHeaders.Args c n h0:=header_args_pc headerArgs 0
 have finalArgs:=table_args_frame headerArgs0 uf
 refine ⟨s,ti,tc,tt,cacheEntry,a,?_,icost,ccost,tcost,rfl,?_,out,finalFrame⟩
 · simpa only[Nat.add_assoc] using run.trans joined
 · refine ⟨coreU.withPC,dataU.withPC,?_,?_,?_,alpha,inverse⟩
   · intro i hi
     exact (finalFrame.natReg _ (by unfold UniformPhysicalCRTTableHeaders.Changed;omega) (Or.inl (by omega))).trans (out.headers i hi)
   · exact (finalFrame.natReg 6904 (by unfold UniformPhysicalCRTTableHeaders.Changed;omega) (by omega)).trans source
   · exact header_args_pc finalArgs 6316
end
end ExactFourierCircuits.UniformFinalPhysicalTablePrefix
