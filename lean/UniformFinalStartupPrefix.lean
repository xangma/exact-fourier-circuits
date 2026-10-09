import UniformFinalStartupData
import UniformFinalStartupCode
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStartupPrefix
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformAxisCachePreparationRetention UniformFinalStartupData UniformFinalStartupFrames
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- The real empty-state startup and both charged allocators run in the final
program. Its later table producer affects only the ordinary code-size bound. -/
theorem execution (table:Program){n:ℕ}(hn:0<n) (x:Fin n→ℂ)
 (tableFit:table.length≤UniformJointAllocation.fixed c):∃s ti,
 BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) initial (ti+62+67) s∧
 ti≤UniformAllAxisConjugatePreparation.fullBudget n∧s.pc=1589∧Core n x s∧
 UniformLocalRectangleWorkspaceHeaders.Bank n s∧Data n x s∧
 (∀i,(hi:i<18)→s.natReg (6020+i)=UniformJointAllocationMachine.factors[i]*UniformJointAllocation.slab c n):=by
 have arithmetic:=UniformJointAllocationMachine.arithmetic c n
 have fit:=UniformFinalOuterProgram.code_envelope table n tableFit
 have length:=UniformFinalOuterProgram.programFor_length table
 have room:6243≤UniformJointAllocation.envelope c n:=by omega
 obtain ⟨t,u,run,cost,conj,seed,metadata,operands,roots,outputs,_,budget,header,gathered,inverse⟩:=
  UniformInitialCoreRetention.initial_execution_with_header hn x
 let ti:=t+UniformAllAxisSeedPreparation.preparationRuntime n+1+
  UniformAllAxisConjugatePreparation.preparationRuntime n+1
 have run0:=UniformJointAllocationMachine.execution_bound_mono run arithmetic.2.2.2.1
 have p0:=UniformBoundedAssembly.boundedExecution_placed (UniformFinalStartupCode.initial_code table)
  (by rw[UniformAllAxisConjugatePreparation.fullProgram_length];omega)
  (by omega:1460≤UniformJointAllocation.envelope c n) run0
 let a:=setPC u 1460
 change BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) initial ti a at p0
 have ca:Core n x a:=⟨header.withPC,metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),
  operands.transport rfl,seed.withPC,conj.withPC⟩
 have da:Data n x a:=⟨gathered,inverse,roots,outputs⟩
 let a0:=setPC a 0
 have ra:=UniformJointAllocationMachine.execution c n x a0 rfl (changePC_bound _ a 0 p0.final_bound (by omega))
 have pa:=UniformBoundedAssembly.boundedExecution_placed (UniformFinalStartupCode.allocation_code table)
  (by rw[UniformJointAllocationMachine.program_length];omega) (by omega:1522≤UniformJointAllocation.envelope c n) ra
 have samea:placed 1460 a0=a:=by rfl
 rw[samea] at pa
 let b:=setPC (UniformJointAllocationMachine.result c n a0) 1522
 change BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) a 62 b at pa
 have fa:=UniformJointAllocationMachine.result_frame c n a0
 have cb:Core n x b:=core_transport ca.withPC fa.natHeap fa.scalarHeap
  (fun q lo hi=>fa.natReg q (by unfold UniformJointAllocationMachine.Changed;omega))
  (fun q lo hi=>fa.natReg q (by unfold UniformJointAllocationMachine.Changed;omega)) fa.outputs fa.roots
 have db:Data n x b:=da.withPC.transport fa.natHeap fa.scalarHeap fa.roots fa.outputs
 let b0:=setPC b 0
 have stride:b0.natReg 6002=UniformJointCacheWorkspace.stride n:=allocation_stride c n a0
 have banks:32*UniformJointCacheWorkspace.stride n≤UniformJointAllocation.envelope c n:=
  by
  have h:=UniformJointCacheWorkspace.ambient_budget c n
  change 2000*UniformJointCacheWorkspace.stride n≤UniformJointAllocation.envelope c n at h
  omega
 obtain ⟨rwk,_,values⟩:=UniformJointCacheWorkspaceMachine.execution n (UniformJointAllocation.envelope c n) x b0 stride (by omega) banks rfl
  (changePC_bound _ b 0 pa.final_bound (by omega))
 have pw:=UniformBoundedAssembly.boundedExecution_placed (UniformFinalStartupCode.workspace_code table)
  (by rw[UniformJointCacheWorkspaceMachine.program_length];omega) (by omega:1589≤UniformJointAllocation.envelope c n) rwk
 have sameb:placed 1522 b0=b:=by rfl
 rw[sameb] at pw
 let d:=setPC (UniformJointCacheWorkspaceMachine.result b0) 1589
 change BoundedRuns (UniformFinalOuterProgram.programFor table) n x (UniformJointAllocation.envelope c n) b 67 d at pw
 obtain ⟨nh,sh,_,outs,rts,regs⟩:=UniformJointCacheWorkspaceMachine.result_frame b0
 have cd:Core n x d:=core_transport cb.withPC nh sh
  (fun q lo hi=>regs q (by omega) (by omega) (Or.inl (by omega)))
  (fun q lo hi=>regs q (by omega) (by omega) (Or.inl (by omega))) outs rts
 have dd:Data n x d:=db.withPC.transport nh sh rts outs
 have bank:UniformLocalRectangleWorkspaceHeaders.Bank n d:=values
 refine ⟨d,ti,(p0.trans pa).trans pw,budget,rfl,cd,bank,dd,?_⟩
 intro i hi
 exact (regs (6020+i) (by omega) (by omega) (Or.inl (by omega))).trans (UniformJointAllocationMachine.result_headers c n a0 i hi)
end
end ExactFourierCircuits.UniformFinalStartupPrefix
