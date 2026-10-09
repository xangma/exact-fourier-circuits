import UniformAxisCachePrepareProgram
import UniformAxisCacheAllocationExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePrepareExecution
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (applyBlock setPC)
open UniformAxisCachePrepareProgram
namespace A
export UniformAxisCacheAllocationMachine (Arguments Result wordBudget)
export UniformJointCacheAllocation (axisBank)
end A
namespace I
export UniformAxisCachePoolInstaller (ops)
end I

noncomputable section
structure Ready(r N S:ℕ)(s:State):Prop where
 forest:UniformLocalCacheTreeIteration.Header r 0 (A.axisBank r N S).tasks (A.axisBank r N S).nodes (A.axisBank r N S).requests s
 timing:UniformLocalCacheTimingConductor.Allocation (A.axisBank r N S).durations
  (A.axisBank r N S).nodeStarts (A.axisBank r N S).requestStarts s
 pool:s.natReg 6160=(A.axisBank r N S).pool
 result:A.Result r N S s
 natFrontier:s.natReg 6801=N
 scalarFrontier:s.natReg 6802=S

/-- Actual58 arithmetic followed continuously by ten charged caller copies.
There is no supplied617x/header Result, no free frontier movement, and no PC
reset between allocation and installation. The diagnostic halt is charged. -/
theorem execution(r N S B n:ℕ)(x:Fin n→ℂ)(s:State)
 (args:A.Arguments r N S s)(pc:s.pc=0)(wb:WordBound B s)(budget:A.wordBudget r N S≤B):∃u,
 BoundedExecution program n x B s (4*Nat.clog 2 (4*r)+66) u∧u.pc=68∧Ready r N S u∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧u.natHeap=s.natHeap∧
 (∀q,¬destination q→u.natReg q=s.natReg q):=by
 have code:69≤B:=by unfold A.wordBudget at budget;omega
 obtain ⟨a,allocator,ap,result,frame⟩:=UniformAxisCacheAllocationMachine.execution r N S B n x s args pc wb budget
 have placedAllocator:BoundedRuns program n x B s (4*Nat.clog 2 (4*r)+55) (setPC a 58):=by
  simpa only [placed,Nat.zero_add,setPC] using
   UniformAssembly.BoundedExecution.placed allocator_code (by omega) (by omega) allocator
 have install:=UniformAxisCachePoolInstaller.ten program 58 n B x (setPC a 58) installer_code rfl
  placedAllocator.final_bound (by omega)
 let u:=applyBlock I.ops (setPC a 58)
 have up:u.pc=68:=by simpa only using install.2.1
 have halt:BoundedExecution program n x B u 1 u:=
  .halt install.1.final_bound (by simp [UniformMachine.step,up,halt_at])
 have whole:=placedAllocator.executes (install.1.executes halt)
 have typedResult:A.Result r N S (setPC a 58):=
  ⟨result.tasks,result.nodes,result.requests,result.control,result.leafForward,result.leafTranspose,
   result.durations,result.nodeStarts,result.requestStarts,result.endNat,result.pool,result.endScalar⟩
 have radix:(setPC a 58).natReg 6800=r:=
  (frame.natReg 6800 (by omega) (by omega)).trans args.radix
 have headers:=UniformAxisCacheInstalledAddresses.from_result r N S (setPC a 58) typedResult radix
 refine ⟨u,?_,up,?_,UniformLocalRectangleDescriptors.natOnly_execution program_natOnly whole.executes,?_,?_⟩
 · convert whole using 1
 · exact ⟨headers.1,headers.2.1,headers.2.2.1,headers.2.2.2.1,
    headers.2.2.2.2.1.trans ((frame.natReg 6801 (by omega) (by omega)).trans args.natFrontier),
    headers.2.2.2.2.2.trans ((frame.natReg 6802 (by omega) (by omega)).trans args.scalarFrontier)⟩
 · exact frame.natHeap
 · intro q hq
   exact UniformNewtonTableMachine.Executes.keeps_nat whole.executes (program_keeps q hq)
end
end ExactFourierCircuits.UniformAxisCachePrepareExecution
