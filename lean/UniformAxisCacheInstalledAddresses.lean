import UniformAxisCachePoolInstaller
import UniformAxisCacheAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheInstalledAddresses
open UniformMachine UniformTensorMonomialMachine UniformAxisCacheAllocationMachine
namespace I
export UniformAxisCachePoolInstaller (ops)
end I
noncomputable section
/-- The real allocator Result gives the exact ordinary headers consumed by301.
Neither destination6175..77 nor a frontier update is assumed. -/
theorem from_result(r N S:ℕ)(s:State)(result:Result r N S s)(radix:s.natReg 6800=r):
 UniformLocalCacheTreeIteration.Header r 0 (C.axisBank r N S).tasks (C.axisBank r N S).nodes
  (C.axisBank r N S).requests (applyBlock I.ops s)∧
 UniformLocalCacheTimingConductor.Allocation (C.axisBank r N S).durations
  (C.axisBank r N S).nodeStarts (C.axisBank r N S).requestStarts (applyBlock I.ops s)∧
 (applyBlock I.ops s).natReg 6160=(C.axisBank r N S).pool∧
 Result r N S (applyBlock I.ops s)∧
 (applyBlock I.ops s).natReg 6801=s.natReg 6801∧
 (applyBlock I.ops s).natReg 6802=s.natReg 6802:=by
 have installed:=UniformAxisCachePoolInstaller.installed s
 refine ⟨?_,?_,installed.pool.trans result.pool,?_,rfl,rfl⟩
 · exact ⟨installed.caller.forest.width.trans radix,installed.caller.forest.offset,
    installed.caller.forest.stack.trans result.tasks,installed.caller.forest.directory.trans result.nodes,
    installed.caller.forest.requests.trans result.requests⟩
 · exact ⟨installed.caller.allocation.durations.trans result.durations,
    installed.caller.allocation.starts.trans result.nodeStarts,
    installed.caller.allocation.requests.trans result.requestStarts⟩
 · exact ⟨result.tasks,result.nodes,result.requests,result.control,result.leafForward,result.leafTranspose,
    result.durations,result.nodeStarts,result.requestStarts,result.endNat,result.pool,result.endScalar⟩
end
end ExactFourierCircuits.UniformAxisCacheInstalledAddresses
