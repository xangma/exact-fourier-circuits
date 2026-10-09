import UniformLocalStoredRequestEndpoints
import UniformAxisCacheCanonicalRequests
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestGeometry UniformAxisCacheCanonicalRequests
noncomputable section

lemma canonical_header (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(s:State)
 (ready:UniformAxisCacheTimingExecution.Ready (radix n j)
  (UniformAxisCacheSelectedPreparation.natAt constants n j.val)
  (UniformAxisCacheSelectedPreparation.scalarAt constants n j.val) s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s):
 UniformLocalRequestCursorMachine.Header (radix n j)
  (UniformJointCacheAllocation.axis constants n j).requests (canonical constants n j).length
  (UniformJointCacheAllocation.axis constants n j).requestStarts
  (UniformJointCacheAllocation.axis constants n j).control
  (UniformJointCacheAllocation.axis constants n j).pool (UniformJointCacheWorkspace.stride n) s:=by
 refine ⟨ready.radix,ready.requestBase,?_,ready.timing.requests,ready.result.control,
  ready.result.pool,?_,?_,?_,?_⟩
 · rw[canonical_length];exact ready.requestEnd
 · simpa only[Nat.add_zero,Nat.zero_add,Nat.one_mul] using bank ⟨0,by decide⟩
 · exact bank ⟨16,by decide⟩
 · exact bank ⟨31,by decide⟩
 · exact bank ⟨21,by decide⟩

/-- The current state is the real forest/timing producer output. Every source
row, time, count, layout and initial cursor is derived here; only retained
startup inputs and ordinary program/word bounds remain. -/
theorem canonical_execution (constants:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n))
 (x:Fin n → ℂ)(s:State)
 (ready:UniformAxisCacheTimingExecution.Ready (radix n j)
  (UniformAxisCacheSelectedPreparation.natAt constants n j.val)
  (UniformAxisCacheSelectedPreparation.scalarAt constants n j.val) s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (selected:s.natReg 6167=directoryBase n+2*j.val)(axis:s.natReg 6906=j.val)
 (original:Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (operands:UniformInitialPreparation.Operands n x s)
 (code:3776 ≤ envelope constants n)(pc:s.pc=0)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedExecution program n x (envelope constants n) s ticks u ∧
 ticks ≤ costPrefix n j (canonical constants n j) (canonical constants n j).length+23 ∧
 u.pc=3775 ∧
 Ready constants n j (canonical constants n j)
  (UniformJointCacheAllocation.axis constants n j).requests
  (UniformJointCacheAllocation.axis constants n j).requestStarts
  (geometry constants n hn j) x (canonical constants n j).length u ∧
 Endpoints constants n j (canonical constants n j)
  (UniformJointCacheAllocation.axis constants n j).requests
  (UniformJointCacheAllocation.axis constants n j).requestStarts u ∧
 LoopFrame constants n j s u ∧
 (∀q,5920 ≤ q → q ≤ 5925 → u.natReg q=s.natReg q):=by
 obtain ⟨u,t,run,cost,up,result,frame⟩:=execution hn (geometry constants n hn j) x s
  (canonical_header constants n j s ready bank) bank selected axis
  (UniformAxisCacheCanonicalRequests.source constants n j s ready) original conjugate metadata operands code pc wb
 exact ⟨u,t,run,cost,up,result,result.endpoints,frame,
  UniformLocalStoredRequestRegisterFrames.execution_clock run⟩

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
