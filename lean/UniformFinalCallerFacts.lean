import UniformFinalRoleTableEntries
import UniformFinalClockOuterRuntime
import UniformActualCompleteClockResult
import UniformConcreteFinalOutputTail
import UniformFinalOuterEnvelope

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCallerFacts
open UniformMachine UniformFinalClockRuntime UniformFinalClockCaller
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- Actual complete clocks restore the same five cache-producer fields needed
by the next literal loader, rather than assuming their syntactic preservation. -/
lemma saved_of_runtime {n:ℕ}{hn:0<n}{x:Fin n→ℂ}{cacheEntry start s:State}
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)(runtime:Runtime n s):
 ∀q,Saved q→s.natReg q=start.natReg q:=by
 intro q hq
 rcases hq with rfl|rfl|rfl|rfl|rfl
 · exact runtime.horizon.trans old.cache.clock.symm
 · exact runtime.natEnd.trans old.cache.natEnd.symm
 · exact runtime.scalarEnd.trans old.cache.scalarEnd.symm
 · have h:start.natReg 6909=UniformJointCacheAllocation.natStart c n:=by
    simpa only[UniformAxisCacheSelectedPreparation.natAt,UniformJointCacheAllocation.offsetSum,
     Finset.range_zero,Finset.sum_empty,Nat.add_zero] using old.cache.savedNat
   exact runtime.initialNat.trans h.symm
 · have h:start.natReg 6910=UniformJointCacheAllocation.scalarStart c n:=by
    simpa only[UniformAxisCacheSelectedPreparation.scalarAt,UniformJointCacheAllocation.offsetSum,
     Finset.range_zero,Finset.sum_empty,Nat.add_zero] using old.cache.savedScalar
   exact runtime.initialScalar.trans h.symm

end
end ExactFourierCircuits.UniformFinalCallerFacts
