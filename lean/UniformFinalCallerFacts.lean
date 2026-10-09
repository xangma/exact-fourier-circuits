import UniformFinalRoleTableEntries
import UniformFinalClockOuterRuntime
import UniformActualCompleteClockResult
import UniformConcreteFinalOutputTail
import UniformFinalOuterEnvelope

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 three-transform construction and §5.4 Theorem 1.1 proof,
PDF pp.22-24 (`eq:chirp`, `thm:main`), with the model in §1.1, PDF p.2 (`sec:model`).

Startup, header, continuation and output bookkeeping refines the fixed
deterministic program. There is no separate paper counterpart for these state
layouts; the surrounding paper argument requires their preparation/index cost.
-/
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
