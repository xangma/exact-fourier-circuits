import UniformFinalClockRuntime

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockCache
open UniformMachine UniformTensorMonomialMachine
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- Actual table preparation changes fresh AP/BI/work cells. Every produced
cache axis lies strictly below AP, so its durable contents are retained. -/
lemma prefix_heaps {n:ℕ} (hn:0<n) {s u:State}
 (frame:UniformFinalPhysicalTablePrefix.Frame n s u)
 (j:Fin (UniformJointCacheAllocation.ell n)):UniformAxisCachePhysical.Heaps c n j s u:=by
 have before:=UniformFinalPhysicalTableGeometry.cache_before c hn j
 exact ⟨fun a _ hi=>frame.natHeap a (hi.trans_le before),fun a _ _=>congrFun frame.scalarHeap a⟩
lemma prefix_all {n upto:ℕ} (hn:0<n) {s u:State}
 (frame:UniformFinalPhysicalTablePrefix.Frame n s u)
 (old:UniformAxisCacheLoopState.All c n hn upto s):UniformAxisCacheLoopState.All c n hn upto u:=
 fun j hj=>UniformAxisCacheContents.transport (old j hj) (prefix_heaps hn frame j)

lemma role_inputs {n:ℕ} (hn:0<n) {x:Fin n→ℂ} {s u:State}
 (frame:UniformFinalRoleExecution.Frame n s u) (old:UniformAxisCacheInputs.Inputs n x s):
 UniformAxisCacheInputs.Inputs n x u:=by
 apply UniformClockCacheInputsRetention.inputs c hn x s u old
 · intro a _
   exact congrFun frame.natHeap a
 · intro a ha
   exact frame.scalar a (Or.inl (by omega))
 · exact frame.saved
 · exact frame.outputs
 · exact frame.roots

lemma role_all_pc {n upto:ℕ} (hn:0<n) {s u:State}
 (frame:UniformFinalRoleExecution.Frame n s u)
 (old:UniformAxisCacheLoopState.All c n hn upto s):
 UniformAxisCacheLoopState.All c n hn upto (setPC u 0):=
 (frame.cache_all hn old).transport rfl rfl
lemma role_inputs_pc {n:ℕ} (hn:0<n) {x:Fin n→ℂ} {s u:State}
 (frame:UniformFinalRoleExecution.Frame n s u) (old:UniformAxisCacheInputs.Inputs n x s):
 UniformAxisCacheInputs.Inputs n x (setPC u 0):=(role_inputs hn frame old).withPC

/-- The input and cache obligations used by the first clock follow from the
actual startup result and its actual table-prefix frame. -/
lemma from_prefix {n:ℕ} (hn:0<n) {x:Fin n→ℂ} {cacheEntry start s:State}
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:UniformFinalPhysicalTablePrefix.Result n x s)
 (frame:UniformFinalPhysicalTablePrefix.Frame n start s):
 UniformAxisCacheInputs.Inputs n x s∧
 UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s:=
 ⟨UniformAxisCacheInputs.of_core entry.core,prefix_all hn frame old.cache.all⟩
end
end ExactFourierCircuits.UniformFinalClockCache
