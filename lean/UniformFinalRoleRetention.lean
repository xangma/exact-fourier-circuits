import UniformFinalRoleExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleExecution
open UniformMachine UniformFinalRoleModel UniformAxisCachePreparationRetention UniformFinalStartupData
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
lemma Frame.low {n:ℕ} {s u:State} (hn:0<n) (h:Frame n s u):UniformCacheLowRetention.Frame n s u:=by
 have low:=(UniformFinalRoleGeometry.geometry hn).2.2.2.2.2.2
 exact ⟨fun a _=>congrFun h.natHeap a,fun a ha=>h.scalar a (Or.inl (ha.trans_le low))⟩
lemma Frame.saved {n:ℕ} {s u:State} (h:Frame n s u):
 ∀q,100≤q→q≤106→u.natReg q=s.natReg q:=by
 intro q lo hi
 exact h.natReg q (by unfold R.Protected;omega) (by unfold H.Changed;omega)
lemma Frame.core {n:ℕ} {s u:State} {x:Fin n→ℂ} (hn:0<n) (h:Frame n s u)
 (old:Core n x s):Core n x u:=by
 have low:=h.low hn
 have protectedFrame:=(low.preserved hn h.saved h.outputs h.roots).protected
 have original:=(UniformAllAxisSeedPreparation.word_setup hn).2.1
 have conjugate:=(UniformAllAxisConjugatePreparation.word_setup hn).2.1
 refine ⟨?_,protectedFrame.metadata old.metadata,protectedFrame.operands old.operands,?_,?_⟩
 · constructor
   all_goals first
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.index
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.offset
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.count
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.one
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.directory
   | exact (h.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans old.header.zero
 · exact old.seed.transport_before (fun a ha=>low.scalar a (ha.trans_le original)) h.natHeap
 · apply UniformLocalRectangleCoefficientMachine.conjugate_retained old.conjugate
   · intro a ha
     apply low.scalar
     exact ha.trans_le conjugate
   · intro a _
     exact congrFun h.natHeap a
lemma Frame.data {n:ℕ} {s u:State} {x:Fin n→ℂ} (hn:0<n) (h:Frame n s u)
 (old:Data n x s):Data n x u:=by
 have low:=h.low hn
 exact ⟨fun j=>(low.alpha_copied hn j).trans (old.gathered j),
  low.beta_inverse hn old.inverse,h.roots.trans old.roots,h.outputs.trans old.outputs⟩
lemma Frame.cache_heaps {n:ℕ} {s u:State} (hn:0<n) (h:Frame n s u)
 (j:Fin (UniformJointCacheAllocation.ell n)):UniformAxisCachePhysical.Heaps c n j s u:=by
 have before:=UniformKernelSpectrumStorage.caches_before c hn j
 have end_eq:=UniformKernelSpectrumStorage.end_eq c hn
 refine ⟨fun a _ _=>congrFun h.natHeap a,?_⟩
 intro a _ ha
 exact h.scalar a (Or.inl (by omega))
lemma Frame.cache_all {n upto:ℕ} {s u:State} (hn:0<n) (h:Frame n s u)
 (old:UniformAxisCacheLoopState.All c n hn upto s):UniformAxisCacheLoopState.All c n hn upto u:=
 fun j hj=>UniformAxisCacheContents.transport (old j hj) (h.cache_heaps hn j)
lemma Frame.spectrum {n:ℕ} {s u:State} (hn:0<n) (h:Frame n s u) (j:Fin (V n)):
 u.scalarHeap (UniformKernelSpectrumStorage.base c n+j.val)=
 s.scalarHeap (UniformKernelSpectrumStorage.base c n+j.val):=
 h.scalar _ (Or.inl (UniformKernelSpectrumStorage.cell_below_source c hn j))
end
end ExactFourierCircuits.UniformFinalRoleExecution
