import UniformFinalClockOuterFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOuterRetention
open UniformMachine UniformAxisCachePreparationRetention
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants

lemma Frame.original {n:ℕ}{s u:State}(hn:0<n)(h:Frame n s u)
 (old:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s):
 UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u:=by
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2
 refine ⟨?_,?_,?_⟩
 · intro j hj q l
   exact (h.low.scalar _ ((UniformAllAxisSeedPreparation.compact_address_before j hj q l).trans_le word.1)).trans (old.coefficients j hj q l)
 · intro j hj
   apply Eq.trans _ (old.address j hj)
   apply h.low.nat
   change _<(n+2)^19
   have:=j.isLt
   have bound:=word.2
   omega
 · intro j hj
   apply Eq.trans _ (old.width j hj)
   apply h.low.nat
   change _<(n+2)^19
   have:=j.isLt
   have bound:=word.2
   omega

lemma Frame.conjugate {n:ℕ}{s u:State}(hn:0<n)(h:Frame n s u)
 (old:UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s):
 UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u:=by
 have word:=(UniformAllAxisConjugatePreparation.word_setup hn).2
 apply UniformLocalRectangleCoefficientMachine.conjugate_retained old
 · intro a ha
   exact h.low.scalar a (ha.trans_le word.1)
 · intro a ha
   exact h.low.nat a (ha.trans_le word.2)

lemma Frame.core {n:ℕ}{s u:State}{x:Fin n→ℂ}(hn:0<n)(h:Frame n s u)
 (old:Core n x s):Core n x u:=by
 have protectedFrame:=(h.low.preserved hn h.saved h.outputs h.roots).protected
 refine ⟨?_,protectedFrame.metadata old.metadata,protectedFrame.operands old.operands,
  h.original hn old.seed,h.conjugate hn old.conjugate⟩
 constructor
 all_goals first
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.index
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.offset
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.count
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.one
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.directory
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.header.zero

lemma Frame.data {n:ℕ}{s u:State}{x:Fin n→ℂ}(hn:0<n)(h:Frame n s u)
 (old:UniformFinalStartupData.Data n x s):UniformFinalStartupData.Data n x u:=
 ⟨fun j=>(h.low.alpha_copied hn j).trans (old.gathered j),
 h.low.beta_inverse hn old.inverse,h.roots.trans old.roots,h.outputs.trans old.outputs⟩

lemma Frame.inputs {n:ℕ}{s u:State}{x:Fin n→ℂ}(hn:0<n)(h:Frame n s u)
 (old:UniformAxisCacheInputs.Inputs n x s):UniformAxisCacheInputs.Inputs n x u:=by
 have protectedFrame:=(h.low.preserved hn h.saved h.outputs h.roots).protected
 exact ⟨protectedFrame.metadata old.metadata,protectedFrame.operands old.operands,
  h.original hn old.original,h.conjugate hn old.conjugate⟩

lemma Frame.cache_all {n upto:ℕ}{s u:State}(hn:0<n)(h:Frame n s u)
 (old:UniformAxisCacheLoopState.All c n hn upto s):
 UniformAxisCacheLoopState.All c n hn upto u:=
 fun j hj=>UniformAxisCacheContents.transport (old j hj) (h.cache j)

end
end ExactFourierCircuits.UniformFinalClockOuterRetention
