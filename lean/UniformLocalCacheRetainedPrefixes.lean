import UniformLocalCacheHighRegisters
import UniformLocalRectangleCoefficientMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextConductor
open UniformMachine UniformAllAxisSeedPreparation

/-- Ordinary placement of the retained global banks before the reusable
mapping workspace and fresh factor pools. -/
structure Prefixes (n:ℕ) (c:UniformLocalCacheSlotHeaderMachine.Parameters) : Prop where
 nat : UniformConjugateRankSpectrumPreparation.dirEnd n  ≤  c.borrowed
 scalar : UniformConjugateRankSpectrumPreparation.seedEnd n  ≤  c.pool
 mu : UniformConjugateRankSpectrumPreparation.seedEnd n  ≤  c.mu
 bar : UniformConjugateRankSpectrumPreparation.seedEnd n  ≤  c.conjugateMu

theorem prefix_frame {n B ticks:ℕ}{x:Fin n → ℂ}{s u:State}
 (c:UniformLocalCacheSlotHeaderMachine.Parameters)(fresh:Prefixes n c)
 (run:BoundedExecution program n x B s ticks u)
 (nat:∀ i,i<c.borrowed → u.natHeap i=s.natHeap i)
 (scalar:∀ i,(i<c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) → 
  i ≠ c.mu → i ≠ c.conjugateMu → u.scalarHeap i=s.scalarHeap i)
 (out:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 (∀ i,i<UniformConjugateRankSpectrumPreparation.seedEnd n → u.scalarHeap i=s.scalarHeap i) ∧
 (∀ i,i<UniformConjugateRankSpectrumPreparation.dirEnd n → u.natHeap i=s.natHeap i) := by
 have ns:∀ i,i<UniformConjugateRankSpectrumPreparation.dirEnd n → u.natHeap i=s.natHeap i:=
  fun i hi=>nat i (lt_of_lt_of_le hi fresh.nat)
 have ss:∀ i,i<UniformConjugateRankSpectrumPreparation.seedEnd n → u.scalarHeap i=s.scalarHeap i:=by
  intro i hi
  exact scalar i (Or.inl (lt_of_lt_of_le hi fresh.scalar)) (by have:=fresh.mu;omega)
   (by have:=fresh.bar;omega)
 refine ⟨⟨?_,?_,?_,?_,?_⟩,ss,ns⟩
 · intro i hi
   apply ns
   unfold UniformConjugateRankSpectrumPreparation.dirEnd UniformAllAxisConjugatePreparation.directoryBase
   change i<directoryBase n+2*axisCount n+2*axisCount n
   omega
 · intro i hi
   exact ss i (lt_of_lt_of_le hi (UniformConjugateRankSpectrumPreparation.originalEnd_le_seedEnd n))
 · intro q lo hi
   exact execution_nat run q (Or.inl ⟨lo,hi⟩)
 · exact out
 · exact roots

end ExactFourierCircuits.UniformLocalCacheContextConductor
