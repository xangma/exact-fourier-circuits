import UniformActualCalendarRegistryBundle

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheTransfer
open UniformMachine UniformGlobalCalendarDispatch UniformActualCalendarRegistry
noncomputable section

lemma monotone {r O T B O' T':ℕ}{e:Event}{s:State}
 (h:CachedEvent r O T B e s)(scalar:O≤O')(nat:T≤T'):CachedEvent r O' T' B e s:=
 ⟨h.decoded,h.stored,h.source,h.entryFit.trans nat,h.sourcePool.trans scalar,
  h.sourceRows.trans nat,h.matching,h.values⟩

/-- Only the actual source scalar interval is retained. In particular, a
boundary update below that interval need not preserve a whole scalar prefix. -/
lemma interval {r O T B low:ℕ}{e:Event}{s u:State}
 (h:CachedEvent r O T B e s)(lower:low≤e.descriptor.pool)
 (natKeep:∀z,z<T→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,low≤z→z<O→u.scalarHeap z=s.scalarHeap z):CachedEvent r O T B e u:=by
 refine ⟨h.decoded,?_,?_,h.entryFit,h.sourcePool,h.sourceRows,h.matching,h.values⟩
 · rcases h.stored with ⟨pool,width,permutation,kind⟩
   exact ⟨(natKeep _ (by have:=h.entryFit;omega)).trans pool,
    (natKeep _ (by have:=h.entryFit;omega)).trans width,
    (natKeep _ (by have:=h.entryFit;omega)).trans permutation,
    (natKeep _ (by have:=h.entryFit;omega)).trans kind⟩
 · have source:=h.source
   cases phase:e.phase with
   | diagonal lane=>
     simp only[phase,Source] at source ⊢
     intro i hi
     have mul:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
     rw[scalarKeep _ (by omega) (by have:=h.sourcePool;omega)]
     exact source i hi
   | kernel=>
     simp only[phase,Source] at source ⊢
     intro i hi
     exact ⟨(natKeep _ (by have:=h.sourceRows;omega)).trans (source i hi).1,
      (natKeep _ (by have:=h.sourceRows;omega)).trans (source i hi).2⟩

/-- Rebinding preserves the actual event factory; only factual source proofs
and their ordinary read bounds change. -/
def produced {r O T B O' T' address time kind:ℕ}{s u:State}
 (p:Produced r O T B address time kind s)
 (f:∀elapsed,elapsed<S.duration kind→CachedEvent r O' T' B (p.event elapsed) u):
 Produced r O' T' B address time kind u:=⟨p.event,p.address_eq,p.elapsed_eq,f⟩

def family {r O T B O' T' D stride:ℕ}{L:List (ℕ×ℕ)}{s u:State}
 (f:Family r O T B D stride L s)
 (h:∀j:Fin L.length,∀elapsed,elapsed<S.duration (L.get j).2→
  CachedEvent r O' T' B ((f.entry j).event elapsed) u):Family r O' T' B D stride L u where
 entry:=fun j=>produced (f.entry j) (h j)

lemma family_make {r O T B O' T' D stride:ℕ}{L:List (ℕ×ℕ)}{s u:State}
 (f:Family r O T B D stride L s)
 (h:∀j:Fin L.length,∀elapsed,elapsed<S.duration (L.get j).2→
  CachedEvent r O' T' B ((f.entry j).event elapsed) u):
 (family f h).make=f.make:=rfl

lemma selected_eq {r O T B O' T' D stride:ℕ}{L:List (ℕ×ℕ)}{s u:State}
 (f:Family r O T B D stride L s)(g:Family r O' T' B D stride L u)
 (same:g.make=f.make)(tick:ℕ):g.selected tick=f.selected tick:=by
 unfold Family.selected
 rw[same]

lemma bundle_events_eq {r O T B O' T' D:ℕ}{L:List (ℕ×ℕ)}{nodes:List UniformCacheRangeSelector.Range}{s u:State}
 (f:Bundle r O T B D L nodes s)(g:Bundle r O' T' B D L nodes u)
 (rectangle:g.rectangle.make=f.rectangle.make)
 (node:∀i,(g.node i).make=(f.node i).make)(tick:ℕ):g.events tick=f.events tick:=by
 unfold Bundle.events
 rw[selected_eq f.rectangle g.rectangle rectangle tick]
 have point:∀i,(g.node i).selected tick=(f.node i).selected tick:=
  fun i=>selected_eq (f.node i) (g.node i) (node i) tick
 simp_rw[point]

def family_mono {r O T B O' T' D stride:ℕ}{L:List (ℕ×ℕ)}{s:State}
 (f:Family r O T B D stride L s)(scalar:O≤O')(nat:T≤T'):Family r O' T' B D stride L s:=
 family f (fun i elapsed bound=>monotone ((f.entry i).cached elapsed bound) scalar nat)

def bundle_mono {r O T B O' T' D:ℕ}{L:List (ℕ×ℕ)}{nodes:List UniformCacheRangeSelector.Range}{s:State}
 (f:Bundle r O T B D L nodes s)(scalar:O≤O')(nat:T≤T'):Bundle r O' T' B D L nodes s where
 rectangle:=family_mono f.rectangle scalar nat
 node:=fun i=>family_mono (f.node i) scalar nat

lemma bundle_mono_events {r O T B O' T' D:ℕ}{L:List (ℕ×ℕ)}{nodes:List UniformCacheRangeSelector.Range}{s:State}
 (f:Bundle r O T B D L nodes s)(scalar:O≤O')(nat:T≤T')(tick:ℕ):
 (bundle_mono f scalar nat).events tick=f.events tick:=
 bundle_events_eq _ _ rfl (fun _=>rfl) tick

end
end ExactFourierCircuits.UniformFinalAxisCacheTransfer
