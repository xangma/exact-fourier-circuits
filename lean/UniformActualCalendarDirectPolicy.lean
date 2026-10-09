import UniformActualCalendarDirectEvent

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectEvent
open UniformMachine UniformGlobalCalendarDispatch UniformGlobalMatchingScaleMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheSemanticExecution
noncomputable section
variable {c : Config} {r : ℕ} {q : UniformTransposeDescriptorMachine.Record}
 {mu : ℂ} {positive : 2≤r} {s : State}

def phase (q : UniformTransposeDescriptorMachine.Record) (elapsed : ℕ) : Phase:=
 if q.kind=0 then .diagonal 0 else
 phases.get ⟨elapsed%28,by rw[phases_length];exact Nat.mod_lt _ (by decide)⟩

/-- Actual mixed-duration direct events obey the literal281 decoder policy:
a scale is one diagonal tick; a shear uses its actual ordinary28 phases. -/
lemma decoded (res : SemanticResult c r q mu positive s)
 (elapsed : ℕ) (bound : elapsed<UniformDirectLeafCacheChronology.duration q) :
 Decoded (actualEvent res elapsed (phase q elapsed)).descriptor (phase q elapsed):=by
 by_cases scale:q.kind=0
 · right;left
   refine ⟨?_,?_⟩
   · change res.kind=1
     simpa only[UniformDirectLeafCacheChronology.cacheKind,scale,ite_true] using res.kind_eq
   · simp only[phase,scale,ite_true]
     rfl
 · have ordinary:res.kind=0:=by
    simpa only[UniformDirectLeafCacheChronology.cacheKind,scale,ite_false] using res.kind_eq
   have elapsedBound:elapsed<28:=by
    simpa only[UniformDirectLeafCacheChronology.duration,scale,ite_false] using bound
   left
   refine ⟨elapsedBound,ordinary,?_⟩
   simp only[phase,scale,ite_false,Nat.mod_eq_of_lt elapsedBound]
   rfl

theorem cached_policy {O T B : ℕ} (res : SemanticResult c r q mu positive s)
 (legal : UniformDirectLeafCacheSource.Legal q) (elapsed : ℕ)
 (bound : elapsed<UniformDirectLeafCacheChronology.duration q)
 (entryFit : c.entry+7≤T) (poolFit : c.pool+9*r≤O)
 (permutationFit : c.permutation+r≤T) (radixBound : r≤B) :
 CachedEvent r O T B (actualEvent res elapsed (phase q elapsed)) s:=
 cached res legal elapsed (phase q elapsed) (decoded res elapsed bound)
  entryFit poolFit permutationFit radixBound

end
end ExactFourierCircuits.UniformActualCalendarDirectEvent
