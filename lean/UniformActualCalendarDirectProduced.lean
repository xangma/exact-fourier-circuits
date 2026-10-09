import UniformActualCalendarRegistryFamily
import UniformActualCalendarDirectPolicy

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectProduced
open UniformMachine UniformActualCalendarRegistry UniformDirectLeafCacheSemanticExecution
open UniformDirectLeafCacheReader UniformGlobalCalendarDispatch
noncomputable section

lemma duration (q : UniformTransposeDescriptorMachine.Record) :
 UniformGlobalCalendarSelector.duration (UniformDirectLeafCacheChronology.cacheKind q)=
 UniformDirectLeafCacheChronology.duration q:=by
 by_cases scale:q.kind=0
 · simp only[UniformDirectLeafCacheChronology.cacheKind,UniformDirectLeafCacheChronology.duration,
    UniformGlobalCalendarSelector.duration,scale,ite_true]
   decide
 · simp only[UniformDirectLeafCacheChronology.cacheKind,UniformDirectLeafCacheChronology.duration,
    UniformGlobalCalendarSelector.duration,scale,ite_false]
   decide

def event {c : Config} {r : ℕ} {q : UniformTransposeDescriptorMachine.Record} {mu : ℂ}
 {positive : 2≤r} {s : State} (res : SemanticResult c r q mu positive s) (elapsed : ℕ) : Event:=
 UniformActualCalendarDirectEvent.actualEvent res elapsed (UniformActualCalendarDirectEvent.phase q elapsed)

/-- The actual descriptor cache determines all event values and endpoints. -/
def produced {c : Config} {r : ℕ} {q : UniformTransposeDescriptorMachine.Record} {mu : ℂ}
 {positive : 2≤r} {s : State} {O T B : ℕ} (res : SemanticResult c r q mu positive s)
 (legal : UniformDirectLeafCacheSource.Legal q) (entryFit:c.entry+7≤T)
 (poolFit:c.pool+9*r≤O) (permutationFit:c.permutation+r≤T) (radixBound:r≤B):
 Produced r O T B c.entry c.time (UniformDirectLeafCacheChronology.cacheKind q) s where
 event:=event res
 address_eq:=fun _=>rfl
 elapsed_eq:=fun _=>rfl
 cached:=fun elapsed bound=>UniformActualCalendarDirectEvent.cached_policy res legal elapsed
  (by simpa only[duration] using bound) entryFit poolFit permutationFit radixBound

end
end ExactFourierCircuits.UniformActualCalendarDirectProduced
