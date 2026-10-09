import UniformCalendarActualAtoms
import UniformCalendarFlattenIndices

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRefinementActive
noncomputable section
open UniformLocalCacheTiming UniformGlobalCalendarUnion UniformCalendarIntervalPartition
open UniformCalendarActualAtoms

abbrev pieces (n:ℕ)(E:List TimedEvent)(i:Fin E.length):List ℕ:=durations n (E.get i).event

def order (n:ℕ)(E:List TimedEvent):
 (Σi:Fin E.length,Fin (pieces n E i).length)≃Fin (E.flatMap (records n)).length:=
 (Equiv.sigmaCongrRight (fun i=>finCongr (records_length n (E.get i)).symm)).trans
  (UniformCalendarFlattenIndices.order E (records n))

lemma order_get (n:ℕ)(E:List TimedEvent)(i:Fin E.length)(j:Fin (pieces n E i).length):
 (E.flatMap (records n)).get (order n E ⟨i,j⟩)=
 ((E.get i).start+prefixDuration (pieces n E i) j.val,kind ((pieces n E i).get j)):=by
 rw[order,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
  UniformCalendarFlattenIndices.get_order,records_get]
 rfl

def FineIndex (n:ℕ)(E:List TimedEvent)(t:ℕ):=
 {i:Fin (E.flatMap (records n)).length //
 UniformGlobalCalendarSelector.active t ((E.flatMap (records n)).get i).1 ((E.flatMap (records n)).get i).2}

/-- Literal selector indices are exactly the genuine sequential atom intervals. -/
def fineEquiv (n:ℕ)(E:List TimedEvent)(t:ℕ):
 UniformCalendarAtomCollapse.ActiveAtom E (pieces n E) t≃FineIndex n E t:=
 Equiv.subtypeEquiv (order n E) (by
  intro a
  rw[order_get]
  unfold UniformGlobalCalendarSelector.active
  change _ ↔ (E.get a.1).start+prefixDuration (pieces n E a.1) a.2.val≤t ∧
   t<(E.get a.1).start+prefixDuration (pieces n E a.1) a.2.val+
    UniformGlobalCalendarSelector.duration (kind ((pieces n E a.1).get a.2))
  rw[kind_duration _ (durations_values n (E.get a.1).event a.2)])

/-- Derived from the actual1/28 cache records; no selected-event bijection
or calendar alignment is a premise. -/
def collapse (n:ℕ)(E:List TimedEvent)(t:ℕ):FineIndex n E t≃ActiveIndex E t:=
 (fineEquiv n E t).symm.trans
  (UniformCalendarAtomCollapse.collapse E (pieces n E) (fun i=>durations_sum n (E.get i).event) t)

lemma collapse_macro (n:ℕ)(E:List TimedEvent)(t:ℕ)(a:UniformCalendarAtomCollapse.ActiveAtom E (pieces n E) t):
 (collapse n E t (fineEquiv n E t a)).val=a.val.1:=by
 rw[collapse,Equiv.trans_apply,Equiv.symm_apply_apply]
 rfl

end
end ExactFourierCircuits.UniformCalendarRefinementActive
