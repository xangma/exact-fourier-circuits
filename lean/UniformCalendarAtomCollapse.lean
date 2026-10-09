import UniformCalendarIntervalPartition

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarAtomCollapse
noncomputable section
open UniformLocalCacheTiming UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarIntervalPartition

/-- The real sequential atoms of each macro event, with their prefix clocks. -/
def ActiveAtom (E : List TimedEvent) (ds : Fin E.length→List ℕ) (t : ℕ) :=
 {a : Σi : Fin E.length,Fin (ds i).length //
   (E.get a.1).start+prefixDuration (ds a.1) a.2.val≤t ∧
   t<(E.get a.1).start+prefixDuration (ds a.1) a.2.val+(ds a.1).get a.2}

variable (E : List TimedEvent) (ds : Fin E.length→List ℕ)
 (durations : ∀i,(ds i).sum=(E.get i).event.duration) (t : ℕ)

def project (a : ActiveAtom E ds t) : ActiveIndex E t:=
 ⟨a.val.1,by
  have stop:=before_sum (ds a.val.1) a.val.2
  rw[durations] at stop
  change (E.get a.val.1).start≤t ∧ t<(E.get a.val.1).start+(E.get a.val.1).event.duration
  exact ⟨by have:=a.property.1;omega,by have:=a.property.2;omega⟩⟩

lemma project_injective : Function.Injective (project E ds durations t):=by
 intro a b eq
 have same:a.val.1=b.val.1:=congrArg Subtype.val eq
 rcases a with ⟨⟨i,j⟩,ha⟩
 rcases b with ⟨⟨k,l⟩,hb⟩
 change i=k at same
 subst k
 change (E.get i).start+prefixDuration (ds i) j.val≤t ∧ t<(E.get i).start+prefixDuration (ds i) j.val+(ds i).get j at ha
 change (E.get i).start+prefixDuration (ds i) l.val≤t ∧ t<(E.get i).start+prefixDuration (ds i) l.val+(ds i).get l at hb
 have bound:t-(E.get i).start<(ds i).sum:=by
  have stop:=before_sum (ds i) j
  omega
 obtain ⟨part,_hp,unique⟩:=partition (ds i) (t-(E.get i).start) bound
 have hj:j=part:=unique j (by omega)
 have hl:l=part:=unique l (by omega)
 have jl:j=l:=hj.trans hl.symm
 apply Subtype.ext
 exact Sigma.ext rfl (heq_of_eq jl)

lemma project_surjective : Function.Surjective (project E ds durations t):=by
 intro i
 have bound:t-(E.get i.val).start<(ds i.val).sum:=by
  rw[durations]
  have :=i.property
  change (E.get i.val).start≤t ∧ t<(E.get i.val).start+(E.get i.val).event.duration at this
  omega
 obtain ⟨j,hj,_unique⟩:=partition (ds i.val) (t-(E.get i.val).start) bound
 refine ⟨⟨⟨i.val,j⟩,?_⟩,?_⟩
 · change (E.get i.val).start+prefixDuration (ds i.val) j.val≤t ∧ t<(E.get i.val).start+prefixDuration (ds i.val) j.val+(ds i.val).get j
   have lo:=i.property.1
   exact ⟨by omega,by omega⟩
 · rfl

/-- Fine cache intervals cover exactly one atom of every active macro event. -/
def collapse : ActiveAtom E ds t≃ActiveIndex E t:=
 Equiv.ofBijective (project E ds durations t) ⟨project_injective E ds durations t,project_surjective E ds durations t⟩
lemma collapse_macro (a : ActiveAtom E ds t) : (collapse E ds durations t a).val=a.val.1:=rfl

end
end ExactFourierCircuits.UniformCalendarAtomCollapse
