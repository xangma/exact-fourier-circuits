import UniformAxisCacheRequestBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheCanonicalRequests
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformJointCacheAllocation UniformAxisCacheSelectedPreparation
open UniformAxisCacheRequestSource UniformLocalRequestPlan
open UniformLocalRequestGeometry UniformCanonicalCacheSlotGeometry

def canonical (c:Constants)(n:ℕ)(j:Fin (axisCount n)):List Request:=
 requests (UniformLocalCacheTimingMetadata.rootVisits (radix n j) 0 (axis c n j).requests)

lemma canonical_length (c:Constants)(n:ℕ)(j:Fin (axisCount n)):
 (canonical c n j).length=UniformLocalCacheTimingMetadata.requestCount (radix n j) 0 (axis c n j).requests:=
 requests_length _
lemma length_bound (c:Constants)(n:ℕ)(j:Fin (axisCount n)):(canonical c n j).length≤(radix n j)^2:=by
 rw [canonical_length]
 exact UniformAxisCacheTimingGeometry.requests_bound _ _
lemma capacity (c:Constants)(n:ℕ)(j:Fin (axisCount n)):
 slotPrefix n (canonical c n j) (canonical c n j).length+2*(radix n j)^2≤
 UniformJointCacheExtent.capacity (radix n j):=
 UniformAxisCacheRequestBounds.capacity _ _ _
lemma cache_room (c:Constants)(n:ℕ)(j:Fin (axisCount n))(i:ℕ)(hi:i<(canonical c n j).length):
 slotPrefix n (canonical c n j) i+UniformLocalRequestPlan.slotCount n ((canonical c n j)[i]'hi).row≤
 UniformJointCacheExtent.capacity (radix n j):=by
 rw [←prefix_step n (canonical c n j) i hi]
 exact (prefix_mono n (canonical c n j) (show i+1≤(canonical c n j).length by omega) (le_refl _)).trans
  (by have:=capacity c n j;omega)
lemma time_room (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n))(i:ℕ)(hi:i<(canonical c n j).length):
 ((canonical c n j)[i]'hi).time+28*UniformLocalRequestPlan.slotCount n ((canonical c n j)[i]'hi).row≤envelope c n:=by
 have time:=UniformAxisCacheRequestBounds.time_bound n (radix n j) (axis c n j).requests _ (List.getElem_mem hi)
 have duration:=UniformAxisCacheTimingGeometry.duration_fits (radix n j) (natAt c n j.val) (scalarAt c n j.val)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)
 exact time.trans (duration.trans (UniformAxisCacheAllocationMachine.selected_wordBudget c n hn j))

lemma ordinary_intervals (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n)):
 slab c n≤(axis c n j).requests∧slab c n≤(axis c n j).requestStarts∧
 (axis c n j).requests+7*(canonical c n j).length≤(axis c n j).control∧
 (axis c n j).leafForward≤(axis c n j).requestStarts∧
 (axis c n j).requests+7*(canonical c n j).length≤envelope c n∧
 (axis c n j).requestStarts+(canonical c n j).length≤envelope c n:=by
 have count:=length_bound c n j
 have fit:=(axis_fit c n j).1.trans ((ends_bound c n hn).1)
 have env:2*slab c n≤envelope c n:=by unfold envelope;omega
 have rfactor:1≤2*radix n j+2:=by omega
 have requestFit:7*(canonical c n j).length≤7*(2*radix n j+2)*(radix n j)^2:=by
  have upper:=(Nat.mul_le_mul_right ((radix n j)^2) rfactor)
  rw [Nat.one_mul] at upper
  have lifted:=Nat.mul_le_mul_left 7 (count.trans upper)
  simpa only [Nat.mul_assoc] using lifted
 dsimp only [axis,axisBank,natStart] at fit ⊢
 omega

/-- Every geometric/capacity/time field of the real finite request loop is
derived from the actual canonical forest, with timestamps after cache end. -/
theorem geometry (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n)):
 Geometry c n j (canonical c n j) (axis c n j).requests (axis c n j).requestStarts:=by
 obtain ⟨rowsHigh,timesHigh,rowsBefore,timesAfter,rowsBound,timesBound⟩:=ordinary_intervals c n hn j
 refine ⟨?_,?_,by have:=capacity c n j;omega,rowsHigh,timesHigh,rowsBefore,timesAfter,rowsBound,timesBound⟩
 · intro i hi
   obtain ⟨v,o,hv,hp,extent,member⟩:=UniformAxisCacheRequestBounds.origin (radix n j) (axis c n j).requests
    ((canonical c n j)[i]'hi) (List.getElem_mem hi)
   exact UniformJointCacheWorkspace.geometry_of_rows j _ hv hp (by omega) member
 · intro i hi
   obtain ⟨v,o,hv,hp,extent,member⟩:=UniformAxisCacheRequestBounds.origin (radix n j) (axis c n j).requests
    ((canonical c n j)[i]'hi) (List.getElem_mem hi)
   have cache:=cache_room c n j i hi
   have time:=time_room c n hn j i hi
   simp only [UniformLocalRequestPlan.controller,requestAt_eq (canonical c n j) i hi]
   exact UniformCanonicalCacheSlotComplete.geometry c hn j v o _ hv hp extent member _ _ cache time _ _

theorem source (c:Constants)(n:ℕ)(j:Fin (axisCount n))(s:State)
 (ready:UniformAxisCacheTimingExecution.Ready (radix n j) (natAt c n j.val) (scalarAt c n j.val) s):
 Source (axis c n j).requests (axis c n j).requestStarts (canonical c n j) s:=
 UniformAxisCacheRequestSource.source _ _ _ _ _ _ s ready.tables ready.printed

end ExactFourierCircuits.UniformAxisCacheCanonicalRequests
