import UniformActualCacheRangeBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCacheRangeValues
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestRangeSource
open UniformLocalCacheTreeMachine UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheChronology
noncomputable section

/-- Ordinary envelope room for the scanner's unconditional start+28 check,
 including direct scale records whose actual duration is only one tick. -/
lemma horizon_room (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n)):
 2*UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan (radix n j))+32 ≤ envelope c n:=by
 have positive:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 change 2 ≤ radix n j at positive
 have ending:=((axis_fit c n j).2).trans ((ends_bound c n hn).2)
 change (axis c n j).pool+9*radix n j*UniformJointCacheExtent.capacity (radix n j) ≤ 2*slab c n at ending
 have product:=Nat.mul_le_mul_right (UniformJointCacheExtent.capacity (radix n j))
  (show 18 ≤ 9*radix n j by omega)
 have duration:=UniformAxisCacheTimingGeometry.duration_cap (radix n j)
 have large:=fixed_large c
 unfold envelope
 omega

lemma node_values {p:Parameters}{visits:List Visit}{A B:ℕ}
 (facts:UniformDirectLeafForestState.Facts p visits)(room:2*p.rootDuration+32 ≤ B):
 ∀q∈nodeRanges p visits A,∀j,j < q.count → (q.records j).1+28 ≤ B ∧(q.records j).2 ≤ B:=by
 intro q member
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 intro j hj
 change j < operations visits[i.val] at hj
 have stop:leaf visits[i.val]:=by
  by_contra neg
  simp only[operations,ite_eq_right neg] at hj
  omega
 have jl:j < (UniformDirectLeafForestLeafEnd.qs p A visits[i.val]).length:=by
  simpa only[operations,ite_eq_left stop,UniformDirectLeafForestLeafEnd.count] using hj
 have duration:=facts.duration i.val i.isLt stop
 have elapsed:=elapsed_take_le (UniformDirectLeafForestLeafEnd.qs p A visits[i.val]) j
 rw[UniformDirectLeafForestLeafEnd.qs,UniformDirectLeafHighFinal.records_elapsed] at elapsed
 change (nodeRecords p visits A i.val i.isLt j).1+28 ≤ B ∧
  (nodeRecords p visits A i.val i.isLt j).2 ≤ B
 simp only[nodeRecords,dite_eq_left jl,UniformDirectLeafCacheLoopGeometry.slot,starts]
 constructor
 · simp only[UniformDirectLeafForestLeafEnd.qs]
   have start:(UniformDirectLeafForestForward.config p visits i.val).time ≤ p.rootDuration+4:=by
    simp only[UniformDirectLeafForestForward.config]
    omega
   omega
 · unfold cacheKind
   split <;>omega

lemma canonical_values (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n)):
 ∀q∈nodeRanges (UniformAxisCacheForestEntry.parameters c n j)
  (UniformAxisCacheForestEntry.visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val),
  ∀i,i < q.count → (q.records i).1+28 ≤ envelope c n ∧(q.records i).2 ≤ envelope c n:=
 node_values (UniformAxisCacheForestEntry.facts c n j) (horizon_room c n hn j)
end
end ExactFourierCircuits.UniformActualCacheRangeValues
