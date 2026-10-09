import UniformActualCacheRectangleSource
import UniformDirectLeafForestRangeSource
import UniformAxisCacheForestGeometry
import UniformFourierAxisWorkspace
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCacheRangeBounds
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestRangeSource
open UniformLocalCacheTreeMachine UniformLocalRequestPlan
noncomputable section

lemma total_eq_sum (qs:List UniformCacheRangeSelector.Range):
 UniformCacheRangeSelector.total qs=(qs.map (fun q=>q.count)).sum:=by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simpa only[UniformCacheRangeSelector.total,List.map_cons,List.sum_cons] using congrArg (q.count+·) ih

lemma node_length (p:Parameters)(visits:List Visit)(A:ℕ):
 (nodeRanges p visits A).length=visits.length:=List.length_ofFn
lemma node_total (p:Parameters)(visits:List Visit)(A:ℕ):
 UniformCacheRangeSelector.total (nodeRanges p visits A)=demand visits:=by
 rw[total_eq_sum]
 have mapped:(nodeRanges p visits A).map (fun q=>q.count)=visits.map operations:=by
  rw[nodeRanges,List.map_ofFn]
  exact (List.map_ofFn (f:=fun i:Fin visits.length=>visits[i]) (g:=operations)).symm.trans
   (congrArg (List.map operations) List.ofFn_getElem)
 rw[mapped]
 rfl

/-- Conservative scanner extent, including its extra stride, is bounded by
 the actual complete leaf cache frontier and one ordinary stride. -/
lemma node_end {p:Parameters}{visits:List Visit}{A:ℕ}
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (q:UniformCacheRangeSelector.Range)(member:q∈nodeRanges p visits A):
 UniformCacheRangeSelector.endAddress p.radix q ≤
 p.start.permutation+(3*p.radix+11)*demand visits+3*p.radix+11:=by
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 have next:=before_next visits i.val i.isLt
 have ending:=before_le visits (i.val+1)
 have rank:before visits i.val+operations visits[i.val] ≤ demand visits:=by omega
 have scaled:=Nat.mul_le_mul_left (3*p.radix+11) rank
 rw[Nat.mul_add] at scaled
 dsimp only[UniformCacheRangeSelector.endAddress,UniformCacheRangeSelector.stride,position]
 rw[entry]
 change p.start.permutation+3*p.radix+4+(3*p.radix+11)*before visits i.val+
  (3*p.radix+11)*operations visits[i.val]+7 ≤
  p.start.permutation+(3*p.radix+11)*demand visits+3*p.radix+11
 omega

lemma total_capacity (c:Constants)(n:ℕ)(j:Fin (ell n)):
 UniformAxisCacheForestEntry.rectangleCount c n j+
 UniformCacheRangeSelector.total (nodeRanges (UniformAxisCacheForestEntry.parameters c n j)
  (UniformAxisCacheForestEntry.visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)) ≤
 UniformJointCacheExtent.capacity (radix n j):=by
 rw[node_total]
 have h:=UniformAxisCacheForestGeometry.capacity c n j
 omega

lemma nodes_bound (c:Constants)(n:ℕ)(j:Fin (ell n)):
 (nodeRanges (UniformAxisCacheForestEntry.parameters c n j) (UniformAxisCacheForestEntry.visits c n j)
  (UniformAllAxisSeedPreparation.axisBase n j.val)).length ≤ 2*radix n j+1:=by
 rw[node_length]
 exact UniformAxisCacheTimingGeometry.nodes_bound _ _

/-- Fresh selection storage is after every produced cache. None of the range
 or count bounds is a supplied directory/layout certificate. -/
theorem layout (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n)):
 UniformCacheRangeSelector.Layout (radix n j) (axis c n j).tasks (axis c n j).control
  (UniformAxisCacheForestEntry.rectangleCount c n j) (UniformFourierAxisWorkspace.axis c n j).selected (envelope c n)
  (nodeRanges (UniformAxisCacheForestEntry.parameters c n j) (UniformAxisCacheForestEntry.visits c n j)
   (UniformAllAxisSeedPreparation.axisBase n j.val)):=by
 have positive:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 change 2 ≤ radix n j at positive
 have old:=(UniformFourierAxisWorkspace.caches_before c n j j).1
 have newer:=UniformFourierAxisWorkspace.axis_geometry c n j
 have fit:=UniformFourierAxisWorkspace.axis_fit c hn j
 have capacity:=total_capacity c n j
 have nodes:=nodes_bound c n j
 have bounds:=UniformAxisCacheForestGeometry.bounds c n hn j
 have spare:(axis c n j).leafForward+3*radix n j+11 ≤ (axis c n j).endNat:=by
  dsimp only[axis,axisBank]
  nlinarith only[positive]
 have rectEnd:(axis c n j).control+(3*radix n j+11)*
  UniformAxisCacheForestEntry.rectangleCount c n j ≤ (axis c n j).leafForward:=by
  have h:=bounds.cacheEnd
  have product:=Nat.mul_le_mul_left (3*radix n j+11)
   (Nat.le_add_right (UniformAxisCacheForestEntry.rectangleCount c n j)
    (demand (UniformAxisCacheForestEntry.visits c n j)))
  omega
 constructor
 · have h:(axis c n j).tasks+4*radix n j+6 ≤ (axis c n j).endNat:=by
    dsimp only[axis,axisBank]
    omega
   exact h.trans old
 · have h:(axis c n j).tasks+2*(2*radix n j+1)+2 ≤ (axis c n j).endNat:=by
    dsimp only[axis,axisBank]
    omega
   omega
 · change (axis c n j).control+3*radix n j+4+(3*radix n j+11)*
    UniformAxisCacheForestEntry.rectangleCount c n j+7 ≤ (UniformFourierAxisWorkspace.axis c n j).selected
   omega
 · intro q member
   have e:=node_end (p:=UniformAxisCacheForestEntry.parameters c n j)
    (A:=UniformAllAxisSeedPreparation.axisBase n j.val) (by rfl) q member
   change UniformCacheRangeSelector.endAddress (radix n j) q ≤ _ at e
   have cache:=bounds.cacheEnd
   dsimp only[UniformAxisCacheForestEntry.parameters] at e
   have rewrite:(axis c n j).control+(3*radix n j+11)*UniformAxisCacheForestEntry.rectangleCount c n j+
    (3*radix n j+11)*demand (UniformAxisCacheForestEntry.visits c n j)=
    (axis c n j).control+(3*radix n j+11)*
     (UniformAxisCacheForestEntry.rectangleCount c n j+demand (UniformAxisCacheForestEntry.visits c n j)):=by ring
   rw[rewrite] at e
   omega
 · have scaled:=Nat.mul_le_mul_left 2 capacity
   have boundary:=newer.1
   have chain:(UniformFourierAxisWorkspace.axis c n j).boundary ≤ (UniformFourierAxisWorkspace.axis c n j).endNat:=by
    have a:=newer.2.1;have b:=newer.2.2.1;have d:=newer.2.2.2.1
    have e:=newer.2.2.2.2.1;have f:=newer.2.2.2.2.2.1;have g:=newer.2.2.2.2.2.2
    omega
   unfold envelope
   omega
end
end ExactFourierCircuits.UniformActualCacheRangeBounds
