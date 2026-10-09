import UniformActualCacheRangeValues
import UniformCacheRangeSelectorOutput
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCacheRangeSource
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformDirectLeafForestData UniformDirectLeafForestRangeSource UniformLocalRequestPlan
open UniformActualCacheRectangleRetention UniformActualCacheRectangleSource
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests
noncomputable section

lemma before (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n)):
 Before c n j (canonical c n j) (parameters c n j) (visits c n j):=by
 have bounds:=UniformAxisCacheForestGeometry.bounds c n hn j
 have order:=UniformAxisCachePhysical.control_after_tasks c n j
 have nodes:=UniformAxisCacheTimingGeometry.nodes_bound (radix n j) (axis c n j).requests
 change (visits c n j).length ≤ 2*radix n j+1 at nodes
 constructor
 · rfl
 · rfl
 · rfl
 · change UniformLocalRectangleWorkspaceHeaders.z n+3 ≤ (axis c n j).control
   have h:=bounds.rows
   omega
 · change (axis c n j).tasks+2*(visits c n j).length ≤ (axis c n j).control
   dsimp only[axis,axisBank]
   omega
 · change (axis c n j).tasks+4*radix n j+4+2 ≤ (axis c n j).control
   dsimp only[axis,axisBank]
   omega

/-- Every completed rectangle entry survives the actual leaf loop's precise
 footprint. The ordinary separation is derived from the canonical allocator. -/
theorem rectangles_after_forest {c n j R T}
 (hn:0<n)(g:UniformLocalRequestGeometry.Geometry c n j (canonical c n j) R T)
 {s u:State}(frame:UniformDirectLeafForestExecution.Frame (parameters c n j) (visits c n j) s u)
 (old:∀i (hi:i < (canonical c n j).length),
  UniformLocalRequestGeometry.Complete c n j (canonical c n j) R T g i hi s):
 ∀i (hi:i < (canonical c n j).length),
  UniformLocalRequestGeometry.Complete c n j (canonical c n j) R T g i hi u:=
 all_completed g (before c n hn j) frame old

/-- Join the actual rectangle and leaf postconditions. All physical counts,
 node ranges, timestamps and kinds are read from the produced cache banks. -/
theorem range_source {c n j R T}
 (g:UniformLocalRequestGeometry.Geometry c n j (canonical c n j) R T)
 {s:State}{positive:2 ≤ radix n j}
 (rectangles:∀i (hi:i < (canonical c n j).length),
  UniformLocalRequestGeometry.Complete c n j (canonical c n j) R T g i hi s)
 (forest:UniformDirectLeafForestContents.Contents (parameters c n j) (visits c n j)
  (UniformAllAxisSeedPreparation.axisBase n j.val) positive s):
 UniformCacheRangeSelector.RangeSource (radix n j) (axis c n j).tasks (axis c n j).control
  (rectangleCount c n j) (records (entries n (canonical c n j)))
  (nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)) s.natHeap:=
 UniformDirectLeafForestRangeSource.range_source forest _ (rectangle_source g rectangles)

/-- Concrete producer-to-selector bridge: the request invariant is the
 output of literal3776, and Post/Frame are the output of literal461. No
 separately populated range, matching, action or selected-entry premise. -/
theorem after_forest {c n j R T}
 (hn:0<n)(g:UniformLocalRequestGeometry.Geometry c n j (canonical c n j) R T)
 {x:Fin n→ℂ}{s u:State}{positive:2 ≤ radix n j}
 (request:UniformLocalStoredRequestLoop.Ready c n j (canonical c n j) R T g x (canonical c n j).length s)
 (post:UniformDirectLeafForestExecution.Post (parameters c n j) (visits c n j) n
  (UniformAllAxisSeedPreparation.axisBase n j.val) positive u)
 (frame:UniformDirectLeafForestExecution.Frame (parameters c n j) (visits c n j) s u):
 UniformCacheRangeSelector.RangeSource (radix n j) (axis c n j).tasks (axis c n j).control
  (rectangleCount c n j) (records (entries n (canonical c n j)))
  (nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)) u.natHeap:=by
 apply range_source g
 · exact rectangles_after_forest hn g frame (fun i hi=>request.completed i hi hi)
 · exact UniformDirectLeafForestContents.ofPost post

/-- The same ordinary global envelope supplies every remaining numeric
 selector premise and a bound on its real measured runtime. -/
theorem preconditions (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n)):
 UniformCacheRangeSelector.Layout (radix n j) (axis c n j).tasks (axis c n j).control
  (rectangleCount c n j) (UniformFourierAxisWorkspace.axis c n j).selected (envelope c n)
  (nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)) ∧
 (∀i,i < rectangleCount c n j →
  (records (entries n (canonical c n j)) i).1+28 ≤ envelope c n ∧
  (records (entries n (canonical c n j)) i).2 ≤ envelope c n) ∧
 (∀q∈nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val),
  ∀i,i < q.count → (q.records i).1+28 ≤ envelope c n ∧(q.records i).2 ≤ envelope c n) ∧
 90 ≤ envelope c n ∧
 21*(rectangleCount c n j+UniformCacheRangeSelector.total
  (nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)))+
  16*(nodeRanges (parameters c n j) (visits c n j) (UniformAllAxisSeedPreparation.axisBase n j.val)).length+31 ≤
  21*UniformJointCacheExtent.capacity (radix n j)+16*(2*radix n j+1)+31:=by
 refine ⟨UniformActualCacheRangeBounds.layout c n hn j,
  rectangle_values (UniformAxisCacheCanonicalRequests.geometry c n hn j),
  UniformActualCacheRangeValues.canonical_values c n hn j,?_,?_⟩
 · have h:=fixed_large c
   unfold envelope
   omega
 · have total:=UniformActualCacheRangeBounds.total_capacity c n j
   have nodes:=UniformActualCacheRangeBounds.nodes_bound c n j
   have t:=Nat.mul_le_mul_left 21 total
   have m:=Nat.mul_le_mul_left 16 nodes
   omega
end
end ExactFourierCircuits.UniformActualCacheRangeSource
