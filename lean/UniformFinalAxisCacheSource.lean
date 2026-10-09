import UniformFinalAxisCacheBundle
import UniformFinalOuterStartup

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheSource
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests UniformFinalAxisCacheBundle
noncomputable section

/-- All remaining selector inputs are factual projections of the actual
rectangle3776 and corrected leaf461 output, with canonical layout bounds. -/
structure Factual (c:Constants)(n:ℕ)(j:Fin (ell n))(s:State):Prop where
 source:UniformCacheRangeSelector.RangeSource (radix n j) (axis c n j).tasks (axis c n j).control
  (rectangleCount c n j) (UniformActualCacheRectangleSource.records
   (UniformActualCacheRectangleSource.entries n (canonical c n j))) (nodes c n j) s.natHeap
 layout:UniformCacheRangeSelector.Layout (radix n j) (axis c n j).tasks (axis c n j).control
  (rectangleCount c n j) (UniformFourierAxisWorkspace.axis c n j).selected (envelope c n) (nodes c n j)
 rectangleValues:∀i,i<rectangleCount c n j→
  (UniformActualCacheRectangleSource.records (UniformActualCacheRectangleSource.entries n (canonical c n j)) i).1+28≤envelope c n ∧
  (UniformActualCacheRectangleSource.records (UniformActualCacheRectangleSource.entries n (canonical c n j)) i).2≤envelope c n
 nodeValues:∀q∈nodes c n j,∀i,i<q.count→(q.records i).1+28≤envelope c n∧(q.records i).2≤envelope c n
 countFit:rectangleCount c n j+UniformCacheRangeSelector.total (nodes c n j)≤UniformJointCacheExtent.capacity (radix n j)
 nodesFit:(nodes c n j).length≤2*radix n j+1
 countWord:rectangleCount c n j+UniformCacheRangeSelector.total (nodes c n j)≤envelope c n
 selectedEnd:(UniformFourierAxisWorkspace.axis c n j).selected+
  2*(rectangleCount c n j+UniformCacheRangeSelector.total (nodes c n j))≤(UniformFourierAxisWorkspace.axis c n j).boundary
 duration:s.natHeap (axis c n j).durations=some (UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan (radix n j)))
 durationWord:2*UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan (radix n j))+5≤envelope c n
 code:90≤envelope c n

/-- No source/selected/matching/action certificate is supplied to this bridge. -/
theorem of_contents {c n hn j s}(h:UniformAxisCacheContents.Contents c n hn j s):Factual c n j s:=by
 obtain ⟨layout,rectangles,leaves,code,_⟩:=UniformActualCacheRangeSource.preconditions c n hn j
 have cap:=UniformActualCacheRangeBounds.total_capacity c n j
 change rectangleCount c n j+UniformCacheRangeSelector.total (nodes c n j)≤UniformJointCacheExtent.capacity (radix n j) at cap
 have capWord:UniformJointCacheExtent.capacity (radix n j)≤envelope c n:=
  (UniformAxisCacheForestGeometry.bounds c n hn j).capWord
 have selected:=(UniformFourierAxisWorkspace.axis_geometry c n j).1
 have selectedBound:=Nat.mul_le_mul_left 2 cap
 exact ⟨UniformActualCacheRangeSource.range_source (geometry c n hn j) h.rectangles h.leaves,
  layout,rectangles,leaves,cap,UniformActualCacheRangeBounds.nodes_bound c n j,cap.trans capWord,
  by omega,h.leaves.root,UniformFourierClockBounds.selected_word c hn j,code⟩

theorem of_all {c n hn s}(h:UniformAxisCacheLoopState.All c n hn (ell n) s)(j:Fin (ell n)):
 Factual c n j s:=of_contents (h j j.isLt)

def bundle_of_all {c n hn s}(h:UniformAxisCacheLoopState.All c n hn (ell n) s)(j:Fin (ell n)):=
 UniformFinalAxisCacheBundle.actual c n hn j (h j j.isLt)

theorem of_output {c n hn x s u}(h:UniformAxisCacheWholeExecution.Output c n hn x s u)(j:Fin (ell n)):
 Factual c n j u:=of_all h.all j

def bundle_of_output {c n hn x s u}(h:UniformAxisCacheWholeExecution.Output c n hn x s u)(j:Fin (ell n)):=
 bundle_of_all h.all j

theorem of_startup {n hn x cacheEntry s}(h:UniformFinalOuterStartup.Result n hn x cacheEntry s)
 (j:Fin (ell n)):Factual UniformActualGlobalConstants.constants n j s:=of_output h.cache j

def bundle_of_startup {n hn x cacheEntry s}(h:UniformFinalOuterStartup.Result n hn x cacheEntry s)
 (j:Fin (ell n)):=bundle_of_output h.cache j

/-- Cache intervals survive later operations independently of shared controller
registers. This also retains the actual root-duration and range cells. -/
theorem transport {c n hn j s u}(h:UniformAxisCacheContents.Contents c n hn j s)
 (keep:UniformAxisCachePhysical.Heaps c n j s u):Factual c n j u:=
 of_contents (UniformAxisCacheContents.transport h keep)

end
end ExactFourierCircuits.UniformFinalAxisCacheSource
