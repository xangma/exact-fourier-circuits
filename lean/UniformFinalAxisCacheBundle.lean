import UniformFinalAxisCacheRectangle
import UniformFinalAxisCacheTransfer
import UniformActualCalendarBundleFactoryEvents
import UniformActualCacheRangeSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheBundle
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests
open UniformActualCalendarRegistry UniformLocalRequestPlan
open UniformDirectLeafForestData UniformDirectLeafForestState
noncomputable section

variable (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))

def rows:List Request:=canonical c n j
def nodes:List UniformCacheRangeSelector.Range:=
 UniformDirectLeafForestRangeSource.nodeRanges (parameters c n j) (visits c n j) (axisBase n j.val)
def records:List (ℕ×ℕ):=UniformActualCalendarRectangleRegistry.entries n (rows c n j)

include hn in
lemma radix_fit:radix n j≤envelope c n:=by
 have h:=(UniformJointCacheAllocation.forestLayout c n hn j).native
 simpa only[axis_radix,Nat.zero_add] using h

include hn in
lemma forest_bounds:
 (parameters c n j).start.pool+9*(parameters c n j).radix*
  UniformDirectLeafForestModel.demand (visits c n j)≤(axis c n j).endScalar ∧
 (parameters c n j).start.permutation+(3*(parameters c n j).radix+11)*
  UniformDirectLeafForestModel.demand (visits c n j)≤(axis c n j).endNat:=by
 have b:=UniformAxisCacheForestGeometry.bounds c n hn j
 have leaf:(axis c n j).leafForward≤(axis c n j).endNat:=by dsimp only[axis,axisBank];omega
 constructor
 · simpa only[parameters,Nat.mul_add,Nat.add_assoc] using b.scalarEnd
 · simpa only[parameters,Nat.mul_add,Nat.add_assoc] using b.cacheEnd.trans leaf

/-- Proof-side conservative reference only. No three-slab placement is
required of the physical caller. -/
def reference {s:State}(h:UniformAxisCacheContents.Contents c n hn j s):
 Bundle (radix n j) (3*slab c n) (3*slab c n) (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) s:=by
 have ends:=ends_bound c n hn
 have fits:=axis_fit c n j
 exact of_actual (geometry c n hn j) h.rectangles h.leaves (facts c n j) hn le_rfl le_rfl
  (radix_fit c n hn j) rfl rfl
  ((forest_bounds c n hn j).1.trans (fits.2.trans (by omega)))
  ((forest_bounds c n hn j).2.trans (fits.1.trans (by omega)))

/-- The real producer-backed bundle at the actual ends of this axis's cache. -/
def actual {s:State}(h:UniformAxisCacheContents.Contents c n hn j s):
 Bundle (radix n j) (axis c n j).endScalar (axis c n j).endNat (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) s where
 rectangle:=UniformFinalAxisCacheRectangle.whole (geometry c n hn j) h.rectangles (radix_fit c n hn j)
 node:=fun i=>by
  have hi:i.val<(visits c n j).length:=by simpa only[nodes,
   UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt
  let index:Fin (visits c n j).length:=⟨i.val,hi⟩
  have f:=UniformActualCalendarForestRegistry.family h.leaves (facts c n j) rfl
   (forest_bounds c n hn j).1 (forest_bounds c n hn j).2 (radix_fit c n hn j) index
  have get:(nodes c n j).get i=
   (⟨(position (parameters c n j) (visits c n j) i.val).entry,
    UniformDirectLeafForestModel.operations (visits c n j)[i.val],
    UniformDirectLeafForestRangeSource.nodeRecords (parameters c n j) (visits c n j)
     (axisBase n j.val) i.val hi⟩:UniformCacheRangeSelector.Range):=List.getElem_ofFn i.isLt
  rw[get]
  exact f

lemma actual_node_make {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (visits c n j).length)(k:Fin (UniformDirectLeafForestModel.operations (visits c n j)[i]))(elapsed:ℕ):
 ((actual c n hn j h).node (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)).make k.val elapsed=
 UniformActualCalendarDirectProduced.event (UniformActualCalendarForestRegistry.data h.leaves i k) elapsed:=by
 let f:=UniformActualCalendarForestRegistry.family h.leaves (facts c n j) rfl
  (forest_bounds c n hn j).1 (forest_bounds c n hn j).2 (radix_fit c n hn j) i
 have get:(nodes c n j).get (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)=
  (⟨(position (parameters c n j) (visits c n j) i.val).entry,
   UniformDirectLeafForestModel.operations (visits c n j)[i],
   UniformDirectLeafForestRangeSource.nodeRecords (parameters c n j) (visits c n j)
    (axisBase n j.val) i.val i.isLt⟩:UniformCacheRangeSelector.Range):=List.getElem_ofFn _
 have projection:((actual c n hn j h).node (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)).make=f.make:=by
  unfold actual
  exact Family.range_make_mpr _ _ get f
 exact (congrFun (congrFun projection k.val) elapsed).trans
  (UniformActualCalendarForestRegistry.family_make h.leaves (facts c n j) rfl
   (forest_bounds c n hn j).1 (forest_bounds c n hn j).2 (radix_fit c n hn j) i k elapsed)

lemma reference_node_make {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (visits c n j).length)(k:Fin (UniformDirectLeafForestModel.operations (visits c n j)[i]))(elapsed:ℕ):
 ((reference c n hn j h).node (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)).make k.val elapsed=
 UniformActualCalendarDirectProduced.event (UniformActualCalendarForestRegistry.data h.leaves i k) elapsed:=by
 unfold reference
 apply UniformActualCalendarRegistry.actual_node_make (geometry c n hn j) h.rectangles h.leaves (facts c n j) hn

lemma rectangle_make_eq {s:State}(h:UniformAxisCacheContents.Contents c n hn j s):
 (actual c n hn j h).rectangle.make=(reference c n hn j h).rectangle.make:=by
 change (UniformFinalAxisCacheRectangle.whole (geometry c n hn j) h.rectangles (radix_fit c n hn j)).make=_
 rw[UniformFinalAxisCacheRectangle.whole_make_eq _ _ hn]
 rfl

lemma node_make_eq {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (nodes c n j).length):
 ((actual c n hn j h).node i).make=((reference c n hn j h).node i).make:=by
 have hi:i.val<(visits c n j).length:=by
  simpa only[nodes,UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt
 let index:Fin (visits c n j).length:=⟨i.val,hi⟩
 have indexEq:nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) index=i:=Fin.ext rfl
 rw[←indexEq]
 funext k elapsed
 by_cases hk:k<UniformDirectLeafForestModel.operations (visits c n j)[index]
 · exact (actual_node_make c n hn j h index ⟨k,hk⟩ elapsed).trans
    (reference_node_make c n hn j h index ⟨k,hk⟩ elapsed).symm
 · have length:(List.ofFn (fun z:Fin ((nodes c n j).get (nodeIndex (parameters c n j)
    (visits c n j) (axisBase n j.val) index)).count=>
    ((nodes c n j).get (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) index)).records z.val)).length=
    UniformDirectLeafForestModel.operations (visits c n j)[index]:=by
    simp only[List.length_ofFn,nodes,UniformDirectLeafForestRangeSource.nodeRanges,
     List.get_eq_getElem,List.getElem_ofFn,nodeIndex,index]
   simp only[Family.make,length,dite_eq_right hk]

/-- Every emitted event is exactly the frozen factory event used by the
semantic calendar proof, although operational read bounds are now tight. -/
theorem events_eq {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)(tick:ℕ):
 (actual c n hn j h).events tick=(reference c n hn j h).events tick:=
 UniformFinalAxisCacheTransfer.bundle_events_eq _ _ (rectangle_make_eq c n hn j h)
  (node_make_eq c n hn j h) tick

end
end ExactFourierCircuits.UniformFinalAxisCacheBundle
