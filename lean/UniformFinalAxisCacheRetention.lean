import UniformFinalAxisCacheBundle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheRetention
open UniformMachine UniformGlobalCalendarDispatch UniformActualCalendarRegistry
open UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests UniformFinalAxisCacheBundle
noncomputable section

variable (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))

lemma rectangle_lower {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (k elapsed:ℕ)(hk:k<(records c n j).length):
 (axis c n j).pool≤((actual c n hn j h).rectangle.make k elapsed).descriptor.pool:=by
 obtain ⟨i,hi,t,ht,rfl⟩:=UniformFinalAxisCacheRectangle.entries_index n (canonical c n j) k hk
 change (axis c n j).pool≤
  ((UniformFinalAxisCacheRectangle.whole (geometry c n hn j) h.rectangles (radix_fit c n hn j)).make _ elapsed).descriptor.pool
 rw[UniformFinalAxisCacheRectangle.whole_make _ _ _ i hi t elapsed ht]
 change (axis c n j).pool≤
  (UniformLocalCacheSlotConductorMachine.Cursor.shifted
   (UniformLocalRequestPlan.controller c n j (canonical c n j) i) t).pool
 rw[UniformLocalRequestPlan.controller,UniformLocalRequestPlan.requestAt_eq _ i hi]
 change (axis c n j).pool≤(axis c n j).pool+9*radix n j*slotPrefix n (canonical c n j) i+9*radix n j*t
 omega

lemma leaf_lower {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (visits c n j).length)(k:Fin (UniformDirectLeafForestModel.operations (visits c n j)[i]))(elapsed:ℕ):
 (axis c n j).pool≤
  (((actual c n hn j h).node (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)).make k.val elapsed).descriptor.pool:=by
 rw[actual_node_make c n hn j h i k elapsed]
 have b:=UniformDirectLeafForestContents.slot_bounds (p:=parameters c n j)
  (A:=axisBase n j.val) rfl i.isLt (UniformActualCalendarForestRegistry.is_leaf i k)
  (UniformActualCalendarForestRegistry.record_bound i k)
 change (axis c n j).pool≤
  (UniformDirectLeafCacheLoopGeometry.slot (UniformDirectLeafForestForward.config (parameters c n j) (visits c n j) i.val)
   (radix n j) (UniformDirectLeafForestLeafEnd.qs (parameters c n j) (axisBase n j.val) (visits c n j)[i]) k.val).pool
 have low:(axis c n j).pool≤(parameters c n j).start.pool:=by dsimp only[parameters];omega
 exact low.trans b.1

lemma node_lower {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (nodes c n j).length)(k elapsed:ℕ)
 (hk:k<(List.ofFn (fun z:Fin ((nodes c n j).get i).count=>((nodes c n j).get i).records z.val)).length):
 (axis c n j).pool≤(((actual c n hn j h).node i).make k elapsed).descriptor.pool:=by
 have hi:i.val<(visits c n j).length:=by
  simpa only[nodes,UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt
 let index:Fin (visits c n j).length:=⟨i.val,hi⟩
 have get:(nodes c n j).get i=
  (⟨(UniformDirectLeafForestData.position (parameters c n j) (visits c n j) i.val).entry,
   UniformDirectLeafForestModel.operations (visits c n j)[i.val],
   UniformDirectLeafForestRangeSource.nodeRecords (parameters c n j) (visits c n j)
    (axisBase n j.val) i.val hi⟩:UniformCacheRangeSelector.Range):=List.getElem_ofFn i.isLt
 have ke:k<UniformDirectLeafForestModel.operations (visits c n j)[index]:=by
  rw[List.length_ofFn,get] at hk
  exact hk
 have eq:nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) index=i:=Fin.ext rfl
 rw[←eq]
 exact leaf_lower c n hn j h index ⟨k,ke⟩ elapsed

def family_interval {r O T B low D stride:ℕ}{L:List (ℕ×ℕ)}{s u:State}
 (f:Family r O T B D stride L s)
 (lower:∀k elapsed,k<L.length→low≤(f.make k elapsed).descriptor.pool)
 (natKeep:∀z,z<T→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,low≤z→z<O→u.scalarHeap z=s.scalarHeap z):Family r O T B D stride L u:=
 UniformFinalAxisCacheTransfer.family f (fun i elapsed bound=>
  UniformFinalAxisCacheTransfer.interval ((f.entry i).cached elapsed bound)
   (by simpa only[Family.make,dite_eq_left i.isLt] using lower i.val elapsed i.isLt) natKeep scalarKeep)

/-- Later clock phases keep exactly the persistent coefficient interval and
Nat source prefix. Event factories are retained verbatim, not reselected. -/
def transferred {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z):
 Bundle (radix n j) (axis c n j).endScalar (axis c n j).endNat (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) u where
 rectangle:=family_interval (actual c n hn j h).rectangle (fun k elapsed hk=>rectangle_lower c n hn j h k elapsed hk) natKeep scalarKeep
 node:=fun i=>family_interval ((actual c n hn j h).node i)
  (fun k elapsed hk=>node_lower c n hn j h i k elapsed hk) natKeep scalarKeep

lemma transferred_events {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z)(tick:ℕ):
 (transferred c n hn j h natKeep scalarKeep).events tick=(actual c n hn j h).events tick:=
 UniformFinalAxisCacheTransfer.bundle_events_eq _ _ rfl (fun _=>rfl) tick

theorem transferred_reference {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z)(tick:ℕ):
 (transferred c n hn j h natKeep scalarKeep).events tick=(reference c n hn j h).events tick:=
 (transferred_events c n hn j h natKeep scalarKeep tick).trans (events_eq c n hn j h tick)

/-- Operational dispatch may use the later fresh merged banks. This changes
only the ordinary read bounds; actual events and source values are unchanged. -/
theorem at_merged {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)(tick:ℕ):
 ∀e∈(actual c n hn j h).events tick,
 CachedEvent (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e s:=by
 have before:=UniformFourierAxisWorkspace.caches_before c n j j
 have selected:(UniformFourierAxisWorkspace.axis c n j).selected≤(UniformFourierAxisWorkspace.axis c n j).rawRows:=by
  have g:=UniformFourierAxisWorkspace.axis_geometry c n j
  omega
 intro e he
 exact UniformFinalAxisCacheTransfer.monotone ((actual c n hn j h).cached tick e he) before.2 (before.1.trans selected)

theorem transferred_merged {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z)(tick:ℕ):
 ∀e∈(transferred c n hn j h natKeep scalarKeep).events tick,
 CachedEvent (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e u:=by
 have before:=UniformFourierAxisWorkspace.caches_before c n j j
 have selected:(UniformFourierAxisWorkspace.axis c n j).selected≤(UniformFourierAxisWorkspace.axis c n j).rawRows:=by
  have g:=UniformFourierAxisWorkspace.axis_geometry c n j
  omega
 intro e he
 exact UniformFinalAxisCacheTransfer.monotone
  ((transferred c n hn j h natKeep scalarKeep).cached tick e he) before.2 (before.1.trans selected)

lemma merged_bounds:
 (axis c n j).endScalar≤(UniformFourierAxisWorkspace.axis c n j).pool ∧
 (axis c n j).endNat≤(UniformFourierAxisWorkspace.axis c n j).rawRows:=by
 have before:=UniformFourierAxisWorkspace.caches_before c n j j
 have selected:(UniformFourierAxisWorkspace.axis c n j).selected≤(UniformFourierAxisWorkspace.axis c n j).rawRows:=by
  have g:=UniformFourierAxisWorkspace.axis_geometry c n j
  omega
 exact ⟨before.2,before.1.trans selected⟩

def merged {s:State}(h:UniformAxisCacheContents.Contents c n hn j s):
 Bundle (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) s:=
 UniformFinalAxisCacheTransfer.bundle_mono (actual c n hn j h)
  (merged_bounds c n j).1 (merged_bounds c n j).2

def merged_transferred {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z):
 Bundle (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) u:=
 UniformFinalAxisCacheTransfer.bundle_mono (transferred c n hn j h natKeep scalarKeep)
  (merged_bounds c n j).1 (merged_bounds c n j).2

lemma merged_transferred_events {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (natKeep:∀z,z<(axis c n j).endNat→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→u.scalarHeap z=s.scalarHeap z)(tick:ℕ):
 (merged_transferred c n hn j h natKeep scalarKeep).events tick=(reference c n hn j h).events tick:=
 (UniformFinalAxisCacheTransfer.bundle_mono_events _ _ _ tick).trans
  (transferred_reference c n hn j h natKeep scalarKeep tick)

end
end ExactFourierCircuits.UniformFinalAxisCacheRetention
