import UniformFinalAxisCacheRetention

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheIntervalRetention
open UniformMachine UniformGlobalCalendarDispatch UniformActualCalendarRegistry
open UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests UniformFinalAxisCacheBundle UniformLocalRequestPlan
noncomputable section

/-- Both Nat and scalar source banks are retained only over their actual
allocated intervals. Writes to lower global directories remain permitted. -/
lemma interval {r O T B lowNat lowScalar:ℕ}{e:Event}{s u:State}
 (h:CachedEvent r O T B e s)(address:lowNat≤e.descriptor.address)
 (permutation:lowNat≤e.descriptor.permutation)(pool:lowScalar≤e.descriptor.pool)
 (natKeep:∀z,lowNat≤z→z<T→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,lowScalar≤z→z<O→u.scalarHeap z=s.scalarHeap z):CachedEvent r O T B e u:=by
 refine ⟨h.decoded,?_,?_,h.entryFit,h.sourcePool,h.sourceRows,h.matching,h.values⟩
 · rcases h.stored with ⟨p,w,f,k⟩
   exact ⟨(natKeep _ (by omega) (by have:=h.entryFit;omega)).trans p,
    (natKeep _ (by omega) (by have:=h.entryFit;omega)).trans w,
    (natKeep _ (by omega) (by have:=h.entryFit;omega)).trans f,
    (natKeep _ (by omega) (by have:=h.entryFit;omega)).trans k⟩
 · have source:=h.source
   cases phase:e.phase with
   | diagonal lane=>
     simp only[phase,UniformGlobalCalendarDispatch.Source] at source ⊢
     intro i hi
     have mul:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
     rw[scalarKeep _ (by omega) (by have:=h.sourcePool;omega)]
     exact source i hi
   | kernel=>
     simp only[phase,UniformGlobalCalendarDispatch.Source] at source ⊢
     intro i hi
     exact ⟨(natKeep _ (by omega) (by have:=h.sourceRows;omega)).trans (source i hi).1,
      (natKeep _ (by omega) (by have:=h.sourceRows;omega)).trans (source i hi).2⟩

variable (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))

lemma rectangle_permutation {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (k elapsed:ℕ)(hk:k<(records c n j).length):
 (axis c n j).tasks≤((actual c n hn j h).rectangle.make k elapsed).descriptor.permutation:=by
 obtain ⟨i,hi,t,ht,rfl⟩:=UniformFinalAxisCacheRectangle.entries_index n (canonical c n j) k hk
 change (axis c n j).tasks≤
  ((UniformFinalAxisCacheRectangle.whole (geometry c n hn j) h.rectangles (radix_fit c n hn j)).make _ elapsed).descriptor.permutation
 rw[UniformFinalAxisCacheRectangle.whole_make _ _ _ i hi t elapsed ht]
 change (axis c n j).tasks≤
  (UniformLocalCacheSlotConductorMachine.Cursor.shifted (controller c n j (canonical c n j) i) t).cachePermutation
 rw[controller,requestAt_eq _ i hi]
 have low:=UniformAxisCachePhysical.control_after_tasks c n j
 change (axis c n j).tasks≤(axis c n j).control+(3*radix n j+11)*slotPrefix n (canonical c n j) i+(3*radix n j+11)*t
 omega

lemma leaf_permutation {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (visits c n j).length)(k:Fin (UniformDirectLeafForestModel.operations (visits c n j)[i]))(elapsed:ℕ):
 (axis c n j).tasks≤
  (((actual c n hn j h).node (nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) i)).make k.val elapsed).descriptor.permutation:=by
 rw[actual_node_make c n hn j h i k elapsed]
 have b:=UniformDirectLeafForestContents.slot_bounds (p:=parameters c n j)
  (A:=axisBase n j.val) rfl i.isLt (UniformActualCalendarForestRegistry.is_leaf i k)
  (UniformActualCalendarForestRegistry.record_bound i k)
 change (axis c n j).tasks≤
  (UniformDirectLeafCacheLoopGeometry.slot (UniformDirectLeafForestForward.config (parameters c n j) (visits c n j) i.val)
   (radix n j) (UniformDirectLeafForestLeafEnd.qs (parameters c n j) (axisBase n j.val) (visits c n j)[i]) k.val).permutation
 have low:(axis c n j).tasks≤(parameters c n j).start.permutation:=by
  have before:=UniformAxisCachePhysical.control_after_tasks c n j
  dsimp only[parameters];omega
 exact low.trans b.2.2.1

lemma node_bounds {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (i:Fin (nodes c n j).length):
 (axis c n j).tasks≤((nodes c n j).get i).base ∧
 ∀k elapsed,k<(List.ofFn (fun z:Fin ((nodes c n j).get i).count=>((nodes c n j).get i).records z.val)).length→
 (axis c n j).tasks≤(((actual c n hn j h).node i).make k elapsed).descriptor.permutation:=by
 have hi:i.val<(visits c n j).length:=by
  simpa only[nodes,UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt
 let index:Fin (visits c n j).length:=⟨i.val,hi⟩
 have get:(nodes c n j).get i=
  (⟨(UniformDirectLeafForestData.position (parameters c n j) (visits c n j) i.val).entry,
   UniformDirectLeafForestModel.operations (visits c n j)[i.val],
   UniformDirectLeafForestRangeSource.nodeRecords (parameters c n j) (visits c n j)
    (axisBase n j.val) i.val hi⟩:UniformCacheRangeSelector.Range):=List.getElem_ofFn i.isLt
 constructor
 · rw[get]
   have low:=UniformAxisCachePhysical.control_after_tasks c n j
   dsimp only[UniformDirectLeafForestData.position,parameters]
   omega
 · intro k elapsed hk
   have ke:k<UniformDirectLeafForestModel.operations (visits c n j)[index]:=by
    rw[List.length_ofFn,get] at hk;exact hk
   have eq:nodeIndex (parameters c n j) (visits c n j) (axisBase n j.val) index=i:=Fin.ext rfl
   rw[←eq]
   exact leaf_permutation c n hn j h index ⟨k,ke⟩ elapsed

def family_interval {r O T B lowNat lowScalar D stride:ℕ}{L:List (ℕ×ℕ)}{s u:State}
 (f:Family r O T B D stride L s)(base:lowNat≤D)
 (permutation:∀k elapsed,k<L.length→lowNat≤(f.make k elapsed).descriptor.permutation)
 (pool:∀k elapsed,k<L.length→lowScalar≤(f.make k elapsed).descriptor.pool)
 (natKeep:∀z,lowNat≤z→z<T→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,lowScalar≤z→z<O→u.scalarHeap z=s.scalarHeap z):Family r O T B D stride L u:=
 UniformFinalAxisCacheTransfer.family f (fun i elapsed bound=>
  interval ((f.entry i).cached elapsed bound)
   (by rw[(f.entry i).address_eq];omega)
   (by simpa only[Family.make,dite_eq_left i.isLt] using permutation i.val elapsed i.isLt)
   (by simpa only[Family.make,dite_eq_left i.isLt] using pool i.val elapsed i.isLt) natKeep scalarKeep)

/-- Actual later-clock frames suffice even when lower D2/physical rows change. -/
def transferred {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (keep:UniformAxisCachePhysical.Heaps c n j s u):
 Bundle (radix n j) (axis c n j).endScalar (axis c n j).endNat (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) u where
 rectangle:=family_interval n (actual c n hn j h).rectangle
  (by have low:=UniformAxisCachePhysical.control_after_tasks c n j;unfold UniformActualCalendarRectangleRegistry.base;omega)
  (rectangle_permutation c n hn j h) (UniformFinalAxisCacheRetention.rectangle_lower c n hn j h) keep.nat keep.scalar
 node:=fun i=>family_interval n ((actual c n hn j h).node i)
  (node_bounds c n hn j h i).1 (node_bounds c n hn j h i).2
  (UniformFinalAxisCacheRetention.node_lower c n hn j h i) keep.nat keep.scalar

lemma transferred_events {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (keep:UniformAxisCachePhysical.Heaps c n j s u)(tick:ℕ):
 (transferred c n hn j h keep).events tick=(actual c n hn j h).events tick:=
 UniformFinalAxisCacheTransfer.bundle_events_eq _ _ rfl (fun _=>rfl) tick

def merged_transferred {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (keep:UniformAxisCachePhysical.Heaps c n j s u):
 Bundle (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n)
  (UniformActualCalendarRectangleRegistry.base c n j) (records c n j) (nodes c n j) u:=
 UniformFinalAxisCacheTransfer.bundle_mono (transferred c n hn j h keep)
  (UniformFinalAxisCacheRetention.merged_bounds c n j).1 (UniformFinalAxisCacheRetention.merged_bounds c n j).2

lemma merged_transferred_events {s u:State}(h:UniformAxisCacheContents.Contents c n hn j s)
 (keep:UniformAxisCachePhysical.Heaps c n j s u)(tick:ℕ):
 (merged_transferred c n hn j h keep).events tick=(reference c n hn j h).events tick:=
 (UniformFinalAxisCacheTransfer.bundle_mono_events _ _ _ tick).trans
  ((transferred_events c n hn j h keep tick).trans (events_eq c n hn j h tick))

end
end ExactFourierCircuits.UniformFinalAxisCacheIntervalRetention
