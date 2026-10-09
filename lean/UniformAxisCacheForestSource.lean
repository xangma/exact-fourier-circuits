import UniformAxisCacheRectangleExecution
import UniformAxisCachePhysical
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestSource
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration UniformLocalCacheTreeExecution
open UniformLocalCacheTimingMetadata UniformLocalRectangleDescriptors UniformWorkspacePlanner
open UniformJointCacheAllocation UniformAxisCacheCanonicalRequests

structure Source (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)) (s:State):Prop where
 directory:Directory (axis c n j).nodes 0 (rootVisits (Seed.radix n j) 0 (axis c n j).requests) s
 tables:RequestTables (rootVisits (Seed.radix n j) 0 (axis c n j).requests) s
 printed:UniformLocalCacheTimingExecution.Printed (Seed.radix n j) 0 (axis c n j).requests
  (axis c n j).durations (axis c n j).nodeStarts (axis c n j).requestStarts s

lemma of_ready {c n j s} (h:UniformAxisCacheTimingExecution.Ready (Seed.radix n j)
 (natAt c n j.val) (scalarAt c n j.val) s):Source c n j s:=
 ⟨h.directory,h.tables,h.printed⟩

lemma directory_transport (D k limit:ℕ) (visits:List Visit) (s u:State)
 (extent:D+7*(k+visits.length)≤limit)
 (heap:∀a,D≤a→a<limit→u.natHeap a=s.natHeap a)
 (h:Directory D k visits s):Directory D k visits u:=by
 induction visits generalizing k with
 | nil=>trivial
 | cons q qs ih=>
  refine ⟨?_,ih (k+1) (by simp only [List.length_cons] at extent;omega) h.2⟩
  intro f
  rw [heap _ (by omega) (by have:=f.isLt;simp only [List.length_cons] at extent;omega)]
  exact h.1 f

lemma rectangle_bounds (r R C:ℕ) (source:R+7*requestCount r 0 R≤C)
 (q:Visit) (hq:q∈rootVisits r 0 R):R≤q.rectangleBase∧q.rectangleBase+7*emittedCount q.task.width≤C:=by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 subst q
 have base:((rootVisits r 0 R)[i]'hi).rectangleBase=R+7*visitSum ((rootVisits r 0 R).take i):=
  UniformCacheTimingMetadata.walk_rectangle_prefix _ _ _ _ i hi
 have ending:=UniformCacheTimingBounds.visitSum_request_end (rootVisits r 0 R) i hi
 rw [base]
 unfold requestCount at source
 omega

/-- The actual request program retains all genuine forest tables and charged
start/duration cells, because they are outside its cache-write interval. -/
theorem requests {c n j s u} (h:Source c n j s)
 (frame:UniformLocalStoredRequestLoop.LoopFrame c n j s u):Source c n j u:=by
 have lower:=UniformAxisCachePhysical.axis_lower c n j
 have nodes:=UniformAxisCacheTimingGeometry.nodes_bound (Seed.radix n j) (axis c n j).requests
 have directoryEnd:(axis c n j).nodes+7*(rootVisits (Seed.radix n j) 0 (axis c n j).requests).length≤
   (axis c n j).control:=by
  change nodeCount (Seed.radix n j) 0 (axis c n j).requests≤2*Seed.radix n j+1 at nodes
  change (rootVisits (Seed.radix n j) 0 (axis c n j).requests).length≤2*Seed.radix n j+1 at nodes
  dsimp only [axis,axisBank] at nodes ⊢
  omega
 have nodeLower:(axis c n j).tasks≤(axis c n j).nodes:=by dsimp only [axis,axisBank];omega
 have requestLower:(axis c n j).tasks≤(axis c n j).requests:=by dsimp only [axis,axisBank];omega
 have requestEnd:(axis c n j).requests+7*requestCount (Seed.radix n j) 0 (axis c n j).requests≤
   (axis c n j).control:=by
  have count:=UniformAxisCacheTimingGeometry.requests_bound (Seed.radix n j) (axis c n j).requests
  have factor:=Nat.mul_le_mul_right ((Seed.radix n j)^2) (show 1≤2*Seed.radix n j+2 by omega)
  simp only [Nat.one_mul] at factor
  have lifted:=Nat.mul_le_mul_left 7 (count.trans factor)
  dsimp only [axis,axisBank] at lifted ⊢
  simp only [Nat.mul_assoc] at lifted ⊢
  omega
 have highDurations:(axis c n j).leafForward≤(axis c n j).durations:=by dsimp only [axis,axisBank];omega
 have highStarts:(axis c n j).leafForward≤(axis c n j).nodeStarts:=by dsimp only [axis,axisBank];omega
 have highRequests:(axis c n j).leafForward≤(axis c n j).requestStarts:=by dsimp only [axis,axisBank];omega
 have leafLower:(axis c n j).tasks≤(axis c n j).leafForward:=by dsimp only [axis,axisBank];omega
 refine ⟨directory_transport _ _ (axis c n j).control _ s u (by simpa only [Nat.zero_add] using directoryEnd)
   (fun a lo hi=>frame.nat a (by omega) (Or.inl hi)) h.directory,?_,?_⟩
 · intro q hq large positive i j_ bound f
   have base:=rectangle_bounds _ _ _ requestEnd q hq
   have count:emittedCount q.task.width=
     chunkCount (q.task.width-q.task.width/2) (selected q.task.width)*
     chunkCount (q.task.width/2) (selected q.task.width):=by
    simp only [emittedCount,show ¬(q.task.width<2∨selected q.task.width=0) by omega,ite_false]
   rw [frame.nat _ (by omega) (Or.inl (by rw [count] at base;have:=f.isLt;omega))]
   exact h.tables q hq large positive i j_ bound f
 · constructor
   · intro k hk
     rw [frame.nat _ (by omega) (Or.inr (by omega))]
     exact h.printed.durations k hk
   · intro k hk
     rw [frame.nat _ (by omega) (Or.inr (by omega))]
     exact h.printed.nodes k hk
   · intro k hk i hi
     rw [frame.nat _ (by omega) (Or.inr (by omega))]
     exact h.printed.requests k hk i hi

end ExactFourierCircuits.UniformAxisCacheForestSource
