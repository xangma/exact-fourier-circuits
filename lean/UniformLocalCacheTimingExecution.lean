import UniformLocalCacheTimingInitialization
import UniformCacheTimingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingExecution
open UniformMachine UniformLocalCacheTreeExecution UniformLocalCacheTimingMetadata
open UniformLocalCacheTimingInitialization UniformCacheTimingReference
open UniformTensorMonomialMachine (setPC)

def printerBudget (v o R:ℕ):ℕ:=5*nodeCount v o R+15+
 UniformCacheTimingReverseData.ticks (rootVisits v o R) (nodeCount v o R)+
 UniformCacheTimingForwardLoop.ticks (UniformCacheTimingForwardCanonical.data (rootVisits v o R))
  0 (nodeCount v o R)+2

/-- The physical timing outputs, with durations identified with the ordinary
canonical recursive schedule. All request starts come from charged code. -/
structure Printed (v o R U V T:ℕ)(s:State):Prop where
 durations:∀k,(hk:k<nodeCount v o R)→
  s.natHeap (U+k)=some (taskDuration (rootVisits v o R)[k].task)
 nodes:∀k,k<nodeCount v o R→s.natHeap (V+k)=some 0
 requests:∀k,(hk:k<nodeCount v o R)→∀j,
  j<UniformLocalRectangleDescriptors.emittedCount (rootVisits v o R)[k].task.width→
  s.natHeap (T+visitSum ((rootVisits v o R).take k)+j)=
   some (requestStart (rootVisits v o R)[k] j)

noncomputable section
/-- Complete literal122 execution from actual physical tables, deriving every
Metadata field internally. No duration/start/height bank is an input. -/
theorem execute_from_printed (n v o D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (addresses:Addresses D R U V T s)
 (directory:Directory D 0 (rootVisits v o R) s)
 (tables:RequestTables (rootVisits v o R) s)
 (nodes:s.natReg 4281=nodeCount v o R)
 (requests:s.natReg 4282=R+7*requestCount v o R)
 (layout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃t u,
 BoundedExecution UniformCacheTimingProgram.program n x B s t u∧t≤printerBudget v o R∧
 Printed v o R U V T u∧
 (∀a,(a<U∨U+nodeCount v o R≤a)→(a<V∨V+nodeCount v o R≤a)→
  (a<T∨T+requestCount v o R≤a)→u.natHeap a=s.natHeap a)∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀r,r<6500∨6600≤r→u.natReg r=s.natReg r):=by
 have input:UniformCacheTimingStartup.Input D R U V T (nodeCount v o R) (requestCount v o R) s:=
  ⟨addresses.nodes,addresses.requests,addresses.durations,addresses.starts,addresses.requestStarts,nodes,requests⟩
 obtain ⟨t,u,run,time,values,starts,ready,frame,scalars,registers⟩:=
  UniformCacheTimingExecution.execution n v o D R U V T B x s input directory
   (UniformLocalCacheTimingRows.tableAt_of_requestTables _ s tables) layout
   (canonical_metadata v o R U B source duration rowWord) duration hp hs
 refine ⟨t,u,run,time,⟨?_,starts,ready⟩,frame,scalars,registers⟩
 intro k hk
 exact (values k hk).trans (congrArg some (UniformCacheTimingBottomUp.root_bottomUp v o R k hk))

/-- Actual173 followed by a separate invocation of actual122. The explicit PC
reset is the remaining conductor boundary, not a charged composition claim. -/
theorem producer_timing (n v o W D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (header:UniformLocalCacheTreeIteration.Header v o W D R s)
 (producerLayout:UniformLocalCacheTreeExecution.Layout v o W D R B)
 (addresses:Addresses D R U V T s)
 (timingLayout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃a ta t u,
 BoundedExecution UniformLocalCacheTreeMachine.program n x B s ta a∧
 ta≤(2*v+1)*nodeBudget v+18∧a.pc=172∧
 BoundedExecution UniformCacheTimingProgram.program n x B (setPC a 0) t u∧
 t≤printerBudget v o R∧Printed v o R U V T u∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀r,(r<290∨4295≤r)→(r<6500∨6600≤r)→u.natReg r=s.natReg r)∧
 (∀q,q<W→(q<U∨U+nodeCount v o R≤q)→(q<V∨V+nodeCount v o R≤q)→
  (q<T∨T+requestCount v o R≤q)→u.natHeap q=s.natHeap q):=by
 obtain ⟨a,ta,run,time,ap,dir,tables,nodes,requests,low⟩:=
  UniformLocalCacheTreeExecution.execution n v o W D R B x s header producerLayout hp hs
 have bound:WordBound B (setPC a 0):=⟨by simp [setPC],run.final_bound.2⟩
 obtain ⟨t,u,timing,budget,printed,frame,scalars,registers⟩:=execute_from_printed n v o D R U V T B x (setPC a 0)
  ((addresses.produced run).withPC 0) (dir.withPC 0) (tables.withPC 0) nodes requests
  timingLayout source duration rowWord rfl bound
 have producerScalars:=execution_scalarFrame run
 have timingScalars:UniformLocalRectangleDescriptors.ScalarFrame a u:=
  ⟨scalars.scalarHeap,scalars.scalarReg,scalars.outputs,scalars.rootOrders⟩
 refine ⟨a,ta,t,u,run,time,ap,timing,budget,printed,producerScalars.trans timingScalars,?_,?_⟩
 · intro r producerReg timingReg
   exact (registers r timingReg).trans (execution_natFrame run r producerReg)
 · intro q lowq hU hV hT
   exact (frame q hU hV hT).trans (low q lowq)
end
end ExactFourierCircuits.UniformLocalCacheTimingExecution
