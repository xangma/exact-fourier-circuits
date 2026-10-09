import UniformLocalCacheTimingMetadata
import UniformLocalCacheTimingRows
import UniformCacheTimingReverseInitialization
import UniformCacheTimingForwardCanonical
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingInitialization
open UniformMachine UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution
open UniformLocalCacheTimingMetadata UniformCacheTimingReverseData
open UniformTensorMonomialMachine (setPC)

/-- Ordinary addresses only. Node/request counts come from the actual173
producer; no timing values or preinitialized timing banks are inputs. -/
structure Addresses (D R U V T:ℕ)(s:State):Prop where
 nodes:s.natReg 6500=D
 requests:s.natReg 6501=R
 durations:s.natReg 6502=U
 starts:s.natReg 6503=V
 requestStarts:s.natReg 6504=T

lemma Addresses.withPC {D R U V T:ℕ}{s:State}
 (h:Addresses D R U V T s)(pc:ℕ):Addresses D R U V T (setPC s pc):=
 ⟨h.nodes,h.requests,h.durations,h.starts,h.requestStarts⟩
lemma Addresses.produced {n D R U V T B t:ℕ}{x:Fin n→ℂ}{s a:State}
 (h:Addresses D R U V T s)
 (run:BoundedExecution UniformLocalCacheTreeMachine.program n x B s t a):
 Addresses D R U V T a:=by
 constructor
 · exact (execution_natFrame run 6500 (by omega)).trans h.nodes
 · exact (execution_natFrame run 6501 (by omega)).trans h.requests
 · exact (execution_natFrame run 6502 (by omega)).trans h.durations
 · exact (execution_natFrame run 6503 (by omega)).trans h.starts
 · exact (execution_natFrame run 6504 (by omega)).trans h.requestStarts

noncomputable section
/-- Literal122 startup and charged zeroing, fed by the physical173 tables and
its actual count/end registers. The initial reverse Bank is constructed. -/
theorem initialize_from_printed (n v o D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (addresses:Addresses D R U V T s)
 (directory:Directory D 0 (rootVisits v o R) s)
 (tables:RequestTables (rootVisits v o R) s)
 (nodes:s.natReg 4281=nodeCount v o R)
 (requests:s.natReg 4282=R+7*requestCount v o R)
 (layout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃u,
 BoundedRuns UniformCacheTimingProgram.program n x B s (5*nodeCount v o R+15) u∧
 u.pc=19∧UniformCacheTimingControl.Init D R U V T (nodeCount v o R)
  (requestCount v o R) (nodeCount v o R) u∧
 Bank D R U V T (rootVisits v o R) (nodeCount v o R) u∧
 (∀a,a<U∨U+nodeCount v o R≤a→u.natHeap a=s.natHeap a):=by
 have input:UniformCacheTimingStartup.Input D R U V T (nodeCount v o R) (requestCount v o R) s:=
  ⟨addresses.nodes,addresses.requests,addresses.durations,addresses.starts,addresses.requestStarts,nodes,requests⟩
 have dir:∀j,(hj:j<(rootVisits v o R).length)→
  UniformLocalCacheTreeIteration.AtNode D j (rootVisits v o R)[j].task (rootVisits v o R)[j].rectangleBase s:=by
  intro j hj
  simpa only [Nat.zero_add] using UniformCacheTimingForwardCanonical.directory_at directory j hj
 exact UniformCacheTimingReverseInitialization.execution n D R U V T (requestCount v o R) B
  (rootVisits v o R) x s input dir
  (UniformLocalCacheTimingRows.tableAt_of_requestTables _ s tables) layout
  (canonical_metadata v o R U B source duration rowWord) hp hs

/-- Two separate literal programs, with the invocation boundary stated as a
PC reset. This theorem does not assert a charged single-program composition. -/
theorem producer_initial_bank (n v o W D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (header:UniformLocalCacheTreeIteration.Header v o W D R s)
 (producerLayout:UniformLocalCacheTreeExecution.Layout v o W D R B)
 (addresses:Addresses D R U V T s)
 (timingLayout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃a ta u,
 BoundedExecution UniformLocalCacheTreeMachine.program n x B s ta a∧
 ta≤(2*v+1)*nodeBudget v+18∧a.pc=172∧
 BoundedRuns UniformCacheTimingProgram.program n x B (setPC a 0) (5*nodeCount v o R+15) u∧
 u.pc=19∧UniformCacheTimingControl.Init D R U V T (nodeCount v o R)
  (requestCount v o R) (nodeCount v o R) u∧
 Bank D R U V T (rootVisits v o R) (nodeCount v o R) u∧
 (∀q,q<W→a.natHeap q=s.natHeap q)∧
 (∀q,q<U∨U+nodeCount v o R≤q→u.natHeap q=a.natHeap q):=by
 obtain ⟨a,ta,run,time,ap,dir,tables,nodes,requests,low⟩:=
  UniformLocalCacheTreeExecution.execution n v o W D R B x s header producerLayout hp hs
 have bound:WordBound B (setPC a 0):=⟨by simp [setPC],run.final_bound.2⟩
 obtain ⟨u,init,up,out,bank,frame⟩:=initialize_from_printed n v o D R U V T B x (setPC a 0)
  ((addresses.produced run).withPC 0) (dir.withPC 0) (tables.withPC 0) nodes requests
  timingLayout source duration rowWord rfl bound
 exact ⟨a,ta,u,run,time,ap,init,up,out,bank,low,frame⟩
end
end ExactFourierCircuits.UniformLocalCacheTimingInitialization
