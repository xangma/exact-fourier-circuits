import UniformAxisCacheForestSource
import UniformDirectLeafForestState
import UniformDirectLeafCacheRetained
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestEntry
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation
open UniformAxisCacheInputs UniformAxisCacheForestHeader UniformAxisCacheCanonicalRequests
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration UniformLocalCacheTreeExecution
open UniformLocalCacheTimingMetadata UniformJointCacheAllocation UniformLocalRequestPlan
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestGeometry
noncomputable section

def visits (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):List Visit:=
 rootVisits (Seed.radix n j) 0 (axis c n j).requests
def rectangleCount (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):ℕ:=
 slotPrefix n (canonical c n j) (canonical c n j).length
def parameters (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):Parameters:=
 let a:=axis c n j
 let r:=Seed.radix n j
 let k:=rectangleCount c n j
 let P:=a.control+(3*r+11)*k
 {start:=⟨a.leafForward,Seed.directoryBase n+2*j.val,
   UniformAllAxisConjugatePreparation.directoryBase n+2*j.val,
   a.pool+9*r*k,UniformLocalRectangleWorkspaceHeaders.z n,
   P,P+r,P+2*r,P+3*r,P+3*r+4,0⟩,
  radix:=r,nodes:=a.nodes,starts:=a.nodeStarts,durations:=a.durations,
  forward:=a.leafForward,transpose:=a.leafTranspose,seedPool:=a.pool,
  rectangles:=k,rootDuration:=UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r),
  ranges:=a.tasks}

lemma directory_get (D k:ℕ) (qs:List Visit) (s:State) (h:Directory D k qs s)
 (i:ℕ) (hi:i<qs.length):AtNode D (k+i) qs[i].task qs[i].rectangleBase s:=by
 induction qs generalizing k i with
 | nil=>simp at hi
 | cons q qs ih=>
  cases i with
  | zero=>simpa only[Nat.add_zero,List.getElem_cons_zero] using h.1
  | succ i=>
   have bound:i<qs.length:=by simpa only[List.length_cons,Nat.succ_lt_succ_iff] using hi
   simpa only[List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    using ih (k+1) h.2 i bound

lemma directory_get_zero (D:ℕ) (qs:List Visit) (s:State) (h:Directory D 0 qs s):
 ∀i (hi:i<qs.length),AtNode D i qs[i].task qs[i].rectangleBase s:=by
 intro i hi
 simpa only[Nat.zero_add] using directory_get D 0 qs s h i hi

lemma printed_root (r R U V T:ℕ) (s:State)
 (h:UniformLocalCacheTimingExecution.Printed r 0 R U V T s):
 s.natHeap U=some (UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)):=by
 have root:=h.durations 0 (UniformAxisCacheRootDuration.root_positive r R)
 change s.natHeap U=some (UniformCacheTimingReference.taskDuration ⟨r,0,0,0⟩) at root
 simpa only[UniformCacheTimingReference.taskDuration,UniformLocalCacheTiming.ofPlan_duration] using root

/-- The exact leaf-entry header comes from the charged eight-op header,
real measured request ends, and the retained physical root-duration cell. -/
theorem header {c n j s}
 (prepared:Prepared c n j s)
 (ends:UniformLocalStoredRequestLoop.Endpoints c n j (canonical c n j)
  (axis c n j).requests (axis c n j).requestStarts s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) s)
 (source:UniformAxisCacheForestSource.Source c n j s)
 (radix:s.natReg 6800=Seed.radix n j):
 Header (parameters c n j) (visits c n j) s:=by
 have root:=printed_root _ _ _ _ _ s source.printed
 dsimp only [parameters]
 constructor
 · exact prepared.nodes
 · simpa only [visits,nodeCount] using prepared.count
 · exact prepared.starts
 · exact prepared.durations
 · exact prepared.original
 · exact prepared.conjugate
 · exact prepared.rows
 · exact ends.pool
 · exact ends.permutation
 · exact ends.widths.trans (congrArg (·+Seed.radix n j) ends.permutation)
 · exact ends.markers.trans (congrArg (·+2*Seed.radix n j) ends.permutation)
 · exact ends.physicalAxis.trans (congrArg (·+3*Seed.radix n j) ends.permutation)
 · exact ends.abi.trans (congrArg (fun P=>P+3*Seed.radix n j+4) ends.permutation)
 · exact result.leafForward
 · exact result.leafTranspose
 · exact radix
 · exact result.pool
 · exact root
 · exact result.tasks

/-- Actual directory and start cells supply every leaf source. No prepared
leaf action or output is an input. -/
theorem sources {c n j x s} (input:Inputs n x s)
 (source:UniformAxisCacheForestSource.Source c n j s):
 Sources (parameters c n j) (visits c n j) n s:=by
 refine ⟨input.original,input.conjugate,
  UniformDirectLeafCacheRetained.constants_of_operands input.operands,?_,?_⟩
 · intro i hi
   exact directory_get_zero _ _ s source.directory i hi
 · exact source.printed.nodes

theorem facts (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):
 Facts (parameters c n j) (visits c n j):=by
 constructor
 · intro i hi
   exact (root_extent _ _ _ (List.getElem_mem hi)).2
 · intro i hi stop
   exact root_leaf_duration _ _ i hi stop

end
end ExactFourierCircuits.UniformAxisCacheForestEntry
