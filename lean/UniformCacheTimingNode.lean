import UniformCacheTimingNodeBody
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingNode
open UniformMachine UniformCacheTimingProgram UniformCacheTimingControl
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeIteration (AtNode)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformLocalRectangleDescriptors (emittedCount)
open UniformCacheTimingRows (TableAt amounts writePrefixes)
open UniformCacheTimingNodeBody (value)

def budget (q:Visit):ℕ:=UniformCacheTimingRows.ticks (currentRows q.task)+34

def outputHeap (U V T R k child old:ℕ)(q:Visit)(heap:ℕ→Option ℕ):ℕ→Option ℕ:=
 UniformCacheTimingNodeStore.outputHeap U V k q.task.parent (value q child) (amounts (currentRows q.task)) old
  (writePrefixes T ((q.rectangleBase-R)/7) 0 (currentRows q.task) heap)

noncomputable section
/-- One actual reverse iteration: directory loads, selected/direct dispatch,
physical prefix stores, charged duration scanner, and parent max propagation. -/
theorem execution (n D R U V T N K k child old B:ℕ)(q:Visit)(x:Fin n→ℂ)(s:State)
 (h:Init D R U V T N K (k+1) s)(node:AtNode D k q.task q.rectangleBase s)
 (rowTable:TableAt q.rectangleBase 0 (currentRows q.task) s)
 (childValue:s.natHeap (U+k)=some child)(parentValue:s.natHeap (U+q.task.parent)=some old)
 (hp:s.pc=19)(hs:WordBound B s)(code:122≤B)
 (directory:D+7*(k+1)≤B)(durations:U+k≤B)(starts:V+k≤B)(separate:U+k<V)(separateStarts:V+k<T)
 (parentBefore:k=0∨q.task.parent<k)(parentIndex:q.task.parent≤k)
 (source:q.rectangleBase+7*emittedCount q.task.width+4≤T)
 (sourceBound:q.rectangleBase+7*emittedCount q.task.width+4≤B)
 (destination:T+(q.rectangleBase-R)/7+(currentRows q.task).length≤B)
 (durationBound:value q child≤B)(correctionBound:amounts (currentRows q.task)≤B)
 (budgets:∀a∈currentRows q.task,UniformCacheRowDurationMachine.budget a.a a.e≤B):∃t u,
 BoundedRuns program n x B s t u∧t≤budget q∧u.pc=19∧Init D R U V T N K k u∧
 u.natHeap=outputHeap U V T R k child old q s.natHeap:=by
 obtain ⟨read,rp,rh⟩:=UniformCacheTimingNodeRead.execution n D R U V T N K k child B q x s
  h node childValue hp hs code directory durations starts
 let a:=UniformCacheTimingNodeRead.readState R k q s
 obtain ⟨bt,b,body,bb,bp,bh,bheap⟩:=UniformCacheTimingNodeBody.execution n D R U V T N K k child B q x a rh
  rowTable rp read.final_bound code source sourceBound destination durationBound correctionBound budgets
 have bpval:b.natHeap (U+q.task.parent)=some old:=by
  rw [bheap]
  rw [UniformCacheTimingPrefix.writePrefixes_outside]
  · exact parentValue
  · left
    omega
 obtain ⟨u,store,up,uh,uheap,_⟩:=UniformCacheTimingNodeStore.execution n D R U V T N K k q.task.parent
  (value q child) (amounts (currentRows q.task)) old B x b bh bp body.final_bound code durations starts separate
  durationBound correctionBound parentBefore bpval
 refine ⟨20+bt+UniformCacheTimingNodeStore.ticks k old (value q child),u,(read.trans body).trans store,?_,up,uh,?_⟩
 · have storeBound:UniformCacheTimingNodeStore.ticks k old (value q child)≤8:=by
    unfold UniformCacheTimingNodeStore.ticks
    split_ifs <;>omega
   unfold budget
   omega
 · rw [uheap,bheap]
   rfl
end
end ExactFourierCircuits.UniformCacheTimingNode
