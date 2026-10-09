import UniformCacheTimingNode
import UniformCacheTimingReference
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingReverseData
open UniformMachine UniformCacheTimingRows
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeIteration (AtNode)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformLocalRectangleDescriptors (emittedCount)
open UniformCacheTimingReference

def ordinal (R:ℕ)(q:Visit):ℕ:=(q.rectangleBase-R)/7
structure Layout (D U V T N K B:ℕ):Prop where
 code:122≤B
 directory:D+7*N≤U
 durations:U+N≤V
 starts:V+N≤T
 requests:T+K≤B
structure Metadata (R U K B:ℕ)(visits:List Visit):Prop where
 parentIndex:∀j,(hj:j<visits.length)→visits[j].task.parent≤j
 parentBefore:∀j,(hj:j<visits.length)→0<j→visits[j].task.parent<j
 source:∀q∈visits,q.rectangleBase+7*emittedCount q.task.width+4≤U
 requests:∀q∈visits,ordinal R q+(currentRows q.task).length≤K
 ordered:∀i j,(hi:i<visits.length)→(hj:j<visits.length)→i<j→
   ordinal R visits[i]+(currentRows visits[i].task).length≤ordinal R visits[j]
 durations:∀i,i≤visits.length→∀j,j<visits.length→processedSuffix visits i j≤B
 corrections:∀q∈visits,correction q≤B
 rowBudgets:∀q∈visits,∀a∈currentRows q.task,UniformCacheRowDurationMachine.budget a.a a.e≤B

noncomputable section
structure Bank (D R U V T:ℕ)(visits:List Visit)(i:ℕ)(s:State):Prop where
 directory:∀j,(hj:j<visits.length)→AtNode D j visits[j].task visits[j].rectangleBase s
 rows:∀q∈visits,TableAt q.rectangleBase 0 (currentRows q.task) s
 durations:∀j,j<visits.length→s.natHeap (U+j)=some (processedSuffix visits i j)
 corrections:∀j,(hj:j<visits.length)→i≤j→s.natHeap (V+j)=some (correction visits[j])
 prefixes:∀j,(hj:j<visits.length)→i≤j→∀z,z<(currentRows visits[j].task).length→
   s.natHeap (T+ordinal R visits[j]+z)=some (requestPrefix visits[j] z)

lemma value_eq (visits:List Visit)(k:ℕ)(hk:k<visits.length)
 (parent:k=0∨visits[k].task.parent<k):
 UniformCacheTimingNodeBody.value visits[k] (processedSuffix visits (k+1) k)=processedSuffix visits k k:=by
 rw [processedSuffix_step visits k hk,bottomStep_self k visits[k] (processedSuffix visits (k+1)) parent]
 unfold UniformCacheTimingNodeBody.value correction
 rw [UniformCacheTimingPrefix.amounts_eq]
lemma ticks_nil : ( ([]:List Visit).map UniformCacheTimingNode.budget).sum=0:=rfl

def ticks (visits:List Visit)(i:ℕ):ℕ:=((visits.take i).map UniformCacheTimingNode.budget).sum+1
lemma ticks_zero (visits:List Visit):ticks visits 0=1:=by simp [ticks]
lemma ticks_succ (visits:List Visit)(k:ℕ)(hk:k<visits.length):
 ticks visits (k+1)=UniformCacheTimingNode.budget visits[k]+ticks visits k:=by
 rw [ticks,ticks,List.take_succ_eq_append_getElem hk,List.map_append,List.sum_append]
 simp only [List.map_singleton,List.sum_singleton]
 omega
end
end ExactFourierCircuits.UniformCacheTimingReverseData
