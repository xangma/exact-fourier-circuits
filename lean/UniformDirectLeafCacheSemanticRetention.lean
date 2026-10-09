import UniformDirectLeafCacheSemanticExecution
import UniformDirectLeafCacheLoopRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheSemanticRetention
open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheExecution
open UniformDirectLeafCacheSemanticExecution
noncomputable section

/-- Persistent prior slots survive from actual bank equalities; no cached
operator action is assumed. All current-cache writes are outside these ranges. -/
def result {c:Config} {r B:ℕ} {q:UniformTransposeDescriptorMachine.Record} {mu:ℂ}
 {positive:2≤r} {s u:State} (res:SemanticResult c r q mu positive s) (layout:Layout c r B)
 (dest:q.dest<r) (source:q.source<r)
 (scalar:∀j,c.pool≤j→j<c.pool+9*r→u.scalarHeap j=s.scalarHeap j)
 (nat:∀j,c.permutation≤j→j<c.entry+7→u.natHeap j=s.natHeap j) :
 SemanticResult c r q mu positive u :=
 by
 refine ⟨UniformDirectLeafCacheLoopRetention.result res.toResult layout dest source scalar nat,res.endpoints,?_⟩
 intro kind lane i nd ne
 rw[scalar _ (by omega) (by have:=lane.isLt;have:=i.isLt;nlinarith)]
 exact res.unused kind lane i nd ne
end
end ExactFourierCircuits.UniformDirectLeafCacheSemanticRetention
