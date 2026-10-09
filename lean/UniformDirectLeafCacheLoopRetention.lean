import UniformDirectLeafCacheLoopProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopRetention
open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheExecution
noncomputable section

/-- Persistent prior slots survive from actual bank equalities; no cached
operator action is assumed. All current-cache writes are outside these ranges. -/
def result {c:Config} {r B:ℕ} {q:UniformTransposeDescriptorMachine.Record} {mu:ℂ}
 {positive:2≤r} {s u:State} (res:Result c r q mu positive s) (layout:Layout c r B)
 (dest:q.dest<r) (source:q.source<r)
 (scalar:∀j,c.pool≤j→j<c.pool+9*r→u.scalarHeap j=s.scalarHeap j)
 (nat:∀j,c.permutation≤j→j<c.entry+7→u.natHeap j=s.natHeap j) :
 Result c r q mu positive u := by
 have p:=layout.permutation
 have w:=layout.widths
 have m:=layout.markers
 have a:=layout.axis
 refine ⟨res.count,res.kind,res.edges,res.matching,res.inRange,res.count_eq,res.kind_eq,?_,?_,?_,?_,?_,?_⟩
 · rcases res.entry with ⟨h0,h1,h2,h3,h4,h5,h6⟩
   exact ⟨(nat _ (by omega) (by omega)).trans h0,(nat _ (by omega) (by omega)).trans h1,
    (nat _ (by omega) (by omega)).trans h2,(nat _ (by omega) (by omega)).trans h3,
    (nat _ (by omega) (by omega)).trans h4,(nat _ (by omega) (by omega)).trans h5,
    (nat _ (by omega) (by omega)).trans h6⟩
 · rcases res.rows with ⟨h0,h1,h2,h3,_⟩
   exact ⟨(nat _ (by omega) (by omega)).trans h0,(nat _ (by omega) (by omega)).trans h1,
    (nat _ (by omega) (by omega)).trans h2,(nat _ (by omega) (by omega)).trans h3,trivial⟩
 · intro axis member j
   have eq:axis=UniformMatchingAxisTableMachine.physicalAxis r c.widths c.permutation res.edges
    res.matching res.inRange positive:=by simpa only[List.mem_singleton] using member
   subst axis
   have jl:=j.isLt
   change j.val<(UniformMatchingAxisTableMachine.widths r res.count).length at jl
   rw[UniformMatchingAxisTableMachine.widths_length r res.count
    (UniformMatchingAxisTableMachine.matching_capacity r res.edges res.matching res.inRange)] at jl
   rw[nat _ (by change c.permutation≤c.widths+j.val;omega)
    (by change c.widths+j.val<c.entry+7;omega)]
   exact res.widths _ (by simp) j
 · intro axis member j
   have eq:axis=UniformMatchingAxisTableMachine.physicalAxis r c.widths c.permutation res.edges
    res.matching res.inRange positive:=by simpa only[List.mem_singleton] using member
   subst axis
   have jl:=j.isLt
   change j.val<(UniformMatchingAxisTableMachine.widths r res.count).sum at jl
   rw[UniformMatchingAxisTableMachine.widths_sum r res.count
    (UniformMatchingAxisTableMachine.matching_capacity r res.edges res.matching res.inRange)] at jl
   rw[nat _ (by change c.permutation≤c.permutation+j.val;omega)
    (by change c.permutation+j.val<c.entry+7;omega)]
   exact res.permutations _ (by simp) j
 · intro kind lane j
   have ll:=lane.isLt
   have jl:=j.isLt
   rw[scalar _ (by omega) (by nlinarith)]
   exact res.scale kind lane j
 · intro kind lane side
   have bounds:=UniformGlobalMatchingPoolPreparation.address_bound c.pool r q.dest q.source dest source lane side
   rw[scalar _ bounds.1 bounds.2]
   exact res.shear kind lane side
end
end ExactFourierCircuits.UniformDirectLeafCacheLoopRetention
