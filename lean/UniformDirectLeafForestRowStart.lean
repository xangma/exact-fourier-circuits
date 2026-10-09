import UniformDirectLeafForestState
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestRowStart
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformLocalCacheTreeMachine
noncomputable section

def state(s:State):State:=UniformDirectLeafForestRead.result (setPC s 32)
lemma header {p:Parameters}{visits:List Visit}{i n:ℕ}{s:State}
 (hi:i<visits.length)(h:Cursor p visits i s)(src:Sources p visits n s):
 ReadCursor p visits i visits[i] (state s):=
 UniformDirectLeafForestRead.cursor (h.withPC 32) (src.nodes i hi) (src.starts i hi)
lemma heap(s:State):(state s).natHeap=s.natHeap ∧(state s).scalarHeap=s.scalarHeap ∧
 (state s).outputs=s.outputs ∧(state s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma sources {p:Parameters}{visits:List Visit}{n:ℕ}{s:State}(h:Sources p visits n s):
 Sources p visits n (state s):=by
 refine ⟨UniformDirectLeafForestLeafCall.original_transport h.original rfl rfl,
  UniformDirectLeafForestLeafCall.conjugate_transport h.conjugate rfl rfl,
  UniformDirectLeafForestLeafCall.constants_transport h.constants rfl,?_,?_⟩
 · exact h.nodes
 · exact h.starts
lemma pc(s:State):(state s).pc=37:=rfl

theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}
 (x:Fin n→ℂ)(s:State)(hi:i<visits.length)(h:Cursor p visits i s)(src:Sources p visits n s)
 (code:461≤B)(pc:s.pc=31)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 6 (state s):=by
 have bound:=changePC_bound B s 32 wb (by omega)
 have branch:BoundedRuns UniformDirectLeafForestProgram.program n x B s 1 (setPC s 32):=
  .next wb (by simp[UniformMachine.step,pc,UniformDirectLeafForestProgram.branch_at,h.index,h.count,hi,setPC])
   (.refl bound)
 have run:=UniformDirectLeafForestRead.execution x (setPC s 32) (h.withPC 32)
  (src.nodes i hi) (src.starts i hi) code rfl bound
 exact branch.trans run
end
end ExactFourierCircuits.UniformDirectLeafForestRowStart
