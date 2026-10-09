import UniformLocalRectanglePhaseBanks

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestCoverage
open UniformMachine UniformLocalRectangleDescriptors UniformLocalCacheTreeMachine
open UniformLocalCacheTreeCoverage UniformWorkspacePlanner

/-- Every balanced request has a real seven-cell source emitted by the DFS
printer. Neither a request list nor rectangle geometry is supplied to RAM. -/
lemma stored_request (visits:List Visit) (s:State)
 (tables:UniformLocalCacheTreeExecution.RequestTables visits s) (q:Row)
 (hq:q ∈ visitedRows visits) : ∃D,
 UniformLocalRectangleBankMachine.RowSource D q s ∧
 0<q.a ∧ 0<q.e ∧ q.i0+q.a ≤ q.width ∧ q.split<q.width ∧ q.split ≤ q.i0 ∧
 q.j0+q.e ≤ q.split ∧ gateCount q.a q.e+q.a+q.e ≤ q.width := by
 obtain ⟨L,hL,hq⟩:=List.mem_flatten.mp hq
 obtain ⟨visit,hvisit,rfl⟩:=List.mem_map.mp hL
 unfold currentRows at hq
 split_ifs at hq with bad
 · simp only [List.not_mem_nil] at hq
 · have big:2 ≤ visit.task.width:=by omega
   have fit:0<selected visit.task.width:=by omega
   have geom:=UniformLocalRectangleBankMachine.rows_geometry visit.task.width visit.task.offset q big fit hq
   unfold rows at hq
   obtain ⟨i,hi,hq⟩:=List.mem_flatMap.mp hq
   obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hq
   have hib:i<chunkCount (visit.task.width-visit.task.width/2) (selected visit.task.width):=
    List.mem_range.mp hi
   have hjb:j<chunkCount (visit.task.width/2) (selected visit.task.width):=List.mem_range.mp hj
   let D:=visit.rectangleBase+7*(i*chunkCount (visit.task.width/2) (selected visit.task.width)+j)
   refine ⟨D,?_,geom.1,geom.2.1,?_,?_,geom.2.2.2.2.1,geom.2.2.2.2.2.1,?_⟩
   · intro f
     exact table_row _ _ _ _ s (tables visit hvisit big fit) ⟨i,hib⟩ ⟨j,hjb⟩ f
   · exact geom.2.2.1
   · exact geom.2.2.2.1
   · exact geom.2.2.2.2.2.2.1

/-- Actual plan coverage, including ragged terminal chunks and both recursive
children, now feeds the stored-row physical producer interface directly. -/
lemma root_stored_request (v o R:ℕ) (s:State)
 (tables:UniformLocalCacheTreeExecution.RequestTables (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 s)
 (q:Row) (hq:q ∈ (ofPlan (UniformBalancedToeplitz.plan v) o).rectangles) : ∃D,
 UniformLocalRectangleBankMachine.RowSource D q s ∧
 0<q.a ∧ 0<q.e ∧ q.i0+q.a ≤ q.width ∧ q.split<q.width ∧ q.split ≤ q.i0 ∧
 q.j0+q.e ≤ q.split ∧ gateCount q.a q.e+q.a+q.e ≤ q.width := by
 apply stored_request _ s tables q
 rw [root_walk_rows]
 exact hq

end ExactFourierCircuits.UniformLocalStoredRequestCoverage
