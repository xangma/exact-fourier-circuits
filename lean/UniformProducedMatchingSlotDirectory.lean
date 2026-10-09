import UniformLocalMatchingSlotDirectory
import UniformForwardMatchingFactorTensorBridge
import UniformLocalBroadcastPoolMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedMatchingSlotDirectory
open UniformMachine
namespace F
abbrev Config:=UniformForwardMatchingFactorPreparation.Config
end F
namespace L
abbrev Row:=UniformLocalRectangleDescriptors.Row
abbrev Slot:=UniformLocalCacheChronology.Slot
end L
noncomputable section

lemma edges_of_table {T:ℕ} {rows:List UniformInPlaceMachine.Row} {s:State}
 (diff:UniformGlobalMatchingPoolPreparation.Different rows)
 (table:UniformCrossShearTableMachine.Table T rows s) :
 UniformMatchingAxisTableMachine.Edges (UniformGlobalMatchingScaleBankBridge.rowEdges rows diff) T s := by
 intro j
 exact ⟨(table j.val j.isLt).1,(table j.val j.isLt).2.1⟩

def rowAxis (r W P:ℕ) (rows:List UniformInPlaceMachine.Row)
 (positive:2≤r) (bounds:UniformGlobalMatchingPoolPreparation.Bounds r rows)
 (diff:UniformGlobalMatchingPoolPreparation.Different rows)
 (matching:UniformGlobalMatchingPoolPreparation.Matching rows) : UniformSectorPackingMachine.PhysicalAxis :=
 UniformMatchingAxisTableMachine.physicalAxis r W P
  (UniformGlobalMatchingScaleBankBridge.rowEdges rows diff)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_matching rows diff matching)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_range r rows diff bounds) positive

/-- Runtime result of the actual80-op producer adapter. The row geometry comes
from the actual typed producer, never from a separate matching hypothesis. -/
structure Produced (B n time r pool P W A D kind:ℕ) (x:Fin n→ℂ) (s u:State)
 (rows:List UniformInPlaceMachine.Row) (axis:UniformSectorPackingMachine.PhysicalAxis) : Prop where
 execution:BoundedExecution UniformLocalMatchingSlotDirectory.program n x B s
  (UniformMatchingAxisTableMachine.runtime r rows.length+25) u
 ticks:UniformMatchingAxisTableMachine.runtime r rows.length+25≤21*r+46
 pc:u.pc=79
 entry:UniformLocalMatchingSlotDirectory.Entry D time r pool (r-rows.length) W P kind u
 row:UniformSectorPackingMachine.Rows [axis] 0 A u
 widths:UniformSectorPackingMachine.Widths [axis] u
 permutation:UniformSectorPackingMachine.Permutations [axis] u
 heap:u.scalarHeap=s.scalarHeap
 registers:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 prefixHeap:∀q,q<P→u.natHeap q=s.natHeap q

lemma from_rows {time r pool P W U A T D kind B n:ℕ} (x:Fin n→ℂ) (s:State)
 (rows:List UniformInPlaceMachine.Row) (positive:2≤r)
 (bounds:UniformGlobalMatchingPoolPreparation.Bounds r rows)
 (diff:UniformGlobalMatchingPoolPreparation.Different rows)
 (matching:UniformGlobalMatchingPoolPreparation.Matching rows)
 (args:UniformLocalMatchingSlotDirectory.Args time r pool P W U A T D kind rows.length s)
 (table:UniformCrossShearTableMachine.Table T rows s)
 (hT:T+3*rows.length≤P) (hP:P+r≤W) (hW:W+r≤U) (hU:U+r≤A)
 (hA:A+4≤D) (hD:D+7≤B) (code:80≤B) (pc:s.pc=0) (wb:WordBound B s) :∃u,
 Produced B n time r pool P W A D kind x s u rows (rowAxis r W P rows positive bounds diff matching) := by
 obtain ⟨u,run,cost,up,entry,row,widths,perm,heap,regs,outputs,roots,prefixHeap⟩:=
  UniformLocalMatchingSlotDirectory.execution x (UniformGlobalMatchingScaleBankBridge.rowEdges rows diff) s args
   (edges_of_table diff table) (UniformGlobalMatchingScaleBankBridge.rowEdges_matching rows diff matching)
   (UniformGlobalMatchingScaleBankBridge.rowEdges_range r rows diff bounds) positive hT hP hW hU hA hD code pc wb
 exact ⟨u,run,cost,up,entry,row,widths,perm,heap,regs,outputs,roots,prefixHeap⟩

def forwardAxis {B:ℕ} (c:F.Config) (l:UniformForwardMatchingFactorPreparation.Layout c B)
 (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (P W:ℕ) (positive:2≤c.ambient) : UniformSectorPackingMachine.PhysicalAxis :=
 rowAxis c.ambient W P (UniformForwardMatchingFactorPreparation.rows c l ha he) positive
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).1
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).2.1
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).2.2

/-- After the real430 forward factor printer, its own selected rows determine
matching/range/different and its real9r pool determines every tensor diagonal.
The ordinary count894 is part of Args; its upstream supplement is tracked. -/
theorem forward {B n time P W U A D kind:ℕ} (c:F.Config)
 (l:UniformForwardMatchingFactorPreparation.Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)→ℂ)
 (x:Fin n→ℂ) (s0 s:State)
 (post:UniformForwardMatchingFactorPreparation.Result c l ha he bank s0 s)
 (positive:2≤c.ambient)
 (args:UniformLocalMatchingSlotDirectory.Args time c.ambient c.pool P W U A c.translated D kind
  (UniformForwardMatchingFactorPreparation.rows c l ha he).length s)
 (hT:c.translated+3*(UniformForwardMatchingFactorPreparation.rows c l ha he).length≤P)
 (hP:P+c.ambient≤W) (hW:W+c.ambient≤U) (hU:U+c.ambient≤A)
 (hA:A+4≤D) (hD:D+7≤B) (code:80≤B) (pc:s.pc=0) (wb:WordBound B s) :∃u,
 Produced B n time c.ambient c.pool P W A D kind x s u
  (UniformForwardMatchingFactorPreparation.rows c l ha he) (forwardAxis c l ha he P W positive) ∧
 UniformGlobalDiagonalRowsMachine.Pools [UniformForwardMatchingFactorPreparation.poolEntry c l ha he bank] u := by
 obtain ⟨u,done⟩:=from_rows x s (UniformForwardMatchingFactorPreparation.rows c l ha he) positive
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).1
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).2.1
  (UniformForwardMatchingFactorPreparation.rows_geometry c l ha he).2.2
  args post.table hT hP hW hU hA hD code pc wb
 refine ⟨u,done,?_⟩
 simpa only[UniformGlobalDiagonalRowsMachine.Pools,UniformTensorDiagonalBankMachine.Coefficients,done.heap]
  using post.tensor_pool

def broadcastAxis (q:L.Row) (slot:L.Slot) (g constants r W P:ℕ)
 (fit:g+q.e+q.a≤q.width) (ag:q.a≤g) (target:q.i0+q.a≤q.width)
 (extent:q.offset+q.width≤r) (positive:2≤r) : UniformSectorPackingMachine.PhysicalAxis :=
 rowAxis r W P (UniformLocalBroadcastPoolMachine.rows q slot g constants fit) positive
  (UniformLocalBroadcastPoolMachine.bounds q slot g constants r fit ag target extent)
  (UniformLocalBroadcastPoolMachine.different q slot g constants fit ag)
  (UniformLocalBroadcastPoolMachine.matching q slot g constants fit ag)

def broadcastPool (q:L.Row) (slot:L.Slot) (g constants r pool:ℕ)
 (fit:g+q.e+q.a≤q.width) (ag:q.a≤g) (positive:2≤r) : UniformGlobalDiagonalRowsMachine.Entry where
 radix:=r
 positive:=by omega
 pool:=pool
 value:=fun lane d=>UniformGlobalMatchingScaleBankBridge.nativeFactor
  (UniformGlobalMatchingScaleBankBridge.rowEdges (UniformLocalBroadcastPoolMachine.rows q slot g constants fit)
   (UniformLocalBroadcastPoolMachine.different q slot g constants fit ag))
  (fun _=>if slot.inverse then(-1:ℂ)else 1) lane d.val

/-- The241 producer's actual translated rows and actual signed factor bank feed
80 charged instructions; both inverse signs and empty colors are included. -/
theorem broadcast {R K B n time r pool P W U A T D kind:ℕ} (constants:ℕ)
 (q:L.Row) (slot:L.Slot) (g:ℕ) (fit:g+q.e+q.a≤q.width) (ag:q.a≤g)
 (target:q.i0+q.a≤q.width) (extent:q.offset+q.width≤r) (positive:2≤r)
 (bank:Fin R→ℂ) (x:Fin n→ℂ) (s:State)
 (args:UniformLocalMatchingSlotDirectory.Args time r pool P W U A T D kind (UniformLocalBroadcastPoolMachine.count q slot) s)
 (table:UniformCrossShearTableMachine.Table T (UniformLocalBroadcastPoolMachine.rows q slot g constants fit) s)
 (factors:UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r
  (UniformLocalBroadcastPoolMachine.rows q slot g constants fit) bank
  (UniformLocalBroadcastPoolMachine.coefficients q slot g constants fit)
  (UniformLocalBroadcastPoolMachine.rows q slot g constants fit).length s)
 (hT:T+3*(UniformLocalBroadcastPoolMachine.count q slot)≤P)
 (hP:P+r≤W) (hW:W+r≤U) (hU:U+r≤A)
 (hA:A+4≤D) (hD:D+7≤B) (code:80≤B) (pc:s.pc=0) (wb:WordBound B s) :∃u,
 Produced B n time r pool P W A D kind x s u (UniformLocalBroadcastPoolMachine.rows q slot g constants fit)
  (broadcastAxis q slot g constants r W P fit ag target extent positive) ∧
 UniformGlobalDiagonalRowsMachine.Pools [broadcastPool q slot g constants r pool fit ag positive] u := by
 obtain ⟨u,done⟩:=from_rows x s (UniformLocalBroadcastPoolMachine.rows q slot g constants fit) positive
  (UniformLocalBroadcastPoolMachine.bounds q slot g constants r fit ag target extent)
  (UniformLocalBroadcastPoolMachine.different q slot g constants fit ag)
  (UniformLocalBroadcastPoolMachine.matching q slot g constants fit ag)
  (by simpa only[UniformLocalBroadcastPoolMachine.rows_length] using args) table
  (by simpa only[UniformLocalBroadcastPoolMachine.rows_length] using hT) hP hW hU hA hD code pc wb
 refine ⟨u,done,?_⟩
 intro a member lane j
 have eq:a=broadcastPool q slot g constants r pool fit ag positive:=by simpa only[List.mem_singleton] using member
 subst a
 have real:=UniformGlobalMatchingScaleBankBridge.pool_coefficients
  (UniformLocalBroadcastPoolMachine.different q slot g constants fit ag)
  (UniformLocalBroadcastPoolMachine.matching q slot g constants fit ag) factors lane j
 simpa only[UniformTensorDiagonalBankMachine.Coefficients,done.heap,broadcastPool,
  UniformLocalBroadcastPoolMachine.coefficients,UniformLocalBroadcastPoolMachine.coefficient_value] using real

end
end ExactFourierCircuits.UniformProducedMatchingSlotDirectory
