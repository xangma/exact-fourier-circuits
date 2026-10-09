import UniformMatchingSlotHeapRetention
import UniformProducedMatchingSlotDirectory
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedMatchingSlotDirectory
open UniformMachine
noncomputable section

/-- The suffix frame concerns the same actual80 execution. Determinism links
the strengthened producer proof to its existing physical output contract. -/
lemma Produced.high {time r pool P W U A T D kind B n:ℕ} (x:Fin n→ℂ) (s u:State)
 (rows:List UniformInPlaceMachine.Row) (positive:2≤r)
 (bounds:UniformGlobalMatchingPoolPreparation.Bounds r rows)
 (diff:UniformGlobalMatchingPoolPreparation.Different rows)
 (matching:UniformGlobalMatchingPoolPreparation.Matching rows)
 (args:UniformLocalMatchingSlotDirectory.Args time r pool P W U A T D kind rows.length s)
 (table:UniformCrossShearTableMachine.Table T rows s)
 (hT:T+3*rows.length≤P) (hP:P+r≤W) (hW:W+r≤U) (hU:U+r≤A)
 (hA:A+4≤D) (hD:D+7≤B) (code:80≤B) (pc:s.pc=0) (wb:WordBound B s)
 (post:Produced B n time r pool P W A D kind x s u rows
  (rowAxis r W P rows positive bounds diff matching)):
 ∀q,D+7≤q→u.natHeap q=s.natHeap q:=by
 obtain ⟨v,run,_cheap,_pc,_entry,_row,_widths,_perm,_heap,_regs,_out,_roots,_low,high⟩:=
  UniformMatchingSlotHeapRetention.execution x
   (UniformGlobalMatchingScaleBankBridge.rowEdges rows diff) s args (edges_of_table diff table)
   (UniformGlobalMatchingScaleBankBridge.rowEdges_matching rows diff matching)
   (UniformGlobalMatchingScaleBankBridge.rowEdges_range r rows diff bounds) positive
   hT hP hW hU hA hD code pc wb
 have eq:u=v:=(post.execution.executes.deterministic run.executes).2
 simpa only[eq] using high

end
end ExactFourierCircuits.UniformProducedMatchingSlotDirectory
