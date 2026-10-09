import UniformLocalCacheSlotCursorMachine
import UniformLocalFactorDispatchResult
import UniformProducedMatchingSlotDirectory

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace C
abbrev boot:=UniformLocalCacheSlotCursorMachine.boot
abbrev advance:=UniformLocalCacheSlotCursorMachine.advance
end C
namespace H
abbrev program:=UniformLocalCacheSlotHeaderMachine.program
end H
namespace F
abbrev program:=UniformLocalFactorDispatchMachine.program
end F
namespace D
abbrev program:=UniformLocalMatchingSlotDirectory.program
end D

/-- The same fixed code is used at every stored slot. The measured factor row
count feeds the real80-op partition/ABI producer before the cursor advances. -/
def beforeHeader:Program:=C.boot.map Op.code++[.branchLT 6140 6141 15 1335]
def beforeFactors:Program:=beforeHeader++H.program.map (relocate 15 89)
def beforeDirectory:Program:=beforeFactors++F.program.map (relocate 89 1245)
def beforeAdvance:Program:=beforeDirectory++D.program.map (relocate 1245 1325)
def program:Program:=beforeAdvance++C.advance.map Op.code++[.jump 14,.halt]
lemma beforeHeader_length:beforeHeader.length=15:=by
 simp [beforeHeader,C.boot,UniformLocalCacheSlotCursorMachine.boot_length]
lemma beforeFactors_length:beforeFactors.length=89:=by
 simp [beforeFactors,beforeHeader_length,H.program,UniformLocalCacheSlotHeaderMachine.program_length]
lemma beforeDirectory_length:beforeDirectory.length=1245:=by
 simp [beforeDirectory,beforeFactors_length,F.program,UniformLocalFactorDispatchMachine.program_length]
lemma beforeAdvance_length:beforeAdvance.length=1325:=by
 simp [beforeAdvance,beforeDirectory_length,D.program,UniformLocalMatchingSlotDirectory.program_length]
lemma program_length:program.length=1336:=by
 simp [program,beforeAdvance_length,C.advance,UniformLocalCacheSlotCursorMachine.advance_length]

section Code
attribute [local irreducible] UniformLocalCacheSlotHeaderMachine.program
 UniformLocalFactorDispatchMachine.program UniformLocalMatchingSlotDirectory.program
lemma boot_code:BlockAt C.boot program 0:=by
 intro i hi;change i<14 at hi;interval_cases i <;>rfl
lemma outer_at:program[14]?=some (.branchLT 6140 6141 15 1335):=rfl
lemma header_code:CodeAt H.program program 15 89:=by
 let rest:=F.program.map (relocate 89 1245)++D.program.map (relocate 1245 1325)++
  C.advance.map Op.code++[.jump 14,.halt]
 have eq:program=beforeHeader++H.program.map (relocate 15 89)++rest:=by
  simp only [program,beforeAdvance,beforeDirectory,beforeFactors,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeHeader rest _ 15 89 beforeHeader_length
lemma factor_code:CodeAt F.program program 89 1245:=by
 let rest:=D.program.map (relocate 1245 1325)++C.advance.map Op.code++[.jump 14,.halt]
 have eq:program=beforeFactors++F.program.map (relocate 89 1245)++rest:=by
  simp only [program,beforeAdvance,beforeDirectory,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeFactors rest _ 89 1245 beforeFactors_length
lemma directory_code:CodeAt D.program program 1245 1325:=by
 have eq:program=beforeDirectory++D.program.map (relocate 1245 1325)++
  (C.advance.map Op.code++[.jump 14,.halt]):=by
  simp only [program,beforeAdvance,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeDirectory _ _ 1245 1325 beforeDirectory_length
lemma advance_code:BlockAt C.advance program 1325:=
 UniformRankCrossPreparationMachine.block_of_segment C.advance beforeAdvance [.jump 14,.halt] 1325 beforeAdvance_length
lemma jump_at:program[1334]?=some (.jump 14):=by
 rw [program,List.getElem?_append_right (by
  simp only [List.length_append,List.length_map,beforeAdvance_length,C.advance,
   UniformLocalCacheSlotCursorMachine.advance_length];omega)]
 simp only [List.length_append,List.length_map,beforeAdvance_length,C.advance,
  UniformLocalCacheSlotCursorMachine.advance_length];rfl
lemma halt_at:program[1335]?=some .halt:=by
 rw [program,List.getElem?_append_right (by
  simp only [List.length_append,List.length_map,beforeAdvance_length,C.advance,
   UniformLocalCacheSlotCursorMachine.advance_length];omega)]
 simp only [List.length_append,List.length_map,beforeAdvance_length,C.advance,
  UniformLocalCacheSlotCursorMachine.advance_length];rfl
end Code

noncomputable section
open UniformLocalFactorDispatchMachine

/-- The real dispatched rows determine their geometry, including inverse
occurrence reversal and signed broadcast leaves. No matching premise is read. -/
lemma dispatched_geometry {B:ℕ} (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (q:UniformLocalRectangleDescriptors.Row) (slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (UniformLocalCacheSlotHeaderMachine.forward c q slot) B)
 (bl:BroadcastLayout c q B) (ha he):
 UniformGlobalMatchingPoolPreparation.Bounds c.ambient (printedRows c q slot l bl ha he) ∧
 UniformGlobalMatchingPoolPreparation.Different (printedRows c q slot l bl ha he) ∧
 UniformGlobalMatchingPoolPreparation.Matching (printedRows c q slot l bl ha he) := by
 cases b:slot.broadcast with
 | true=>
  simp only [printedRows,b,ite_true]
  exact ⟨UniformLocalBroadcastPoolMachine.bounds q slot c.gates c.height.P c.ambient
    bl.capacity bl.outputCount bl.targetRange l.extent,
   UniformLocalBroadcastPoolMachine.different q slot c.gates c.height.P bl.capacity bl.outputCount,
   UniformLocalBroadcastPoolMachine.matching q slot c.gates c.height.P bl.capacity bl.outputCount⟩
 | false=>
  cases i:slot.inverse with
  | false=>
   simp only [printedRows,b,i,Bool.false_eq_true,ite_false]
   exact UniformForwardMatchingFactorPreparation.rows_geometry _ l ha he
  | true=>
   simp only [printedRows,b,i,Bool.false_eq_true,ite_false,ite_true]
   exact UniformInverseMatchingFactorPreparation.rows_geometry _ l ha he

namespace Cursor
abbrev Parameters:=UniformLocalCacheSlotHeaderMachine.Parameters
abbrev Control:=UniformLocalCacheSlotCursorMachine.Control
abbrev shifted:=UniformLocalCacheSlotCursorMachine.cursorParameters
end Cursor

/-- Fourteen actual instructions initialize every loop stride and the count. -/
theorem boot_execution {B n:ℕ} (c:Cursor.Parameters) (x:Fin n→ℂ) (s:State)
 (args:UniformLocalCacheSlotHeaderMachine.Args c s) (pc:s.pc=0) (wb:WordBound B s)
 (code:1336≤B) (total:352*c.height.K+330≤B) (scalar:9*c.ambient≤B)
 (natural:3*c.ambient+11≤B):∃u,
 BoundedRuns program n x B s 14 u ∧u.pc=14 ∧Cursor.Control c 0 u ∧
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.natReg 6200=s.natReg 6200:=by
 have safe:=UniformLocalCacheSlotCursorMachine.boot_safe args (by omega) total scalar natural
 have run:=block_runs C.boot program 0 n B x s boot_code pc wb
  (by rw [C.boot,UniformLocalCacheSlotCursorMachine.boot_length];omega) safe.1 safe.2
 let u:=applyBlock C.boot s
 have up:u.pc=14:=by rw [applyBlock_pc,pc,C.boot,UniformLocalCacheSlotCursorMachine.boot_length]
 refine ⟨u,?_,up,UniformLocalCacheSlotCursorMachine.boot_control args,?_,?_,?_,?_,?_,?_⟩
 · simpa only [C.boot,UniformLocalCacheSlotCursorMachine.boot_length] using run
 all_goals rfl

/-- The loop condition is tested on its computed count, never on host control. -/
lemma enter {B n j:ℕ}{c:Cursor.Parameters}{x:Fin n→ℂ}{s:State}
 (h:Cursor.Control c j s) (more:j<352*c.height.K+330) (pc:s.pc=14)
 (wb:WordBound B s) (code:1336≤B):
 BoundedRuns program n x B s 1 (setPC s 15):=by
 have bound:=changePC_bound B s 15 wb (by omega)
 exact .next wb (by simp [step,pc,outer_at,h.index,h.total,more,setPC]) (.refl bound)

/-- Nine cursor updates and the literal back-edge are both charged. -/
theorem advance_execution {B n j:ℕ} (c:Cursor.Parameters) (x:Fin n→ℂ) (s:State)
 (h:Cursor.Control c j s) (pc:s.pc=1325) (wb:WordBound B s) (code:1336≤B)
 (slot:(Cursor.shifted c (j+1)).slot≤B)
 (pool:(Cursor.shifted c (j+1)).pool≤B)
 (time:(Cursor.shifted c (j+1)).time≤B)
 (permutation:(Cursor.shifted c (j+1)).cachePermutation≤B)
 (widths:(Cursor.shifted c (j+1)).cacheWidths≤B)
 (markers:(Cursor.shifted c (j+1)).cacheMarkers≤B)
 (axis:(Cursor.shifted c (j+1)).cacheAxis≤B)
 (directory:(Cursor.shifted c (j+1)).cacheDirectory≤B) (index:j+1≤B):∃u,
 BoundedRuns program n x B s 10 u ∧u.pc=14 ∧Cursor.Control c (j+1) u ∧
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.natReg 6200=s.natReg 6200:=by
 have safe:=UniformLocalCacheSlotCursorMachine.advance_safe h slot pool time permutation widths markers axis directory index
 have run:=block_runs C.advance program 1325 n B x s advance_code pc wb
  (by rw [C.advance,UniformLocalCacheSlotCursorMachine.advance_length];omega) safe.1 safe.2
 let a:=applyBlock C.advance s
 have ap:a.pc=1334:=by rw [applyBlock_pc,pc,C.advance,UniformLocalCacheSlotCursorMachine.advance_length]
 let u:=setPC a 14
 have bound:=changePC_bound B a 14 run.final_bound (by omega)
 have back:BoundedRuns program n x B a 1 u:=.next run.final_bound
  (by simp [step,ap,jump_at,u,setPC]) (.refl bound)
 refine ⟨u,?_,rfl,(UniformLocalCacheSlotCursorMachine.advance_control h).withPC 14,?_,?_,?_,?_,?_,?_⟩
 · simpa only [C.advance,UniformLocalCacheSlotCursorMachine.advance_length] using run.trans back
 all_goals rfl

lemma stop {B n:ℕ}{c:Cursor.Parameters}{x:Fin n→ℂ}{s:State}
 (h:Cursor.Control c (352*c.height.K+330) s) (pc:s.pc=14)
 (wb:WordBound B s) (code:1336≤B):
 BoundedExecution program n x B s 2 (setPC s 1335):=by
 have bound:=changePC_bound B s 1335 wb (by omega)
 have done:BoundedExecution program n x B (setPC s 1335) 1 (setPC s 1335):=
  .halt bound (by simp [step,setPC,halt_at])
 exact .next wb (by simp [step,pc,outer_at,h.index,h.total,setPC]) done

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
