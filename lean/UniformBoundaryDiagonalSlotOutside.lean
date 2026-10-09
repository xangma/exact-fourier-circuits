import UniformBoundarySlotDirectoryOutside
import UniformBoundaryDiagonalExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalOutside
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)
open UniformBoundaryDiagonalMachine
noncomputable section

lemma slot_execution_outside {n B seed r lane time pool arena:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Working seed r lane time pool arena s)(positive:2≤r)(natFit:arena+3*r+11≤B)
 (code:127≤B)(pc:s.pc=34)(wb:WordBound B s):∃u,
 BoundedExecution program n x B s (17*r+59) u ∧u.pc=126 ∧
 UniformLocalMatchingSlotDirectory.Entry (arena+3*r+4) time r pool r (arena+r) arena 1 u ∧
 UniformSectorPackingMachine.Rows [axis r arena positive] 0 (arena+3*r) u ∧
 UniformSectorPackingMachine.Widths [axis r arena positive] u ∧
 UniformSectorPackingMachine.Permutations [axis r arena positive] u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,(j<arena∨arena+3*r+11≤j)→u.natHeap j=s.natHeap j) ∧FinalHeaders r arena u:=by
 have timeBound:time≤B:=by rw[←h.time];exact wb.2.1 5920
 have poolBound:pool≤B:=by rw[←h.pool];exact wb.2.1 6020
 let a:=applyBlock slotSetup s
 have boot:BoundedRuns program n x B s 12 a:=by
  have run:=block_runs slotSetup program 34 n B x s slotSetup_code pc wb
   (by rw[slotSetup_length];omega) (by simp[slotSetup,readable,Op.readable])
   (by simp[slotSetup,peak,Op.peak,Op.apply,writeNat,next,h.radix,h.zero,h.pool,h.arena,h.time];omega)
  simpa only[slotSetup_length] using run
 have ap:a.pc=46:=by rw[applyBlock_pc,pc,slotSetup_length]
 have ah:=slot_setup_working h
 have heaps:=slot_setup_heaps s
 let ready:=setPC a 0
 have args:UniformLocalMatchingSlotDirectory.Args time r pool arena (arena+r) (arena+2*r)
  (arena+3*r) arena (arena+3*r+4) 1 0 ready:=by
  constructor <;>simp[ready,a,slotSetup,setPC,applyBlock,Op.apply,writeNat,next,h.radix,h.zero,h.pool,h.arena,h.time]
  all_goals omega
 obtain ⟨z,run,_cost,zp,entry,row,widths,permutation,heap,registers,outputs,roots,natPrefix⟩:=
  UniformBoundarySlotDirectoryOutside.execution_outside x emptyEdges ready args (by intro i;exact Fin.elim0 i)
   empty_matching (empty_range r) positive (by omega) (by omega) (by omega) (by omega)
   (by omega) natFit (by omega) rfl (changePC_bound B a 0 boot.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed slot_code
  (by rw[UniformLocalMatchingSlotDirectory.program_length];omega) (by omega) run
 rw[show placed 46 ready=a by change {a with pc:=46}=a;rw[←ap]] at moved
 let u:=setPC z 126
 change BoundedRuns program n x B a (UniformMatchingAxisTableMachine.runtime r 0+25) u at moved
 have stop:BoundedExecution program n x B u 1 u:=.halt moved.final_bound (by simp[step,u,setPC,halt_at])
 refine ⟨u,?_,rfl,?_,?_,?_,?_,heap.trans heaps.2.1,registers.trans heaps.2.2.1,
  outputs.trans heaps.2.2.2.1,roots.trans heaps.2.2.2.2,?_,?_⟩
 · convert boot.executes (moved.executes stop) using 1
   simp only[UniformMatchingAxisTableMachine.runtime];omega
 · simpa only[u,setPC,UniformLocalMatchingSlotDirectory.Entry,Nat.sub_zero] using entry
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Rows] using row
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Widths] using widths
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Permutations] using permutation
 · intro j hj
   exact (natPrefix j (by omega)).trans (congrFun heaps.1 j)
 · exact ⟨(slot_kept run 7007 (Or.inl (by omega))).trans ah.radix,
    (slot_kept run 7002 (Or.inl (by omega))).trans ah.zero,
    (slot_kept run 7003 (Or.inl (by omega))).trans ah.one,
    (slot_kept run 5848 (Or.inr ⟨by omega,by omega⟩)).trans args.directory⟩

end
end ExactFourierCircuits.UniformBoundaryDiagonalOutside
