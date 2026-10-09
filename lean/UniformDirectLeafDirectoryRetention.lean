import UniformMatchingSlotDirectoryFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalMatchingSlotDirectory
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformMatchingAxisTableMachine (physicalAxis)
noncomputable section
lemma publish_high {time r pool P W A D kind M : ℕ} {s:State}
 (h:PublishReady time r pool P W A D kind M s) (q:ℕ) (hq:D+7≤q) :
 (applyBlock publish s).natHeap q=s.natHeap q := by
 simp (disch:=omega) [publish,applyBlock,Op.apply,writeNat,next,Function.update,h.axis,h.directory,h.zero,h.one]
 split_ifs <;>first |omega |rfl
theorem execution_high {time r pool P W U A T D kind M B n : ℕ} (x:Fin n→ℂ)
 (E:Fin M→UniformColoring.Edge) (s:State) (args:Args time r pool P W U A T D kind M s)
 (src:UniformMatchingAxisTableMachine.Edges E T s)
 (hm:UniformMatchingAxisTableMachine.Matching E) (hr:UniformMatchingAxisTableMachine.InRange r E)
 (positive:2≤r) (hT:T+3*M≤P) (hP:P+r≤W) (hW:W+r≤U) (hU:U+r≤A)
 (hA:A+4≤D) (hD:D+7≤B) (code:80≤B) (pc:s.pc=0) (wb:WordBound B s) : ∃u,
 BoundedExecution program n x B s (UniformMatchingAxisTableMachine.runtime r M+25) u ∧
 UniformMatchingAxisTableMachine.runtime r M+25≤21*r+46 ∧u.pc=79 ∧
 Entry D time r pool (r-M) W P kind u ∧
 UniformSectorPackingMachine.Rows [physicalAxis r W P E hm hr positive] 0 A u ∧
 UniformSectorPackingMachine.Widths [physicalAxis r W P E hm hr positive] u ∧
 UniformSectorPackingMachine.Permutations [physicalAxis r W P E hm hr positive] u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q<P→u.natHeap q=s.natHeap q) ∧
 (∀q,D+7≤q→u.natHeap q=s.natHeap q) := by
 have safe:=setup_safe wb code
 have boot:=block_runs setup program 0 n B x s setup_code pc wb
  (by rw[setup_length];omega) safe.1 safe.2
 let b:=applyBlock setup s
 have bp:b.pc=9:=by rw[applyBlock_pc,pc,setup_length]
 let ready:=setPC b 0
 have rb:=changePC_bound B b 0 boot.final_bound (by omega)
 have head:=setup_header args
 have readyHeader:UniformMatchingAxisTableMachine.Header r M T P W U A ready:=
  ⟨head.radix,head.count,head.source,head.permutation,head.widths,head.markers,head.row⟩
 have rs:UniformMatchingAxisTableMachine.Edges E T ready:=src
 obtain ⟨v,run,vp,vh,perm,widths,_markers,row,_edges,out,frame⟩:=
  UniformMatchingAxisTableMachine.execution r M T P W U A B n x E ready readyHeader rfl rs hm hr
   hT hP hW hU (by omega) (by omega) rb
 have relocated:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw[UniformMatchingAxisTableMachine.program_length];omega) (by omega) run
 rw[show placed 9 ready=b by change {b with pc:=9}=b;rw[←bp]] at relocated
 let printState:=setPC v 64
 have kept (q:ℕ) (lo:5840≤q) (hi:q≤5849):printState.natReg q=s.natReg q:=
  (frame.2.2.2.2 q (Or.inr (by omega))).trans (setup_nat s q (Or.inr (by omega)) (by omega) (by omega))
 have printing:PublishReady time r pool P W A D kind M printState:=by
  refine ⟨(kept 5840 (by omega) (by omega)).trans args.time,
   (kept 5841 (by omega) (by omega)).trans args.radix,
   (kept 5842 (by omega) (by omega)).trans args.pool,
   (kept 5843 (by omega) (by omega)).trans args.permutation,
   (kept 5844 (by omega) (by omega)).trans args.widths,vh.row,
   (kept 5848 (by omega) (by omega)).trans args.directory,
   (kept 5849 (by omega) (by omega)).trans args.kind,?_,?_,row.1⟩
  · exact (frame.2.2.2.2 5850 (Or.inr (by omega))).trans (by simp[ready,b,setPC,setup,applyBlock,Op.apply,writeNat,UniformMachine.next])
  · exact (frame.2.2.2.2 5853 (Or.inr (by omega))).trans (by simp[ready,b,setPC,setup,applyBlock,Op.apply,writeNat,UniformMachine.next])
 have safety:=publish_safe printing relocated.final_bound hD
 have printed:=block_runs publish program 64 n B x printState publish_code rfl relocated.final_bound
  (by rw[publish_length];omega) safety.1 safety.2
 let z:=applyBlock publish printState
 have zp:z.pc=79:=by rw[applyBlock_pc,publish_length];rfl
 have done:BoundedExecution program n x B z 1 z:=.halt printed.final_bound
  (by simp[step,zp,halt_at])
 have pBank:UniformMatchingAxisTableMachine.Bank P (UniformMatchingAxisTableMachine.ordered r E) z:=by
  intro j hj
  rw[publish_low printing (P+j) (by
   rw[UniformMatchingAxisTableMachine.ordered_length r E hm hr] at hj;omega)]
  exact perm j hj
 have wBank:UniformMatchingAxisTableMachine.Bank W (UniformMatchingAxisTableMachine.widths r M) z:=by
  intro j hj
  have len:=UniformMatchingAxisTableMachine.widths_length r M (UniformMatchingAxisTableMachine.matching_capacity r E hm hr)
  rw[publish_low printing (W+j) (by rw[len] at hj;omega)]
  exact widths j hj
 have aRow:UniformMatchingAxisTableMachine.AxisRow A r M W P z:=by
  unfold UniformMatchingAxisTableMachine.AxisRow
  rw[publish_low printing A (by omega),publish_low printing (A+1) (by omega),
   publish_low printing (A+2) (by omega),publish_low printing (A+3) (by omega)]
  exact row
 obtain ⟨rows',widths',perm'⟩:=UniformMatchingAxisTableMachine.physical_axis E z hm hr positive aRow pBank wBank
 refine ⟨z,?_,?_,zp,publish_entry printing,rows',widths',perm',?_,?_,?_,?_,?_,?_⟩
 · convert boot.executes (relocated.executes (printed.executes done)) using 1
   simp only[setup_length,publish_length]
   omega
 · have:=UniformMatchingAxisTableMachine.runtime_linear r M (UniformMatchingAxisTableMachine.matching_capacity r E hm hr)
   omega
 · exact (publish_heaps printState).1.trans frame.1
 · exact (publish_heaps printState).2.1.trans frame.2.1
 · exact (publish_heaps printState).2.2.1.trans frame.2.2.1
 · exact (publish_heaps printState).2.2.2.trans frame.2.2.2.1
 · intro q hq
   exact (publish_low printing q (by omega)).trans (out q (Or.inl hq) (Or.inl (by omega))
    (Or.inl (by omega)) (Or.inl (by omega)))

 · intro q hq
   exact (publish_high printing q hq).trans (out q (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)))

end
end ExactFourierCircuits.UniformLocalMatchingSlotDirectory
