import UniformGlobalMovementAssembly
import UniformMatchingAxisTableMachine
import UniformGlobalMatchingScaleBankBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalMatchingSlotDirectory
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformMatchingAxisTableMachine (physicalAxis)
noncomputable section

/-- Persistent arguments: time5840,radix5841,pool5842,permutation5843,
widths5844,markers5845,axis5846,actual3wordrows5847,ABI7base5848,kind5849.
The pair count is the real producer register894. No pair certificate is read. -/
structure Args (time r pool P W U A T D kind M : ℕ) (s : State) : Prop where
 time : s.natReg 5840=time
 radix : s.natReg 5841=r
 pool : s.natReg 5842=pool
 permutation : s.natReg 5843=P
 widths : s.natReg 5844=W
 markers : s.natReg 5845=U
 axis : s.natReg 5846=A
 rows : s.natReg 5847=T
 directory : s.natReg 5848=D
 kind : s.natReg 5849=kind
 count : s.natReg 894=M

def setup : List Op := [.literal 5850 0,.literal 5853 1,
 .add 840 5841 5850,.add 841 894 5850,.add 842 5847 5850,
 .add 843 5843 5850,.add 844 5844 5850,.add 845 5845 5850,.add 846 5846 5850]
def publish : List Op := [.getNat 5851 846,.add 5852 5848 5850,
 .putNat 5852 5840,.add 5852 5852 5853,.putNat 5852 5841,
 .add 5852 5852 5853,.putNat 5852 5842,.add 5852 5852 5853,.putNat 5852 5851,
 .add 5852 5852 5853,.putNat 5852 5844,.add 5852 5852 5853,.putNat 5852 5843,
 .add 5852 5852 5853,.putNat 5852 5849]
def program : Program := setup.map Op.code ++
 UniformMatchingAxisTableMachine.program.map (relocate 9 64) ++ publish.map Op.code ++ [.halt]
lemma setup_length : setup.length=9 := rfl
lemma publish_length : publish.length=15 := rfl
lemma program_length : program.length=80 := by
 simp only [program,List.length_append,List.length_map,setup_length,publish_length,
  UniformMatchingAxisTableMachine.program_length];rfl
lemma setup_code : BlockAt setup program 0 := by
 intro i hi;change i<9 at hi;interval_cases i <;>rfl
lemma matching_code : CodeAt UniformMatchingAxisTableMachine.program program 9 64 := by
 have h:=UniformRankCrossPreparationMachine.segment_code (setup.map Op.code)
  (publish.map Op.code++[.halt]) UniformMatchingAxisTableMachine.program 9 64
  (by rw[List.length_map,setup_length])
 simpa only [program,List.append_assoc] using h
lemma publish_code : BlockAt publish program 64 := by
 have h:=UniformRankCrossPreparationMachine.block_of_segment publish
  (setup.map Op.code++UniformMatchingAxisTableMachine.program.map (relocate 9 64)) [.halt] 64
  (by simp only[List.length_append,List.length_map,setup_length,UniformMatchingAxisTableMachine.program_length])
 simpa only [program,List.append_assoc] using h
lemma halt_at : program[79]?=some .halt := by
 unfold program
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,setup_length,publish_length,
  UniformMatchingAxisTableMachine.program_length];omega)]
 simp only[List.length_append,List.length_map,setup_length,publish_length,UniformMatchingAxisTableMachine.program_length];rfl

lemma setup_header {time r pool P W U A T D kind M : ℕ} {s : State}
 (h:Args time r pool P W U A T D kind M s) :
 UniformMatchingAxisTableMachine.Header r M T P W U A (applyBlock setup s) := by
 constructor <;>simp [setup,applyBlock,Op.apply,writeNat,next,h.radix,h.count,h.rows,h.permutation,h.widths,h.markers,h.axis]
lemma setup_heaps (s:State) : (applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧(applyBlock setup s).scalarReg=s.scalarReg ∧
 (applyBlock setup s).outputs=s.outputs ∧(applyBlock setup s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma setup_nat (s:State) (q:ℕ) (header:q<840 ∨847≤q) (zero:q≠5850) (one:q≠5853) :
 (applyBlock setup s).natReg q=s.natReg q := by
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_safe {s:State} {B:ℕ} (wb:WordBound B s) (code:80≤B) :
 readable setup s ∧ peak setup s≤B := by
 have a:=wb.2.1 5841;have b:=wb.2.1 894;have c:=wb.2.1 5847;have d:=wb.2.1 5843
 have e:=wb.2.1 5844;have f:=wb.2.1 5845;have g:=wb.2.1 5846
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next];omega

def Entry (D time r pool count W P kind : ℕ) (s:State) : Prop :=
 s.natHeap D=some time ∧s.natHeap (D+1)=some r ∧s.natHeap (D+2)=some pool ∧
 s.natHeap (D+3)=some count ∧s.natHeap (D+4)=some W ∧s.natHeap (D+5)=some P ∧s.natHeap (D+6)=some kind

structure PublishReady (time r pool P W A D kind M : ℕ) (s:State) : Prop where
 time:s.natReg 5840=time
 radix:s.natReg 5841=r
 pool:s.natReg 5842=pool
 permutation:s.natReg 5843=P
 widths:s.natReg 5844=W
 axis:s.natReg 846=A
 directory:s.natReg 5848=D
 kind:s.natReg 5849=kind
 zero:s.natReg 5850=0
 one:s.natReg 5853=1
 count:s.natHeap A=some (r-M)
lemma publish_safe {time r pool P W A D kind M B : ℕ} {s:State}
 (h:PublishReady time r pool P W A D kind M s) (wb:WordBound B s) (fit:D+7≤B) :
 readable publish s ∧peak publish s≤B := by
 have a:=wb.2.1 5840;have b:=wb.2.1 5841;have c:=wb.2.1 5842;have d:=wb.2.1 5844
 have e:=wb.2.1 5843;have f:=wb.2.1 5849;have g:=wb.2.1 846
 simp only[h.time,h.radix,h.pool,h.widths,h.permutation,h.kind,h.axis] at a b c d e f g
 simp [publish,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.time,h.radix,h.pool,
  h.widths,h.permutation,h.kind,h.axis,h.directory,h.zero,h.one,h.count]
 omega
lemma publish_entry {time r pool P W A D kind M : ℕ} {s:State}
 (h:PublishReady time r pool P W A D kind M s) :
 Entry D time r pool (r-M) W P kind (applyBlock publish s) := by
 simp [Entry,publish,applyBlock,Op.apply,writeNat,next,Function.update,h.time,h.radix,h.pool,
  h.widths,h.permutation,h.kind,h.axis,h.directory,h.zero,h.one,h.count]
 split_ifs <;>first |omega |rfl
lemma publish_low {time r pool P W A D kind M : ℕ} {s:State}
 (h:PublishReady time r pool P W A D kind M s) (q:ℕ) (hq:q<D) :
 (applyBlock publish s).natHeap q=s.natHeap q := by
 simp (disch:=omega) [publish,applyBlock,Op.apply,writeNat,next,Function.update,h.axis,h.directory,h.zero,h.one]
 split_ifs <;>first |omega |rfl
lemma publish_heaps (s:State) : (applyBlock publish s).scalarHeap=s.scalarHeap ∧
 (applyBlock publish s).scalarReg=s.scalarReg ∧(applyBlock publish s).outputs=s.outputs ∧
 (applyBlock publish s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩

/-- One charged Table→axis conversion and ABI7 print. The physical coefficient
pool is retained exactly. This bounded adapter does not assert a full cache loop. -/
theorem execution {time r pool P W U A T D kind M B n : ℕ} (x:Fin n→ℂ)
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
 (∀q,q<P→u.natHeap q=s.natHeap q) := by
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
 refine ⟨z,?_,?_,zp,publish_entry printing,rows',widths',perm',?_,?_,?_,?_,?_⟩
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

end
end ExactFourierCircuits.UniformLocalMatchingSlotDirectory
