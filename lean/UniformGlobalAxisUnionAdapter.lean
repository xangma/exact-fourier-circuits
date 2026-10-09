import UniformMatchingKernelAmbient
import UniformLocalMatchingSlotDirectory
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalAxisUnionAdapter
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformMatchingAxisTableMachine (physicalAxis)
namespace U
export UniformMatchingKernelAmbient (edges range matching)
end U
noncomputable section
/-- Real281 output headers are read directly. The five arena arguments are
ordinary addresses computed by the global axis loop. -/
structure Args (r M pool T P W marker A D:ℕ) (s:State):Prop where
 radix:s.natReg 6768=r
 pool:s.natReg 6769=pool
 rows:s.natReg 6770=T
 count:s.natReg 6771=M
 permutation:s.natReg 5926=P
 widths:s.natReg 5927=W
 marker:s.natReg 5928=marker
 axis:s.natReg 5929=A
 directory:s.natReg 5930=D

def setup:List Op:=[.literal 5931 0,.literal 5932 1,
 .add 840 6768 5931,.add 841 6771 5931,.add 842 6770 5931,
 .add 843 5926 5931,.add 844 5927 5931,.add 845 5928 5931,.add 846 5929 5931]
def publish:List Op:=[.add 5933 5930 5931,.putNat 5933 6768,
 .add 5933 5933 5932,.putNat 5933 6769]
def program:Program:=setup.map Op.code++UniformMatchingAxisTableMachine.program.map (relocate 9 64)++
 publish.map Op.code++[.halt]
lemma program_length:program.length=69:=rfl
lemma setup_code:BlockAt setup program 0:=by intro i hi;change i<9 at hi;interval_cases i <;>rfl
lemma matching_code:CodeAt UniformMatchingAxisTableMachine.program program 9 64:=by
 exact UniformRankCrossPreparationMachine.segment_code (setup.map Op.code) (publish.map Op.code++[.halt]) _ 9 64 rfl
lemma publish_code:BlockAt publish program 64:=by
 exact UniformRankCrossPreparationMachine.block_of_segment publish
  (setup.map Op.code++UniformMatchingAxisTableMachine.program.map (relocate 9 64)) [.halt] 64 rfl
lemma halt_at:program[68]?=some .halt:=rfl
lemma setup_safe {B:ℕ} (s:State) (wb:WordBound B s) (code:69≤B):
 readable setup s ∧peak setup s≤B:=by
 have h0:=wb.2.1 6768;have h1:=wb.2.1 6769;have h2:=wb.2.1 6770;have h3:=wb.2.1 6771
 have h4:=wb.2.1 5926;have h5:=wb.2.1 5927;have h6:=wb.2.1 5928;have h7:=wb.2.1 5929
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
lemma setup_header {r M pool T P W marker A D:ℕ} {s:State} (h:Args r M pool T P W marker A D s):
 UniformMatchingAxisTableMachine.Header r M T P W marker A (applyBlock setup s):=by
 constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.radix,h.count,h.rows,h.permutation,h.widths,h.marker,h.axis]
lemma setup_kept (s:State) (q:ℕ) (lo:5900≤q) (zero:q≠5931) (one:q≠5932):
 (applyBlock setup s).natReg q=s.natReg q:=by
 simp(disch:=omega)[setup,applyBlock,Op.apply,writeNat,next]
structure PrintArgs (r pool D:ℕ) (s:State):Prop where
 radix:s.natReg 6768=r
 pool:s.natReg 6769=pool
 directory:s.natReg 5930=D
 zero:s.natReg 5931=0
 one:s.natReg 5932=1
lemma publish_safe {r pool D B:ℕ} {s:State} (h:PrintArgs r pool D s)
 (wb:WordBound B s) (fit:D+2≤B):readable publish s ∧peak publish s≤B:=by
 have hr: r≤B:=by rw[←h.radix];exact wb.2.1 6768
 have hp: pool≤B:=by rw[←h.pool];exact wb.2.1 6769
 simp[publish,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.radix,h.pool,h.directory,h.zero,h.one]
 omega
lemma published {r pool D:ℕ} {s:State} (h:PrintArgs r pool D s):
 (applyBlock publish s).natHeap D=some r ∧(applyBlock publish s).natHeap (D+1)=some pool:=by
 simp[publish,applyBlock,Op.apply,writeNat,next,Function.update,h.radix,h.pool,h.directory,h.zero,h.one]
lemma publish_outside {r pool D:ℕ} {s:State} (h:PrintArgs r pool D s) (q:ℕ)
 (outside:q<D ∨D+2≤q):(applyBlock publish s).natHeap q=s.natHeap q:=by
 simp(disch:=omega)[publish,applyBlock,Op.apply,writeNat,next,Function.update,h.directory,h.zero,h.one]
 split_ifs <;>first |omega |rfl
/-- Literal69 partitions the genuine disjoint call union and prints its true
factor-directory entry. Matching and bounds are derived from the actual
ordered endpoint injection, never supplied as an oracle. -/
theorem execution {r M pool T P W marker A D B n:ℕ} (x:Fin n→ℂ)
 (position:(Σ _:Fin M,Fin 2) ↪ Fin r) (s:State) (args:Args r M pool T P W marker A D s)
 (src:UniformMatchingAxisTableMachine.Edges (U.edges position) T s) (positive:2≤r)
 (hT:T+3*M≤P) (hP:P+r≤W) (hW:W+r≤ marker) (hU:marker+r≤A) (hA:A+4≤B)
 (hD:D+2≤P) (code:69≤B) (pc:s.pc=0) (wb:WordBound B s):
 ∃u,BoundedExecution program n x B s (UniformMatchingAxisTableMachine.runtime r M+14) u ∧
 UniformMatchingAxisTableMachine.runtime r M+14≤21*r+35 ∧u.pc=68 ∧
 u.natHeap D=some r ∧u.natHeap (D+1)=some pool ∧
 UniformSectorPackingMachine.Rows [physicalAxis r W P (U.edges position) (U.matching position) (U.range position) positive] 0 A u ∧
 UniformSectorPackingMachine.Widths [physicalAxis r W P (U.edges position) (U.matching position) (U.range position) positive] u ∧
 UniformSectorPackingMachine.Permutations [physicalAxis r W P (U.edges position) (U.matching position) (U.range position) positive] u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,(q<D ∨D+2≤q)→(q<P ∨P+r≤q)→(q<W ∨W+r≤q)→(q< marker ∨marker+r≤q)→
  (q<A ∨A+4≤q)→u.natHeap q=s.natHeap q):=by
 have safe:=setup_safe s wb code
 have boot:=block_runs setup program 0 n B x s setup_code pc wb (by change 0+9≤B;omega) safe.1 safe.2
 let b:=applyBlock setup s
 have bp:b.pc=9:=by rw[applyBlock_pc,pc];rfl
 let ready:=setPC b 0
 have rb:=changePC_bound B b 0 boot.final_bound (by omega)
 have head:=setup_header args
 have readyHeader:UniformMatchingAxisTableMachine.Header r M T P W marker A ready:=
  ⟨head.radix,head.count,head.source,head.permutation,head.widths,head.markers,head.row⟩
 obtain ⟨v,run,vp,vh,perm,widths,_markers,row,_edges,out,frame⟩:=
  UniformMatchingAxisTableMachine.execution r M T P W marker A B n x (U.edges position) ready readyHeader rfl src
   (U.matching position) (U.range position) hT hP hW hU hA (by omega) rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw[UniformMatchingAxisTableMachine.program_length];omega) (by omega) run
 rw[show placed 9 ready=b by change {b with pc:=9}=b;rw[←bp]] at moved
 let printState:=setPC v 64
 have kept (q:ℕ) (lo:5900≤q) (z:q≠5931) (o:q≠5932):printState.natReg q=s.natReg q:=
  (frame.2.2.2.2 q (Or.inr (by omega))).trans (setup_kept s q lo z o)
 have printing:PrintArgs r pool D printState:=by
  refine ⟨(kept 6768 (by omega) (by omega) (by omega)).trans args.radix,
   (kept 6769 (by omega) (by omega) (by omega)).trans args.pool,
   (kept 5930 (by omega) (by omega) (by omega)).trans args.directory,?_,?_⟩
  · exact (frame.2.2.2.2 5931 (Or.inr (by omega))).trans (by simp[ready,b,setPC,setup,applyBlock,Op.apply,writeNat,next])
  · exact (frame.2.2.2.2 5932 (Or.inr (by omega))).trans (by simp[ready,b,setPC,setup,applyBlock,Op.apply,writeNat,next])
 have safety:=publish_safe printing moved.final_bound (by omega)
 have printed:=block_runs publish program 64 n B x printState publish_code rfl moved.final_bound
  (by change 64+4≤B;omega) safety.1 safety.2
 let z:=applyBlock publish printState
 have zp:z.pc=68:=by rw[applyBlock_pc];rfl
 have done:BoundedExecution program n x B z 1 z:=.halt printed.final_bound (by simp[step,zp,halt_at])
 have pBank:UniformMatchingAxisTableMachine.Bank P (UniformMatchingAxisTableMachine.ordered r (U.edges position)) z:=by
  intro j hj
  exact (publish_outside printing (P+j) (Or.inr (by omega))).trans (perm j hj)
 have wBank:UniformMatchingAxisTableMachine.Bank W (UniformMatchingAxisTableMachine.widths r M) z:=by
  intro j hj
  exact (publish_outside printing (W+j) (Or.inr (by omega))).trans (widths j hj)
 have aRow:UniformMatchingAxisTableMachine.AxisRow A r M W P z:=by
  unfold UniformMatchingAxisTableMachine.AxisRow
  rw[publish_outside printing A (Or.inr (by omega)),publish_outside printing (A+1) (Or.inr (by omega)),
   publish_outside printing (A+2) (Or.inr (by omega)),publish_outside printing (A+3) (Or.inr (by omega))]
  exact row
 obtain ⟨rows',widths',perm'⟩:=UniformMatchingAxisTableMachine.physical_axis (U.edges position) z
  (U.matching position) (U.range position) positive aRow pBank wBank
 refine ⟨z,?_,?_,zp,(published printing).1,(published printing).2,rows',widths',perm',frame.1,
  frame.2.1,frame.2.2.1,frame.2.2.2.1,?_⟩
 · convert boot.executes (moved.executes (printed.executes done)) using 1
   change _=9+(UniformMatchingAxisTableMachine.runtime r M+(4+1));omega
 · have:=UniformMatchingAxisTableMachine.runtime_linear r M (UniformMatchingAxisTableMachine.matching_capacity r (U.edges position) (U.matching position) (U.range position));omega
 · intro q publish permutation widths markers axis
   exact (publish_outside printing q publish).trans (out q permutation widths markers axis)
end
end ExactFourierCircuits.UniformGlobalAxisUnionAdapter
