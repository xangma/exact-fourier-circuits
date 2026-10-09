import UniformDirectLeafForestSelect
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestSplit
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestModel
open UniformDirectLeafForestControl UniformLocalCacheTreeMachine
noncomputable section

def skipped(s:State):State:=applyBlock UniformDirectLeafForestProgram.skip s
def finished(s:State):State:=UniformDirectLeafForestAdvance.advanced (setPC (skipped s) 450)
lemma heap {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}(h:Cursor p visits i s):
 (finished s).natHeap=UniformDirectLeafForestCapture.outputHeap s.natHeap p.ranges i
  (position p visits i).entry 0:=by
 simp [finished,skipped,UniformDirectLeafForestAdvance.advanced,UniformDirectLeafForestProgram.skip,
  UniformDirectLeafForestProgram.advance,applyBlock,Op.apply,writeNat,next,setPC,
  h.index,h.two,h.ranges,h.entry,h.one,h.zero,UniformDirectLeafForestCapture.outputHeap,Nat.mul_comm]
lemma frame(s:State):(finished s).scalarHeap=s.scalarHeap ∧(finished s).scalarReg=s.scalarReg ∧
 (finished s).outputs=s.outputs ∧(finished s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma nextCursor {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}
 (hi:i<visits.length)(h:Cursor p visits i s)(split:¬leaf visits[i]):
 Cursor p visits (i+1) (finished s):=by
 have following:=before_next visits i hi
 rw[show operations visits[i]=0 from ite_eq_right split,Nat.add_zero] at following
 constructor
 · constructor <;>simp [finished,skipped,UniformDirectLeafForestAdvance.advanced,
    UniformDirectLeafForestProgram.skip,UniformDirectLeafForestProgram.advance,
    applyBlock,Op.apply,writeNat,next,setPC,h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,
    h.permutation,h.widths,h.markers,h.axis,h.entry,position,following]
 all_goals simp [finished,skipped,UniformDirectLeafForestAdvance.advanced,
  UniformDirectLeafForestProgram.skip,UniformDirectLeafForestProgram.advance,
  applyBlock,Op.apply,writeNat,next,setPC,h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,
  h.root,h.one,h.two,h.seven,h.four,h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges,
  following,Nat.mul_add,Nat.add_assoc]

theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}
 (x:Fin n→ℂ)(s:State)(h:Cursor p visits i s)(hi:i<visits.length)
 (range:p.ranges+2*visits.length≤B)(nodeEnd:p.nodes+7*visits.length≤B)
 (code:461≤B)(pc:s.pc=445)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 8 (finished s):=by
 have entryB:=wb.2.1 6609
 have slots:2*i+1<2*visits.length:=by omega
 have run:BoundedRuns UniformDirectLeafForestProgram.program n x B s 5 (skipped s):=by
  apply block_runs UniformDirectLeafForestProgram.skip UniformDirectLeafForestProgram.program 445 n B x s
   UniformDirectLeafForestProgram.skip_code pc wb (by change 450≤B;omega)
  · simp [UniformDirectLeafForestProgram.skip,readable,Op.readable]
  · simp [UniformDirectLeafForestProgram.skip,peak,Op.peak,Op.apply,writeNat,next,
    h.index,h.two,h.ranges,h.one,h.zero,h.entry]
    rw[h.entry] at entryB
    omega
 have ep:(skipped s).pc=450:=by rw[skipped,applyBlock_pc,pc,UniformDirectLeafForestProgram.skip_length]
 have moved:(setPC (skipped s) 450)=skipped s:=by rw[←ep];cases skipped s;rfl
 have keep(j:ℕ)(ne:j≠6683):(skipped s).natReg j=s.natReg j:=by
  simp [skipped,UniformDirectLeafForestProgram.skip,applyBlock,Op.apply,writeNat,next,ne]
 have seven:(skipped s).natReg 6671=7:=(keep _ (by omega)).trans h.seven
 have one:(skipped s).natReg 6669=1:=(keep _ (by omega)).trans h.one
 have pointer:(skipped s).natReg 6663+7≤B:=by rw[keep _ (by omega),h.pointer];omega
 have index:(skipped s).natReg 6662+1≤B:=by
  have countBound:=wb.2.1 6661;rw[h.count] at countBound
  rw[keep _ (by omega),h.index];omega
 have advance:=UniformDirectLeafForestAdvance.execution x (skipped s) seven one pointer index code ep run.final_bound
 simpa only[finished,moved] using run.trans advance
end
end ExactFourierCircuits.UniformDirectLeafForestSplit
