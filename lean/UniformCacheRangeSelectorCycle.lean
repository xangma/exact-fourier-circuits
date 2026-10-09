import UniformCacheRangeSelectorBoot
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPreparationRowTableMachine (control_run)
noncomputable section
lemma placed_zero (s:State)(base:ℕ)(pc:s.pc=base):placed base (setPC s 0)=s:=by
 cases s;simp_all[placed,setPC]
lemma load_result {r tasks N tick O used i}{q:Range}{s:State}(h:Control r tasks N tick O used i s)
 (a:s.natHeap (tasks+2*i)=some q.base)(b:s.natHeap (tasks+2*i+1)=some q.count):
 Control r tasks N tick O used i (applyBlock loadRange s) ∧
 UniformGlobalCalendarSelector.Args q.base (stride r) q.count tick O used (applyBlock loadRange s):=by
 constructor
 · constructor <;>simp[loadRange,applyBlock,Op.apply,writeNat,next,h.zero,h.one,h.two,h.spacing,
    h.nodeCount,h.index,h.pointer,h.tick,h.output,h.used,a,b]
 · constructor <;>simp[loadRange,applyBlock,Op.apply,writeNat,next,h.zero,h.one,h.spacing,
    h.pointer,h.tick,h.output,h.used,a,b]
lemma advance_result {r tasks N tick O used i s}(h:Control r tasks N tick O used i s):
 Control r tasks N tick O used (i+1) (applyBlock advance s):=by
 constructor <;>simp[advance,applyBlock,Op.apply,writeNat,next,h.zero,h.one,h.two,h.spacing,
    h.nodeCount,h.index,h.pointer,h.tick,h.output,h.used]; omega

/-- One real node-range read and full thirty-op scan. The used count comes
from actual appends, while the local tick is retained exactly. -/
theorem cycle {n r tasks N tick O used i B}(x:Fin n → ℂ)(q:Range)(s:State)
 (h:Control r tasks N tick O used i s)(index:i<N)(pc:s.pc=51)(wb:WordBound B s)(code:90 ≤ B)
 (a:s.natHeap (tasks+2*i)=some q.base)(b:s.natHeap (tasks+2*i+1)=some q.count)
 (source:S.Source q.base (stride r) q.count q.records s.natHeap)
 (pointers:tasks+2*(i+1)+2 ≤ B)(fit:endAddress r q ≤ O)(ob:O ≤ B)
 (values:∀j,j<q.count → (q.records j).1+28 ≤ B ∧ (q.records j).2 ≤ B)
 (outFit:O+2*(used+q.count) ≤ B):∃u ticks,
 BoundedRuns program n x B s ticks u ∧ticks ≤ 21*q.count+16 ∧u.pc=51 ∧
 Control r tasks N tick O (used+(S.selected q.base (stride r) tick q.records 0 q.count).length) (i+1) u ∧
 u.natHeap=S.writeSelections O used (S.selected q.base (stride r) tick q.records 0 q.count) s.natHeap:=by
 have enterStep:step program n x s=.running (setPC s 52):=by
  simp[step,pc,code_51,h.index,h.nodeCount,index,setPC]
 have enter:=control_run program n B 52 x s wb (by omega) enterStep
 let begin:=setPC s 52
 have bh:=h.withPC 52
 have ab:q.base ≤ B:=(wb.2.2.1 _ _ a).2
 have bb:q.count ≤ B:=(wb.2.2.1 _ _ b).2
 have sb:stride r ≤ B:=by simpa only[h.spacing] using wb.2.1 7110
 have load:BoundedRuns program n x B begin 4 (applyBlock loadRange begin):=by
  apply block_runs loadRange program 52 n B x begin load_code rfl enter.final_bound (by change 56 ≤ B;omega)
  · simp[loadRange,readable,Op.readable,Op.apply,writeNat,next,h.pointer,h.one,a,b,begin,setPC]
  · simp[loadRange,peak,Op.peak,Op.apply,writeNat,next,h.pointer,h.one,h.zero,h.spacing,a,b,begin,setPC]
    omega
 let loaded:=applyBlock loadRange begin
 have lp:loaded.pc=56:=by rw[applyBlock_pc];rfl
 have results:=load_result bh a b
 let ready:=setPC loaded 0
 have readyBound:=changePC_bound B loaded 0 load.final_bound (by omega)
 have args:UniformGlobalCalendarSelector.Args q.base (stride r) q.count tick O used ready:=
  ⟨results.2.directory,results.2.spacing,results.2.count,results.2.tick,results.2.output,results.2.used⟩
 obtain ⟨t,last,scan,cost,done,heap⟩:=UniformGlobalCalendarSelector.execution x q.records ready args rfl readyBound
  (by omega) source (fit.trans ob) fit values outFit
 have second:=UniformBoundedAssembly.boundedExecution_placed node_code
  (by rw[UniformGlobalCalendarSelector.program_length];omega) (by omega) scan
 rw[placed_zero loaded 56 lp] at second
 let after:=setPC last 86
 have ah:Control r tasks N tick O (used+(S.selected q.base (stride r) tick q.records 0 q.count).length) i after:=
  (selector_control scan (results.1.withPC 0) done).withPC 86
 have nb:N ≤ B:=by rw[←h.nodeCount];exact wb.2.1 7107
 have finish:BoundedRuns program n x B after 2 (applyBlock advance after):=by
  apply block_runs advance program 86 n B x after advance_code rfl second.final_bound (by change 88 ≤ B;omega)
  · simp[advance,readable,Op.readable]
  · simp[advance,peak,Op.peak,Op.apply,writeNat,next,ah.index,ah.pointer,ah.one,ah.two]
    omega
 let advanced:=applyBlock advance after
 have ap:advanced.pc=88:=by rw[applyBlock_pc];rfl
 have jumpStep:step program n x advanced=.running (setPC advanced 51):=by simp[step,ap,code_88,setPC]
 have jump:=control_run program n B 51 x advanced finish.final_bound (by omega) jumpStep
 refine ⟨setPC advanced 51,1+4+t+2+1,((enter.trans load).trans second).trans (finish.trans jump),by omega,rfl,
  (advance_result ah).withPC 51,?_⟩
 exact heap
end
end ExactFourierCircuits.UniformCacheRangeSelector
