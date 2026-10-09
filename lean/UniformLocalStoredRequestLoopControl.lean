import UniformLocalStoredRequestLoopProgram
import UniformLocalRequestControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestControl

def axisOperations:List Op:=[.literal 6190 0,.add 4200 6906 6190]
lemma axisOperations_length:axisOperations.length=2:=rfl
lemma axis_code:BlockAt axisOperations program 22:=by
 intro i hi
 change i<2 at hi
 interval_cases i
 · exact zero_at
 · exact axis_at

noncomputable section
def entered (s:State):State:=applyBlock axisOperations (setPC s 22)
lemma entered_pc (s:State):(entered s).pc=24:=rfl
lemma entered_axis (s:State):(entered s).natReg 4200=s.natReg 6906:=by
 simp [entered,axisOperations,applyBlock,Op.apply,writeNat,next,setPC]
lemma entered_heaps (s:State):(entered s).natHeap=s.natHeap ∧
 (entered s).scalarHeap=s.scalarHeap ∧(entered s).scalarReg=s.scalarReg ∧
 (entered s).outputs=s.outputs ∧(entered s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma entered_keeps (s:State)(q:ℕ)(a:q≠6190)(b:q≠4200):(entered s).natReg q=s.natReg q:=by
 simp [entered,axisOperations,applyBlock,Op.apply,writeNat,next,setPC,a,b]
lemma entered_control {constants n j qs R T i s}(h:Control constants n j qs R T i s):
 Control constants n j qs R T i (entered s):=by
 apply h.retained
 · intro q lo hi;exact entered_keeps s q (by omega) (by omega)
 · intro q lo;exact entered_keeps s q (by omega) (by omega)

/-- One actual loop test plus two charged instructions install the axis index.
No scalar, heap, root, tag or output is changed by these three instructions. -/
lemma enter {constants n j qs R T i B}{x:Fin n→ℂ}{s:State}
 (h:Control constants n j qs R T i s)(more:i<qs.length)
 (pc:s.pc=21)(wb:WordBound B s)(code:3776≤B):
 BoundedRuns program n x B s 3 (entered s):=by
 have first:BoundedRuns program n x B s 1 (setPC s 22):=.next wb
  (by simp [step,pc,branch_at,h.live.index,h.live.count,more,setPC])
  (.refl (changePC_bound B s 22 wb (by omega)))
 have safe:readable axisOperations (setPC s 22) ∧ peak axisOperations (setPC s 22)≤B:=by
  constructor
  · simp [axisOperations,readable,Op.readable]
  · simpa [axisOperations,peak,Op.peak,Op.apply,writeNat,next,setPC] using wb.2.1 6906
 have last:=block_runs axisOperations program 22 n B x (setPC s 22) axis_code rfl
  first.final_bound (by rw [axisOperations_length];omega) safe.1 safe.2
 simpa only [axisOperations_length,entered] using first.trans last

lemma stop {constants n j qs R T B}{x:Fin n→ℂ}{s:State}
 (h:Control constants n j qs R T qs.length s)(pc:s.pc=21)
 (wb:WordBound B s)(code:3776≤B):
 BoundedExecution program n x B s 2 (setPC s 3775):=by
 have bound:=changePC_bound B s 3775 wb (by omega)
 refine .next wb ?_ (.halt bound ?_)
 · simp only [step,pc,branch_at,h.live.index,h.live.count,lt_self_iff_false,ite_false]
   rfl
 · simp [step,setPC,halt_at]
attribute [irreducible] entered
end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
