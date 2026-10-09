import UniformFinalFiniteAxisState
import UniformActualAxisPreparedCycle

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalFiniteAxisAdvance
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformJointAllocation (slab envelope)
open UniformTensorMonomialMachine (setPC)
open UniformFinalAxisRetention UniformFinalAxisPrinted UniformFinalFiniteAxisState
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program UniformActualGlobalConstants.constants UniformRecursiveSelfCallMachine.W

lemma reset_start {n g pc:ℕ}{j:Fin (axisCount n)}{x:Fin n→ℂ}{s v:State}
 {tree:ℕ→List UniformGlobalCalendarDispatch.Event}
 (a:UniformFourierAxisCommonResult.Result constants n g j tree x (setPC s pc) v):
 UniformFourierAxisCommonResult.Result constants n g j tree x s v:=
 ⟨a.pc,a.footer,a.selections,a.cached,a.action,a.inputs,a.natOutside,a.scalarOutside,a.outputs,a.roots,a.natReg⟩

def axisCost {n:ℕ}(hn:0<n){original:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (g k:ℕ):ℕ:=if h:k<axisCount n then
 let j:Fin (axisCount n):=⟨k,h⟩
 UniformFourierAxisOperationalCases.budget (radix n j)
  (UniformFourierAxisCommonInputs.records constants n j).length (UniformFourierAxisCommonInputs.nodes constants n j)+
  66*radix n j+233+(events hn cache g j).length*(9*radix n j+48)
 else 0

lemma printed_next {n g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (original s a u:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (j:Fin (axisCount n))
 (actual:UniformFourierAxisCommonResult.Result constants n g j (treeEvents hn cache j) x s a)
 (out:UniformFinalAxisSuffix.Output hn j (treeEvents hn cache j) x s a actual u)
 (old:UniformCalendarPrintedPrefix.Printed hn (events hn cache g) (position hn cache g) j.val s):
 UniformCalendarPrintedPrefix.Printed hn (events hn cache g) (position hn cache g) (j.val+1) u:=
 UniformCalendarPrintedPrefix.step hn (events hn cache g) (position hn cache g) j s u old out.frame
  (UniformFinalAxisPrinted.banks cache j actual out)

lemma ready_next {n H g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(original s a u:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (j:Fin (axisCount n))
 (actual:UniformFourierAxisCommonResult.Result constants n g j (treeEvents hn cache j) x s a)
 (out:UniformFinalAxisSuffix.Output hn j (treeEvents hn cache j) x s a actual u)
 (old:UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC s 5))
 (bound:WordBound (envelope constants n) u):
 UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC u 5):=
 UniformFinalAxisReadyTransport.ready old (UniformFinalAxisRetention.frame out) bound

lemma cache_frontiers_next {n g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (original s a u:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (j:Fin (axisCount n))
 (actual:UniformFourierAxisCommonResult.Result constants n g j (treeEvents hn cache j) x s a)
 (out:UniformFinalAxisSuffix.Output hn j (treeEvents hn cache j) x s a actual u):
 UniformAxisCacheStartupMachine.Frontiers constants n (j.val+1) u:=
 ⟨out.cacheNat.trans (cache_next j).1,out.cacheScalar.trans (cache_next j).2⟩

lemma directory_step (U k:ℕ):U+2*k+2=U+2*(k+1):=by omega

lemma next_state {n H g t:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(original s a u:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (k:ℕ)(hk:k<axisCount n)(state:AxisReady (H:=H) (g:=g) hn x v original cache k s)
 (actual:UniformFourierAxisCommonResult.Result constants n g ⟨k,hk⟩ (treeEvents hn cache ⟨k,hk⟩) x s a)
 (prepare:BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope constants n) (setPC s 0) t a)
 (out:UniformFinalAxisSuffix.Output hn ⟨k,hk⟩ (treeEvents hn cache ⟨k,hk⟩) x s a actual u)
 (front:a.natReg 6819=(UniformJointCacheAllocation.axis constants n ⟨k,hk⟩).endNat∧
  a.natReg 6821=(UniformJointCacheAllocation.axis constants n ⟨k,hk⟩).endScalar)
 (bound:WordBound (envelope constants n) u):AxisReady (H:=H) (g:=g) hn x v original cache (k+1) u:=by
 let j:Fin (axisCount n):=⟨k,hk⟩
 have frame:=UniformFinalAxisRetention.frame out
 have ready:=ready_next hn x v original s a u cache j actual out state.ready bound
 have printed:=printed_next hn x original s a u cache j actual out state.printed
 have nextCache:=cache_next j
 have nextWorkspace:=workspace_next j
 refine ⟨out.pc,out.index,out.directory.trans (directory_step _ _),?_,?_,?_,ready,state.retained.trans frame,printed,?_,?_⟩
 · exact out.nextNat.trans nextWorkspace.1
 · exact out.nextScalar.trans nextWorkspace.2
 · intro positive
   exact cache_frontiers_next hn x original s a u cache j actual out
 · intro q lo hi
   exact (out.seed q lo hi).trans ((UniformFinalAxisStartupFrame.prepare prepare q (Or.inr ⟨lo,hi⟩)).trans (state.seed q lo hi))
 · intro positive
   exact ⟨out.allocatorFrontiers.1.trans (front.1.trans nextCache.1),
    out.allocatorFrontiers.2.trans (front.2.trans nextCache.2)⟩

lemma cost_join (prep r count t dt:ℕ)(a:t≤prep)(b:dt≤66*r+232+count*(9*r+48)):
 1+(t+dt)≤prep+66*r+233+count*(9*r+48):=by omega

/-- One actual finite-axis advance: no preparation, action or advance callback. -/
theorem execution {n H g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(original s:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (k:ℕ)(hk:k<axisCount n)(state:AxisReady (H:=H) (g:=g) hn x v original cache k s)
 (bound:WordBound (envelope constants n) s):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x (envelope constants n) s ticks u∧
 ticks≤axisCost hn cache g k∧AxisReady (H:=H) (g:=g) hn x v original cache (k+1) u:=by
 let j:Fin (axisCount n):=⟨k,hk⟩
 have clock:=UniformFinalFiniteAxisState.clock state hk
 have kept:UniformAxisCachePhysical.Heaps constants n j original (setPC s 0):=
  ⟨(state.retained.cache j).nat,(state.retained.cache j).scalar⟩
 obtain ⟨a,t,prepare,cheap,actual⟩:=UniformFourierAxisCommonExecution.execution (cache j) kept clock
 have front:=UniformFourierAxisCommonFrontiers.frontiers (cache j) kept clock prepare
 let actual':=reset_start actual
 obtain ⟨u,dt,suffix,suffixCheap,out⟩:=UniformFinalAxisSuffix.execution hn j (treeEvents hn cache j) x s a actual'
  (capacity hn cache g j) (allocator_slab state.ready).2 state.directory state.index state.ready.one prepare.final_bound
 have axes:s.natReg 5938=axisCount n:=state.ready.axes
 have run:=UniformActualAxisPreparedCycle.join_preparation x s a u state.pc
  (by rw[state.index,axes];exact hk) bound (UniformActualGlobalClockProgram.code_bound n) prepare suffix
 have done:=next_state hn x v original s a u cache k hk state actual' prepare out front run.final_bound
 refine ⟨u,1+(t+dt),run,?_,done⟩
 unfold axisCost
 rw[dite_eq_left hk]
 exact cost_join _ _ _ _ _ cheap suffixCheap

end
end ExactFourierCircuits.UniformFinalFiniteAxisAdvance
