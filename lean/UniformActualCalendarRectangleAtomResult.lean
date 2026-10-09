import UniformActualCalendarRectangleFineFactory
import UniformRequestCanonicalPhase
import UniformCalendarAtomValues
import UniformCalendarAtomSourceTransport

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleAtomResult
noncomputable section
open OAI.ExactFourier UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents UniformLocalCacheTreeMachine
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformCalendarRefinementActive UniformCalendarActualAtoms
open UniformGlobalCalendarUnion UniformGlobalCalendarGeometry UniformLocalCacheTiming UniformLocalFourierLayers UniformCalendarNativePieces
open UniformCalendarIntervalPartition UniformActualCalendarRectanglePhaseResult UniformCalendarAtomValues UniformCalendarAtomSourceTransport

attribute [local irreducible] Nat.add Nat.mul of_actual

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{R N:ℕ}
 {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:State}
 (g:Geometry constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N)
 (all:∀i (hi:i<(UniformAxisCacheRequestSource.requests visits).length),
  Complete constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N g i hi s)
 (forest:Contents p visits A positive s)(facts:Facts p visits)(hn:0<n)
 {O T:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤T)
 (radixRoom:radix n axisIndex≤envelope constants n)(sameRadix:p.radix=radix n axisIndex)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*UniformDirectLeafForestModel.demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*UniformDirectLeafForestModel.demand visits≤T)

def result (t:ℕ)(i:Fin (UniformAxisCacheRequestSource.requests visits).length)
 (j:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))).length)
 (active:((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).start +
   prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))) j.val≤t ∧
  t<((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).start+
   prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))) j.val+
    (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))).get j)
 (fit:Event.low ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event+
  Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event≤radix n axisIndex)
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta (radix n axisIndex)))≠0}
 (L:List (Layer (Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event)))
 (actual:Core (NewtonFourier.invH (zeta (radix n axisIndex))) hf
  ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event L):
 Result
  ((of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
   (UniformCalendarRefinementActive.order n (preparationEvents visits) ⟨UniformCalendarPreparationIndices.order visits (.inl i),j⟩).val
   (t-((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).start-
    prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))) j.val))
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex)
   (Event.low ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event)
   (Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).event) fit)
  L (t-((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))).start):=by
 let e:=(preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inl i))
 let before:=prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))) j.val
 let elapsed:=t-e.start-before
 have same:e=rectangleEvent ((UniformAxisCacheRequestSource.requests visits).get i):=
  UniformCalendarPreparationIndices.rectangle_get visits i
 have slots:=UniformActualCalendarRectangleFineFactory.slot_bound n visits i j
 have rows:pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))=
  List.replicate (slotCount n (UniformAxisCacheRequestSource.requests visits)[i].row) 28:=
  congrArg (fun e:TimedEvent=>durations n e.event) same
 have size:(pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))).get j=28:=
  get_replicate _ _ rows j
 have beforeEq:before=28*j.val:=by
  change prefixDuration _ j.val=_
  apply (congrArg (fun ds=>prefixDuration ds j.val) rows).trans
  simp only[prefixDuration,List.take_replicate,List.sum_replicate,Nat.nsmul_eq_mul,Nat.min_eq_left slots.le,Nat.mul_comm]
 have lo:e.start+before≤t:=active.1
 have upper:t<e.start+before+28:=by simpa only[size] using active.2
 have below:elapsed<28:=by dsimp only[elapsed];omega
 have fitq:(UniformAxisCacheRequestSource.requests visits)[i].row.offset+
  (UniformAxisCacheRequestSource.requests visits)[i].row.width≤radix n axisIndex:=by
  have bound:=fit
  change Event.low e.event+Event.width e.event≤radix n axisIndex at bound
  rw[same] at bound
  exact bound
 apply native_result (radix n axisIndex) t (NewtonFourier.invH (zeta (radix n axisIndex))) hf e
  (rectangleEvent ((UniformAxisCacheRequestSource.requests visits).get i)) same fitq _ (fun _=>rfl) _ _ L actual
 intro layers core
 let out:=UniformRequestCanonicalPhase.phase_result g all i.val i.isLt j.val slots core fitq elapsed below
 have eventEq:=UniformActualCalendarRectangleFineFactory.make g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat i j elapsed
 have clockEq:28*j.val+elapsed=t-((UniformAxisCacheRequestSource.requests visits)[i].time):=by
  have clock:=UniformCalendarAtomValues.clock e.start before t lo
  have startEq:e.start=(UniformAxisCacheRequestSource.requests visits)[i].time:=congrArg TimedEvent.start same
  simpa only[elapsed,beforeEq,startEq,Nat.sub_add_eq] using clock
 refine ⟨out.snapshot,?_,out.matrix.trans (congrArg (UniformCalendarRenderTick.tick layers) clockEq)⟩
 rw[eventEq]
 exact out.source

end
end ExactFourierCircuits.UniformActualCalendarRectangleAtomResult
