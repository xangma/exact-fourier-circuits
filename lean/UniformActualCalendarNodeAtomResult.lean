import UniformActualCalendarNodeFineFactory
import UniformActualCalendarForestPhaseResult
import UniformCalendarResultAmbient
import UniformRequestCanonicalPhase
import UniformCalendarAtomValues
import UniformCalendarAtomSourceTransport

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNodeAtomResult
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

def result (t:ℕ)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length)
 (k:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).length)
 (active:((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).start+
   prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))) k.val≤t ∧
  t<((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).start+
   prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))) k.val+
    (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).get k)
 (fit:Event.low ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event+
  Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event≤radix n axisIndex)
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta (radix n axisIndex)))≠0}
 (L:List (Layer (Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event)))
 (actual:Core (NewtonFourier.invH (zeta (radix n axisIndex))) hf
  ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event L):
 Result
  ((of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
   (UniformCalendarRefinementActive.order n (preparationEvents visits) ⟨UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩),k⟩).val
   (t-((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).start-
    prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))) k.val))
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex)
   (Event.low ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event)
   (Event.width ((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).event) fit)
  L (t-((preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).start):=by
 let e:=(preparationEvents visits).get (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))
 let before:=prefixDuration (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))) k.val
 let elapsed:=t-e.start-before
 let record:Fin (UniformDirectLeafForestModel.operations visits[i]):=⟨k.val,UniformActualCalendarNodeFineFactory.operation_bound n visits i j k⟩
 let topo:=UniformActualCalendarForestPhaseResult.operationIndex (p:=p) (A:=A) i record
 let K:=A+3*p.radix
 have same:e=⟨0,.direct (visits.get i).task.width (visits.get i).task.offset⟩:=
  UniformCalendarPreparationIndices.direct_descriptor visits i j
 have rows:pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))=
  durations n (.direct (visits.get i).task.width (visits.get i).task.offset):=
  congrArg (fun e:TimedEvent=>durations n e.event) same
 have get_congr {α:Type}{L M:List α}(eq:L=M)(idx:Fin L.length):
  L.get idx=M.get (finCongr (congrArg List.length eq) idx):=by cases eq;rfl
 have size:(pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).get k=
  UniformDirectLeafCacheChronology.duration (UniformTransposeDescriptorMachine.ofOperation (visits.get i).task.offset K
   ((UniformDirectToeplitz.topology (visits.get i).task.width).get topo)):=
  (get_congr rows k).trans (UniformCalendarAtomValues.direct_get n _ _ K _)
 have beforeEq:before=UniformDirectLeafCacheChronology.elapsed
  ((UniformTransposeDescriptorMachine.leafRecords (visits.get i).task.width (visits.get i).task.offset K).take k.val):=
  (congrArg (fun ds=>prefixDuration ds k.val) rows).trans (UniformActualCalendarAtomRecords.leaf_prefix _ _ K k.val).symm
 have startEq:e.start=0:=congrArg TimedEvent.start same
 have lo:e.start+before≤t:=active.1
 have upper:t<e.start+before+UniformDirectLeafCacheChronology.duration
  (UniformTransposeDescriptorMachine.ofOperation (visits.get i).task.offset K
   ((UniformDirectToeplitz.topology (visits.get i).task.width).get topo)):=by
  simpa only[size] using active.2
 have below:elapsed<UniformDirectLeafCacheChronology.duration
  (UniformTransposeDescriptorMachine.ofOperation (visits.get i).task.offset K
   ((UniformDirectToeplitz.topology (visits.get i).task.width).get topo)):=by dsimp only[elapsed];omega
 have fitq:(visits.get i).task.offset+(visits.get i).task.width≤radix n axisIndex:=by
  have bound:=fit
  change Event.low e.event+Event.width e.event≤radix n axisIndex at bound
  rw[same] at bound
  exact bound
 apply native_result (radix n axisIndex) t (NewtonFourier.invH (zeta (radix n axisIndex))) hf e
  ⟨0,.direct (visits.get i).task.width (visits.get i).task.offset⟩ same fitq _ (fun _=>rfl) _ _ L actual
 intro layers core
 have hfp:PowerSeries.constantCoeff (NewtonFourier.invH (zeta p.radix))≠0:=by rw[sameRadix];exact hf
 have corep:Core (NewtonFourier.invH (zeta p.radix)) hfp
  (.direct (visits.get i).task.width (visits.get i).task.offset) layers:=by rw[sameRadix];exact core
 have fitp:(visits.get i).task.offset+(visits.get i).task.width≤p.radix:=fitq.trans_eq sameRadix.symm
 let raw:=UniformActualCalendarForestPhaseResult.phase_result forest i record corep fitp elapsed below
 let out:=UniformCalendarResultAmbient.cast raw sameRadix
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex) (visits.get i).task.offset (visits.get i).task.width fitq)
  (fun _=>rfl)
 have eventEq:=UniformActualCalendarNodeFineFactory.make g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat i j k elapsed
 have clockEq:UniformDirectLeafCacheChronology.elapsed
  ((UniformTransposeDescriptorMachine.leafRecords (visits.get i).task.width (visits.get i).task.offset K).take k.val)+elapsed=t-0:=by
  have clock:=UniformCalendarAtomValues.clock e.start before t lo
  simpa only[elapsed,beforeEq,startEq,Nat.sub_add_eq] using clock
 refine ⟨out.snapshot,?_,out.matrix.trans (congrArg (UniformCalendarRenderTick.tick layers) clockEq)⟩
 rw[eventEq]
 exact out.source

end
end ExactFourierCircuits.UniformActualCalendarNodeAtomResult
