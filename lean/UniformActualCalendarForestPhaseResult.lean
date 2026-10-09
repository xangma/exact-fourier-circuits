import UniformActualCalendarRectanglePhaseResult
import UniformActualCalendarNativeDirect
import UniformActualCalendarForestRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarForestPhaseResult
noncomputable section
open OAI.ExactFourier UniformLocalCacheTreeMachine UniformDirectLeafForestData UniformDirectLeafForestContents
open UniformDirectLeafForestModel UniformDirectLeafCacheChronology UniformTransposeDescriptorMachine
open UniformDirectToeplitz UniformCalendarNativePieces UniformLocalFourierLayers UniformActualCalendarNativeDirect
open UniformActualCalendarRectanglePhaseResult UniformActualCalendarDirectSource

variable {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:UniformMachine.State}
 (forest:Contents p visits A positive s)
 (i:Fin visits.length)(j:Fin (operations visits[i]))

abbrev width:ℕ:=(visits.get i).task.width
abbrev offset:ℕ:=(visits.get i).task.offset
abbrev coefficientBase:ℕ:=A+3*p.radix

def operationIndex:Fin (topology (width i)).length:=
 ⟨j.val,by
  have bound:=UniformActualCalendarForestRegistry.record_bound (p:=p) (A:=A) i j
  simpa only[UniformDirectLeafForestLeafEnd.qs,UniformDirectLeafCacheProducedSource.records,ite_true,
   leafRecords,List.length_map,width,List.get_eq_getElem,Fin.getElem_fin] using bound⟩

lemma descriptor:
 (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j.val]'(UniformActualCalendarForestRegistry.record_bound i j)=
 ofOperation (offset i) (coefficientBase (p:=p) (A:=A))
  ((topology (width i)).get (operationIndex (p:=p) (A:=A) i j)):=by
 have bound:j.val<((topology (width i)).map (ofOperation (offset i) (coefficientBase (p:=p) (A:=A)))).length:=by
  rw[List.length_map];exact (operationIndex (p:=p) (A:=A) i j).isLt
 change ((topology (width i)).map (ofOperation (offset i) (coefficientBase (p:=p) (A:=A))))[j.val]'bound=_
 exact List.getElem_map _

/-- Each corrected forest factory supplies its native direct phase and exact
ordered source directly from the genuine retained SemanticResult. -/
def phase_result {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta p.radix))≠0}
 {L:List (Layer (width i))}
 (actual:Core (NewtonFourier.invH (zeta p.radix)) hf (.direct (width i) (offset i)) L)
 (extent:offset i+width i≤p.radix)(elapsed:ℕ)
 (phase:elapsed<duration (ofOperation (offset i) (coefficientBase (p:=p) (A:=A))
  ((topology (width i)).get (operationIndex (p:=p) (A:=A) i j)))):
 Result (UniformActualCalendarDirectProduced.event (UniformActualCalendarForestRegistry.data forest i j) elapsed)
  (UniformChunkPortMachine.intervalEmbedding p.radix (offset i) (width i) extent)
  L (UniformDirectLeafCacheChronology.elapsed
   ((leafRecords (width i) (offset i) (coefficientBase (p:=p) (A:=A))).take j.val)+elapsed):=by
 let op:=(topology (width i)).get (operationIndex (p:=p) (A:=A) i j)
 let hv:=topology_positive (operationIndex (p:=p) (A:=A) i j)
 let h:Fin (width i)→ℂ:=fun x=>PowerSeries.coeff x.val (NewtonFourier.invH (zeta p.radix))
 let h0:=invH_zero p.radix (width i) hv
 refine ⟨snapshot p.radix (width i) (operationIndex (p:=p) (A:=A) i j) elapsed,?_,?_⟩
 · apply operation_source (UniformActualCalendarForestRegistry.data forest i j) h hv h0 op
    (offset i) (coefficientBase (p:=p) (A:=A)) elapsed
    (UniformChunkPortMachine.intervalEmbedding p.radix (offset i) (width i) extent) (fun _=>rfl)
   · exact descriptor i j
   · exact (congrArg (UniformDirectLeafCacheSource.mu p.radix (coefficientBase (p:=p) (A:=A)))
      (descriptor (p:=p) (A:=A) i j)).trans
      (mu_invH_ofOperation p.radix (width i) (offset i) (coefficientBase (p:=p) (A:=A)) hv op)
 · exact snapshot_tick p.radix (width i) (offset i) (coefficientBase (p:=p) (A:=A))
    (operationIndex (p:=p) (A:=A) i j) elapsed actual phase

end
end ExactFourierCircuits.UniformActualCalendarForestPhaseResult
