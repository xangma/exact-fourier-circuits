import UniformDirectLeafForestRowStart
import UniformDirectLeafForestCacheRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestRow
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformLocalCacheTreeMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
noncomputable section

structure Done(p:Parameters)(visits:List Visit)(i A:ℕ)(hi:i<visits.length)(positive:2≤p.radix)(s u:State):Prop where
 pc:u.pc=31
 cursor:Cursor p visits (i+1) u
 frame:UniformDirectLeafForestLeafStep.StepFrame p visits i s u
 range:RangeAt p visits i hi u
 events:leaf visits[i]→∀j (hj:j<(UniformDirectLeafForestLeafEnd.qs p A visits[i]).length),Nonempty
  (UniformDirectLeafCacheSemanticExecution.SemanticResult
   (slot (UniformDirectLeafForestForward.config p visits i) p.radix
    (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j) p.radix
   (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j]
   (UniformDirectLeafCacheSource.mu p.radix (A+3*p.radix)
    (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j]) positive u)

/-- A real leaf executes388 and captures a measured range; a real split
executes the zero-range branch. Both routes advance the physical node cursor. -/
theorem from_read {p:Parameters}{visits:List Visit}{i n B:ℕ}
 (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))(x:Fin n→ℂ)(s:State)
 (hi:i<visits.length)(h:ReadCursor p visits i visits[i] s)
 (src:Sources p visits n s)(facts:Facts p visits)
 (radix:p.radix=UniformAllAxisSeedPreparation.radix n axis)(positive:2≤p.radix)
 (od:p.start.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:p.start.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (l:Placement p (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B visits)
 (pc:s.pc=37)(wb:WordBound B s):∃u ticks,
 BoundedRuns UniformDirectLeafForestProgram.program n x B s ticks u ∧
 ticks≤(62*p.radix+246)*operations visits[i]+87 ∧
 Done p visits i (UniformAllAxisSeedPreparation.axisBase n axis.val) hi positive s u:=by
 have code:=l.code
 have range:p.ranges+2*visits.length≤B:=by
  have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;have:=l.natEnd;omega
 have nodes:p.nodes+7*visits.length≤B:=by have:=l.nodeEnd;have:=l.rows;have:=l.natEnd;omega
 by_cases stop:leaf visits[i]
 · obtain ⟨selTicks,select,selCost⟩:=UniformDirectLeafForestSelect.leaf_branch x s h stop code pc wb
   obtain ⟨b,ticks,body,cost,res,ctrl⟩:=UniformDirectLeafForestLeafCall.execution axis x (setPC s 39)
    hi (h.withPC 39) radix positive (src.withPC (pc:=39)).original (src.withPC (pc:=39)).conjugate (src.withPC (pc:=39)).constants od cd
    (src.nodes i hi) stop (facts.extent i hi) (facts.duration i hi stop) l.toLayout l.nodeEnd rfl select.final_bound
   have res0:=UniformDirectLeafForestLeafCall.source_transport res (s:=s) rfl rfl rfl rfl
   have finish:=UniformDirectLeafForestLeafStep.finish_execution x (setPC s 39) b hi stop positive res ctrl
    range l.ordinal nodes code body.final_bound
   let u:=UniformDirectLeafForestLeafEnd.finished b
   have whole:BoundedRuns UniformDirectLeafForestProgram.program n x B s (selTicks+(9+ticks)+12) u:=
    (select.trans body).trans finish
   refine ⟨u,_,whole,?_,?_,⟩
   · rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop]
     omega
   · refine ⟨rfl,UniformDirectLeafForestLeafEnd.nextCursor hi stop positive res ctrl,?_,?_,?_⟩
     · exact UniformDirectLeafForestLeafStep.frame hi stop positive res0 ctrl
        (by have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;omega) l.cacheEnd l.descriptors
        (by have:=facts.extent i hi;omega)
     · constructor
       · rw[UniformDirectLeafForestLeafEnd.rangeHeap hi positive res ctrl]
         simp [UniformDirectLeafForestCapture.outputHeap]
       · rw[UniformDirectLeafForestLeafEnd.rangeHeap hi positive res ctrl]
         simp [UniformDirectLeafForestCapture.outputHeap,operations,stop]
     · intro _
       exact UniformDirectLeafForestLeafEnd.events hi stop positive l.toLayout
        (by have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;omega)
        (facts.extent i hi) (facts.duration i hi stop) res ctrl
 · have select:=UniformDirectLeafForestSelect.split_branch x s h stop code pc wb
   have body:=UniformDirectLeafForestSplit.execution x (setPC s 445) (h.toCursor.withPC 445)
    hi range nodes code rfl select.final_bound
   let u:=UniformDirectLeafForestSplit.finished (setPC s 445)
   refine ⟨u,10,select.trans body,by simp only[operations,ite_eq_right stop];omega,?_,⟩
   refine ⟨rfl,UniformDirectLeafForestSplit.nextCursor hi (h.toCursor.withPC 445) stop,?_,?_,fun impossible=>False.elim (stop impossible)⟩
   · constructor
     · intro a _;rfl
     · intro a _ _ outside
       rw[UniformDirectLeafForestSplit.heap (h.toCursor.withPC 445)]
       simp (disch:=omega) [UniformDirectLeafForestCapture.outputHeap,setPC]
     · intro a high
       rw[UniformDirectLeafForestSplit.heap (h.toCursor.withPC 445)]
       have bound:p.ranges+2*i+2≤a:=by
        have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;have:=l.cacheEnd;have:=l.descriptors;omega
       simp (disch:=omega) [UniformDirectLeafForestCapture.outputHeap,setPC]
     · rfl
     · rfl
   · constructor
     · rw[UniformDirectLeafForestSplit.heap (h.toCursor.withPC 445)]
       simp [UniformDirectLeafForestCapture.outputHeap,setPC]
     · rw[UniformDirectLeafForestSplit.heap (h.toCursor.withPC 445)]
       simp [UniformDirectLeafForestCapture.outputHeap,operations,stop,setPC]
end
end ExactFourierCircuits.UniformDirectLeafForestRow
