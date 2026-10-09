import UniformDirectLeafForestLeafCall
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestLeafEnd
open UniformMachine UniformTensorMonomialMachine
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestControl
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource
open UniformDirectLeafCacheLoopBoot UniformLocalCacheTreeMachine
noncomputable section

def finished(u:State):State:=UniformDirectLeafForestAdvance.advanced
 (setPC (UniformDirectLeafForestCapture.captured (setPC u 436)) 450)

def qs(p:Parameters)(A:ℕ)(q:Visit):List UniformTransposeDescriptorMachine.Record:=
 records q.task.width q.task.offset (A+3*p.radix) 0

lemma count(p:Parameters)(A:ℕ)(q:Visit):(qs p A q).length=size q.task.width:=records_length _ _ _ _

lemma endCore {p:Parameters}{visits:List Visit}{i D H A C:ℕ}{s u:State}
 (hi:i<visits.length)(stop:leaf visits[i])(positive:2≤p.radix)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D H p.radix A C (qs p A visits[i]) positive s u):
 Core (position p visits (i+1)) u:=by
 have following:=before_next visits i hi
 rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop] at following
 constructor
 · exact res.args.originalDirectory
 · exact res.args.conjugateDirectory
 · convert res.args.pool using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring
 · exact res.args.rows
 · convert res.args.permutation using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring
 · convert res.args.widths using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring
 · convert res.args.markers using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring
 · convert res.args.axis using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring
 · convert res.args.entry using 1
   simp only[position,UniformDirectLeafForestForward.config,slot,count]
   rw[following];ring

lemma nextCursor {p:Parameters}{visits:List Visit}{i D H A C:ℕ}{s u:State}
 (hi:i<visits.length)(stop:leaf visits[i])(positive:2≤p.radix)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D H p.radix A C (qs p A visits[i]) positive s u)
 (ctrl:Control p visits i (setPC u 436)):
 Cursor p visits (i+1) (finished u):=by
 have following:=before_next visits i hi
 rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop] at following
 have cnt:(setPC u 436).natReg 6628=size visits[i].task.width:=by
  simpa only[count,setPC] using res.controls.count
 have nc:=UniformDirectLeafForestAdvance.captured_control ctrl cnt following
 apply cursor nc
 exact UniformDirectLeafForestAdvance.core
  ((UniformDirectLeafForestCapture.core ((endCore hi stop positive res).withPC 436)).withPC 450)

lemma rangeHeap {p:Parameters}{visits:List Visit}{i D H A C:ℕ}{s u:State}
 (hi:i<visits.length)(positive:2≤p.radix)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D H p.radix A C (qs p A visits[i]) positive s u)
 (ctrl:Control p visits i (setPC u 436)):
 (finished u).natHeap=UniformDirectLeafForestCapture.outputHeap u.natHeap p.ranges i
  (position p visits i).entry (size visits[i].task.width):=by
 apply UniformDirectLeafForestCapture.heap ctrl
 · simpa only[count,setPC] using res.controls.count
 · exact res.controls.natStride
 · simpa only[setPC,UniformDirectLeafForestForward.config,slot,count] using res.args.entry

lemma events {p:Parameters}{visits:List Visit}{i A C B D H:ℕ}{s u:State}
 (hi:i<visits.length)(stop:leaf visits[i])(positive:2≤p.radix)
 (l:UniformDirectLeafForestGeometry.Layout p A C B visits)
 (rangeEnd:p.ranges+2*visits.length≤p.start.permutation)
 (extent:visits[i].task.offset+visits[i].task.width≤p.radix)
 (duration:visits[i].task.width+14*visits[i].task.width*(visits[i].task.width-1)≤p.rootDuration)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D H p.radix A C (qs p A visits[i]) positive s u)
 (ctrl:Control p visits i (setPC u 436)):
 ∀j (hj:j<(qs p A visits[i]).length),Nonempty
 (UniformDirectLeafCacheSemanticExecution.SemanticResult
  (slot (UniformDirectLeafForestForward.config p visits i) p.radix (qs p A visits[i]) j)
  p.radix (qs p A visits[i])[j]
  (UniformDirectLeafCacheSource.mu p.radix (A+3*p.radix) (qs p A visits[i])[j]) positive (finished u)):=by
 have hl:=UniformDirectLeafForestGeometry.phase_layout l hi stop (by omega) duration
 intro j hj
 obtain ⟨event⟩:=res.events j hj
 apply Nonempty.intro
 apply UniformDirectLeafCacheSemanticRetention.result event
  (UniformDirectLeafHighGeometry.slot_layout hl j hj)
  ((records_valid _ _ _ _ p.radix (by omega) _ (List.getElem_mem hj)).1.1)
  ((records_valid _ _ _ _ p.radix (by omega) _ (List.getElem_mem hj)).1.2.1)
 · intro a _ _;rfl
 · intro a lower _
   rw[rangeHeap hi positive res ctrl]
   apply show UniformDirectLeafForestCapture.outputHeap u.natHeap p.ranges i
     (position p visits i).entry (size visits[i].task.width) a=u.natHeap a from ?_
   have high:p.ranges+2*i+2≤p.start.permutation:=by omega
   have before:p.start.permutation≤a:=by
    simp only[slot,UniformDirectLeafForestForward.config,position] at lower
    omega
   simp (disch:=omega) [UniformDirectLeafForestCapture.outputHeap]
end
end ExactFourierCircuits.UniformDirectLeafForestLeafEnd
