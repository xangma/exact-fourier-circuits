import UniformDirectLeafForestLeafEnd
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestLeafStep
open UniformMachine UniformTensorMonomialMachine
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestControl
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration UniformDirectLeafForestLeafEnd
noncomputable section

structure StepFrame(p:Parameters)(visits:List Visit)(i:ℕ)(s u:State):Prop where
 scalarOutside:∀a,(a<(position p visits i).pool∨(position p visits (i+1)).pool≤a)→u.scalarHeap a=s.scalarHeap a
 natBefore:∀a,a<(position p visits i).permutation→(a<p.start.rows∨p.start.rows+3≤a)→
  (a<p.ranges+2*i∨p.ranges+2*i+2≤a)→u.natHeap a=s.natHeap a
 natHigh:∀a,p.transpose+4*p.radix^2≤a→u.natHeap a=s.natHeap a
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma frame {p:Parameters}{visits:List Visit}{i A C D:ℕ}{s u:State}
 (hi:i<visits.length)(stop:leaf visits[i])(positive:2≤p.radix)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D (p.transpose+4*size visits[i].task.width) p.radix A C (qs p A visits[i]) positive s u)
 (ctrl:Control p visits i (setPC u 436))
 (rangeEnd:p.ranges+2*visits.length≤p.start.permutation)
 (cacheEnd:p.start.permutation+(3*p.radix+11)*demand visits≤p.forward)
 (descriptors:p.forward+4*p.radix^2≤p.transpose)
 (extent:visits[i].task.width≤p.radix):StepFrame p visits i s (finished u):=by
 have following:=before_next visits i hi
 rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop] at following
 have bound:size visits[i].task.width≤p.radix^2:=by
  have h:=UniformJointCacheTime.leaf_records_bound visits[i].task.width 0 0
  rw[UniformTransposeDescriptorMachine.leafRecords_length] at h
  exact h.trans (Nat.pow_le_pow_left extent 2)
 constructor
 · intro a outside
   apply res.scalarOutside a
   simpa only[UniformDirectLeafForestForward.config,slot,count,position,following,Nat.mul_add,Nat.add_assoc] using outside
 · intro a lower outside range
   rw[rangeHeap hi positive res ctrl]
   have out:UniformDirectLeafForestCapture.outputHeap u.natHeap p.ranges i
    (position p visits i).entry (size visits[i].task.width) a=u.natHeap a:=by
     simp (disch:=omega) [UniformDirectLeafForestCapture.outputHeap]
   rw[out]
   exact res.natBefore a lower outside
 · intro a high
   rw[rangeHeap hi positive res ctrl]
   have rangeBound:p.ranges+2*i+2≤a:=by
    have:=before_le visits i
    omega
   simpa (disch:=omega) [UniformDirectLeafForestCapture.outputHeap] using res.natHigh a (by omega)
 · exact res.outputs
 · exact res.roots

/-- The actual cache helper is followed by charged measured-range capture,
loop jump, and persistent cursor advance. -/
theorem finish_execution {p:Parameters}{visits:List Visit}{i A C D n B:ℕ}
 (x:Fin n→ℂ)(s u:State)(hi:i<visits.length)(stop:leaf visits[i])(positive:2≤p.radix)
 (res:UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
 D (p.transpose+4*size visits[i].task.width) p.radix A C (qs p A visits[i]) positive s u)
 (ctrl:Control p visits i (setPC u 436))
 (range:p.ranges+2*visits.length≤B)
 (ordinal:p.rectangles+demand visits≤B)
 (nodeEnd:p.nodes+7*visits.length≤B)(code:461≤B)(wb:WordBound B (setPC u 436)):
 BoundedRuns UniformDirectLeafForestProgram.program n x B (setPC u 436) 12 (finished u):=by
 have cnt:(setPC u 436).natReg 6628=size visits[i].task.width:=by simpa only[setPC,count] using res.controls.count
 have stride:(setPC u 436).natReg 6634=3*p.radix+11:=res.controls.natStride
 have entry:(setPC u 436).natReg 6609=(position p visits i).entry+(3*p.radix+11)*size visits[i].task.width:=by
  simpa only[setPC,UniformDirectLeafForestForward.config,slot,count] using res.args.entry
 have following:=before_next visits i hi
 rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop] at following
 have ord:p.rectangles+before visits i+size visits[i].task.width≤B:=by
  have:=before_le visits (i+1);omega
 have cap:=UniformDirectLeafForestCapture.execution x (setPC u 436) ctrl cnt stride entry hi range ord code rfl wb
 let a:=UniformDirectLeafForestCapture.captured (setPC u 436)
 have ap:a.pc=444:=by
  simp only[a,UniformDirectLeafForestCapture.captured,applyBlock_pc,
   UniformDirectLeafForestProgram.capture_length,setPC]
 have bound:=changePC_bound B a 450 cap.final_bound (by omega)
 have jump:BoundedRuns UniformDirectLeafForestProgram.program n x B a 1 (setPC a 450):=
  .next cap.final_bound (by simp[UniformMachine.step,ap,UniformDirectLeafForestProgram.skip_at,setPC]) (.refl bound)
 have keep(j:ℕ)(n0:j≠6680)(n2:j≠6682)(n3:j≠6683):
  (setPC a 450).natReg j=(setPC u 436).natReg j:=by
  simp [a,UniformDirectLeafForestCapture.captured,UniformDirectLeafForestProgram.capture,
   applyBlock,Op.apply,writeNat,next,setPC,n0,n2,n3]
 have seven:(setPC a 450).natReg 6671=7:=(keep _ (by omega) (by omega) (by omega)).trans ctrl.seven
 have one:(setPC a 450).natReg 6669=1:=(keep _ (by omega) (by omega) (by omega)).trans ctrl.one
 have pointer:(setPC a 450).natReg 6663+7≤B:=by
  rw[keep _ (by omega) (by omega) (by omega),ctrl.pointer];omega
 have index:(setPC a 450).natReg 6662+1≤B:=by
  have countBound:=wb.2.1 6661;rw[ctrl.count] at countBound
  rw[keep _ (by omega) (by omega) (by omega),ctrl.index];omega
 have advance:=UniformDirectLeafForestAdvance.execution x (setPC a 450) seven one pointer index code rfl bound
 simpa only[finished,a] using (cap.trans jump).trans advance
end
end ExactFourierCircuits.UniformDirectLeafForestLeafStep
