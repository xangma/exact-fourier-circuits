import DFTModelGlobalSectorSavingValue

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorSaving
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
open DFTModelSectorTranspose
noncomputable section

lemma cursor_transfer {M E F i : ℕ} {s u : State}
 (cursor : UniformSameProgramSectorLoop.Cursor M E F i s) (frame : Native.Frame s u) :
 UniformSameProgramSectorLoop.Cursor M E F i u := by
 constructor
 all_goals rw [frame.2.2.2.2 _ (Or.inr (by omega)) (Or.inr (by omega))]
 all_goals first | exact cursor.count | exact cursor.one | exact cursor.index |
   exact cursor.directory | exact cursor.fresh | exact cursor.zero | exact cursor.five

/-- Actual literal34 gather followed at the original sector-child call site
by the actual setup9 and closed child. The two call-site PCs are explicit;
this is not a proof of the still-unjoined outer caller or return cursor. -/
theorem gather_execution {n : ℕ}
 (g : Native.Geometry DFTModelSavingNativeRoot.W false) (M F K : ℕ)
 (bank : Tape Tagged.T) (x : Fin n→ℂ) (s s0 : State)
 (input input0 : Fin DFTModelSavingNativeRoot.W→Fin (2^g.sector.pairs)→Scalar)
 (same : StateMatch s s0) (header : Native.Header g s)
 (cursor : UniformSameProgramSectorLoop.Cursor M g.directory F g.ordinal s)
 (hi : g.ordinal<M)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell
   DFTModelSavingNativeRoot.W g.directory g.buffer g.ordinal g.sector s)
 (width : g.sector.width=2^g.sector.pairs)
 (data : Native.Source g (natural input) s)
 (data0 : Native.Source g (natural input0) s0)
 (encoded : ∀r j,bank.look (r.val*g.volume+g.sector.start+j.val) Tagged.blank=
   encodePaired (input r j) (input0 r j))
 (base : 3≤g.buffer+DFTModelSavingNativeRoot.W*g.sector.start)
 (extent : g.buffer+DFTModelSavingNativeRoot.W*g.sector.start+
   DFTModelSavingNativeRoot.W*2^g.sector.pairs≤F)
 (directoryFit : g.directory+5*M≤g.B)
 (code : UniformSameProgramSectorLoop.program.length≤g.B)
 (room : F+34*(g.sector.pairs+1)+DFTModelSavingNativeRoot.R.reserve*
   (g.sector.pairs+1)*2^g.sector.pairs≤g.B)
 (square : (2^g.sector.pairs)^2≤g.B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K)
 (roles : 1≤DFTModelSavingNativeRoot.W)
 (constants : UniformBinaryCStageMachine.Constants s)
 (pc : s.pc=0) (wb : WordBound g.B s) :
 ∃v v0 u u0 ticks output output0,
 BoundedExecution (UniformSectorTransposeMachine.programFor DFTModelSavingNativeRoot.W false)
   n x g.B s (DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17) v ∧
 BoundedExecution (UniformSectorTransposeMachine.programFor DFTModelSavingNativeRoot.W false)
   n (fun _=>0) g.B s0 (DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17) v0 ∧
 StateMatch v v0 ∧ Native.Frame s v ∧ Native.Frame s0 v0 ∧
 Native.Outside g s.scalarHeap v ∧ Native.Outside g s0.scalarHeap v0 ∧
 BoundedRuns UniformSameProgramSectorLoop.program n x g.B (setPC v 8) (9+ticks)
   (setPC u (17+UniformRecursiveSavingProgram.program.length)) ∧
 BoundedRuns UniformSameProgramSectorLoop.program n (fun _=>0) g.B (setPC v0 8) (9+ticks)
   (setPC u0 (17+UniformRecursiveSavingProgram.program.length)) ∧
 DFTModelSavingNativeRoot.Result n g.B g.sector.pairs
   (g.buffer+DFTModelSavingNativeRoot.W*g.sector.start) F K x
   (ready (setPC v 8)) (ready (setPC v0 8)) u u0 ticks input input0 output output0 ∧
 (run saving ((g.sector.pairs,Complex.I),
   ((DFTModelSavingNativeRoot.W,(g.volume,g.sector.start)),bank))).val=
   ((((g.sector.pairs,Complex.I),
     ((DFTModelSavingNativeRoot.W,(g.volume,g.sector.start)),bank)),2^g.sector.pairs),
     paired output output0) ∧
 (run saving ((g.sector.pairs,Complex.I),
   ((DFTModelSavingNativeRoot.W,(g.volume,g.sector.start)),bank))).valid ∧
 (run saving ((g.sector.pairs,Complex.I),
   ((DFTModelSavingNativeRoot.W,(g.volume,g.sector.start)),bank))).work≤
   (K+11)*(DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17+9+ticks) := by
 obtain ⟨v,v0,actual,baseline,matched,_,_,filled,filled0,frame,frame0,out,out0⟩ :=
   paired_transpose g (natural input) (natural input0) x s s0 same header cell data data0 pc wb
 have inputV : UniformFixedNetworkShearChildMachine.Present
   (g.buffer+DFTModelSavingNativeRoot.W*g.sector.start)
   DFTModelSavingNativeRoot.W (2^g.sector.pairs) input (setPC v 8) := by
   intro r j
   simpa only [UniformSectorTransposeMachine.targetAddress,Bool.false_eq_true,ite_false,
     UniformTensorMonomialMachine.setPC,width,natural_fin] using
     filled r.val r.isLt j.val (by rw [width];exact j.isLt)
 have inputV0 : UniformFixedNetworkShearChildMachine.Present
   (g.buffer+DFTModelSavingNativeRoot.W*g.sector.start)
   DFTModelSavingNativeRoot.W (2^g.sector.pairs) input0 (setPC v0 8) := by
   intro r j
   simpa only [UniformSectorTransposeMachine.targetAddress,Bool.false_eq_true,ite_false,
     UniformTensorMonomialMachine.setPC,width,natural_fin] using
     filled0 r.val r.isLt j.val (by rw [width];exact j.isLt)
 have cv := cursor_transfer cursor frame
 have cursorV : UniformSameProgramSectorLoop.Cursor M g.directory F g.ordinal (setPC v 8) :=
   ⟨cv.count,cv.one,cv.index,cv.directory,cv.fresh,cv.zero,cv.five⟩
 have cellV : UniformSectorBatchDirectoryMachine.BatchCell
   DFTModelSavingNativeRoot.W g.directory g.buffer g.ordinal g.sector (setPC v 8) := by
   simpa only [UniformSectorBatchDirectoryMachine.BatchCell,
     UniformTensorMonomialMachine.setPC,frame.1] using cell
 have keep : ∀a,a<3→v.scalarHeap a=s.scalarHeap a := by
   intro a ha
   apply out
   intro r _
   left
   change a<g.buffer+DFTModelSavingNativeRoot.W*g.sector.start+r*g.sector.width
   omega
 have constantsV : UniformBinaryCStageMachine.Constants (setPC v 8) := by
   constructor
   · exact (keep 1 (by omega)).trans constants.1
   · exact (keep 2 (by omega)).trans constants.2
 obtain ⟨u,u0,ticks,output,output0,run,run0,result⟩ := execution n g.B M g.directory
   g.buffer F g.ordinal K g.sector x (setPC v 8) (setPC v0 8) input input0
   (matched.withPC 8) cursorV hi cellV width inputV inputV0 base extent directoryFit code
   room square cap constantsV rfl
   (changePC_bound g.B v 8 actual.final_bound (by have:=g.code;omega))
 refine ⟨v,v0,u,u0,ticks,output,output0,actual,baseline,matched,frame,frame0,out,out0,
   run,run0,result,value bank rfl encoded result,saving_valid _ _ _ _ _ _,?_⟩
 simpa only [width] using work bank rfl roles encoded result

end
end ExactFourierCircuits.DFTModelGlobalSectorSaving
