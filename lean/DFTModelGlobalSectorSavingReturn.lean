import DFTModelGlobalSectorSavingGather

set_option autoImplicit false

/-! The original reverse literal34 consumes the actual closed child result.
Its caller must still establish the real return header and readonly spectator
cells. This theorem does not insert source header writes or close that caller. -/
namespace ExactFourierCircuits.DFTModelGlobalSectorSaving
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource DFTModelSectorTranspose
noncomputable section

structure Returned {n : ℕ} (g : Native.Geometry DFTModelSavingNativeRoot.W true)
 (old child : Tape Tagged.T) (x : Fin n→ℂ) (s s0 v v0 : State) : Prop where
 actual : BoundedExecution (UniformSectorTransposeMachine.programFor DFTModelSavingNativeRoot.W true)
   n x g.B (UniformTensorMonomialMachine.setPC s 0)
   (DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17) v
 baseline : BoundedExecution (UniformSectorTransposeMachine.programFor DFTModelSavingNativeRoot.W true)
   n (fun _=>0) g.B (UniformTensorMonomialMachine.setPC s0 0)
   (DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17) v0
 matched : StateMatch v v0
 frame : Native.Frame s v
 frame0 : Native.Frame s0 v0
 outside : Native.Outside g s.scalarHeap v
 outside0 : Native.Outside g s0.scalarHeap v0
 values : ∀r,r<DFTModelSavingNativeRoot.W→∀j,j<g.volume→∃a a0,
   v.scalarHeap (g.native+r*g.volume+j)=some a ∧
   v0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
   (run (reader Tagged) ((run (scatter Tagged)
     (((DFTModelSavingNativeRoot.W,(g.volume,(g.sector.start,g.sector.width))),old),child)).val,
     r*g.volume+j)).val=encodePaired a a0
 valid : (run (scatter Tagged)
   (((DFTModelSavingNativeRoot.W,(g.volume,(g.sector.start,g.sector.width))),old),child)).valid
 work : (run (scatter Tagged)
   (((DFTModelSavingNativeRoot.W,(g.volume,(g.sector.start,g.sector.width))),old),child)).work≤
   2*(DFTModelSavingNativeRoot.W*(7*g.sector.width+12)+17)
 peak : (run (scatter Tagged)
   (((DFTModelSavingNativeRoot.W,(g.volume,(g.sector.start,g.sector.width))),old),child)).peak≤g.B

/-- The child source and encoded patch are derived from its actual execution
result. Only ordinary original-return entry metadata and physical spectators
remain as caller obligations. The whole Scalar, including its flag, is copied. -/
theorem scatter_execution {n B q A F K ticks : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {input input0 output output0 : Fin DFTModelSavingNativeRoot.W→Fin (2^q)→Scalar}
 (result : DFTModelSavingNativeRoot.Result n B q A F K x s s0 u u0 ticks
   input input0 output output0)
 (g : Native.Geometry DFTModelSavingNativeRoot.W true)
 (bound : g.B=B) (width : g.sector.width=2^q)
 (base : g.buffer+DFTModelSavingNativeRoot.W*g.sector.start=A)
 (old : Tape Tagged.T) (header : Native.Header g u)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell
   DFTModelSavingNativeRoot.W g.directory g.buffer g.ordinal g.sector u)
 (spectators : ∀r,r<DFTModelSavingNativeRoot.W→∀j,j<g.volume→
   j<g.sector.start ∨g.sector.start+g.sector.width≤j→
   ∃a a0,u.scalarHeap (g.native+r*g.volume+j)=some a ∧
   u0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
   old.look (r*g.volume+j) Tagged.blank=encodePaired a a0) :
 ∃v v0,Returned g old (paired output output0) x u u0 v v0 := by
 have source : Native.Source g (natural output)
   (UniformTensorMonomialMachine.setPC u 0) := by
   intro r hr j hj
   have hq : j<2^q := by omega
   simpa only [UniformSectorTransposeMachine.sourceAddress,ite_true,
     UniformTensorMonomialMachine.setPC,base,width,natural,natural_fin,hr,hq,
     ↓reduceDIte] using result.data ⟨r,hr⟩ ⟨j,hq⟩
 have source0 : Native.Source g (natural output0)
   (UniformTensorMonomialMachine.setPC u0 0) := by
   intro r hr j hj
   have hq : j<2^q := by omega
   simpa only [UniformSectorTransposeMachine.sourceAddress,ite_true,
     UniformTensorMonomialMachine.setPC,base,width,natural,natural_fin,hr,hq,
     ↓reduceDIte] using result.data0 ⟨r,hr⟩ ⟨j,hq⟩
 have encoded : ∀r,r<DFTModelSavingNativeRoot.W→∀j,j<g.sector.width→
   (paired output output0).look (r*g.sector.width+j) Tagged.blank=
   encodePaired (natural output r j) (natural output0 r j) := by
   intro r hr j hj
   have hq : j<2^q := by omega
   simpa only [width,natural,hr,hq,↓reduceDIte] using
     paired_lookup output output0 ⟨r,hr⟩ ⟨j,hq⟩
 obtain ⟨v,v0,actual,baseline,matched,frame,frame0,out,out0,values,
   _,_,valid,work,peak⟩ := actual_scatter g (natural output) (natural output0)
     old (paired output output0) x (UniformTensorMonomialMachine.setPC u 0)
     (UniformTensorMonomialMachine.setPC u0 0) (result.matched.withPC 0)
     ⟨header.volume,header.native,header.directory,header.ordinal⟩ cell source source0 encoded
     spectators rfl
     (by rw [bound];exact changePC_bound B u 0 result.actual.final_bound (by omega))
 exact ⟨v,v0,actual,baseline,matched,frame,frame0,out,out0,values,valid,work,peak⟩

theorem staged_work {n B q A F K ticks V a : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {input input0 output output0 : Fin DFTModelSavingNativeRoot.W→Fin (2^q)→Scalar}
 (bank : Tape Tagged.T) (roles : 1≤DFTModelSavingNativeRoot.W)
 (encoded : ∀r j,bank.look (r.val*V+a+j.val) Tagged.blank=
   encodePaired (input r j) (input0 r j))
 (result : DFTModelSavingNativeRoot.Result n B q A F K x s s0 u u0 ticks
   input input0 output output0) :
 (run saving ((q,Complex.I),((DFTModelSavingNativeRoot.W,(V,a)),bank))).work+
 (run (scatter Tagged)
   (((DFTModelSavingNativeRoot.W,(V,(a,2^q))),bank),paired output output0)).work≤
   (K+13)*(2*(DFTModelSavingNativeRoot.W*(7*2^q+12)+17)+9+ticks) := by
 have first := work bank rfl roles encoded result
 have second := scatter_native_work Tagged DFTModelSavingNativeRoot.W V a (2^q)
   bank (paired output output0)
 nlinarith

end
end ExactFourierCircuits.DFTModelGlobalSectorSaving
