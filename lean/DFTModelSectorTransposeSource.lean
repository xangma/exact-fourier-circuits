import DFTModelSectorTransposeProgram
import DFTModelSectorTransposeOverlay
import DFTModelRecursiveScalarSource
import UniformSectorTransposeMachine

set_option autoImplicit false

/-! Actual literal34 execution correspondence. Both source witnesses retain the
complete Scalar tags; the typed program moves one paired element per cell. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
open DFTModelAdmissibilityControl
namespace Native
abbrev Geometry := UniformSectorTransposeMachine.Geometry
abbrev Source {W : ℕ} {inverse : Bool} := UniformSectorTransposeMachine.Source (W:=W) (inverse:=inverse)
abbrev Filled {W : ℕ} {inverse : Bool} := UniformSectorTransposeMachine.Filled (W:=W) (inverse:=inverse)
abbrev Header {W : ℕ} {inverse : Bool} := UniformSectorTransposeMachine.Header (W:=W) (inverse:=inverse)
abbrev Frame := UniformSectorTransposeMachine.Frame
abbrev Outside {W : ℕ} {inverse : Bool} := UniformSectorTransposeMachine.Outside (W:=W) (inverse:=inverse)
end Native
noncomputable section

theorem paired_transpose {W n : ℕ} {inverse : Bool}
 (g : Native.Geometry W inverse) (f f0 : ℕ→ℕ→Scalar)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (header : Native.Header g s)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (data : Native.Source g f s) (data0 : Native.Source g f0 s0)
 (pc : s.pc=0) (wb : WordBound g.B s) :
 ∃u u0,
 BoundedExecution (UniformSectorTransposeMachine.programFor W inverse) n x g.B s
  (W*(7*g.sector.width+12)+17) u ∧
 BoundedExecution (UniformSectorTransposeMachine.programFor W inverse) n (fun _=>0) g.B s0
  (W*(7*g.sector.width+12)+17) u0 ∧
 StateMatch u u0 ∧ u.pc=33 ∧ u0.pc=33 ∧
 Native.Filled g f W u ∧ Native.Filled g f0 W u0 ∧
 Native.Frame s u ∧ Native.Frame s0 u0 ∧
 Native.Outside g s.scalarHeap u ∧ Native.Outside g s0.scalarHeap u0 := by
 have header0 : Native.Header g s0 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [same.natReg]; exact header.volume
  · rw [same.natReg]; exact header.native
  · rw [same.natReg]; exact header.directory
  · rw [same.natReg]; exact header.ordinal
 have cell0 : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s0 := by
  simpa only [UniformSectorBatchDirectoryMachine.BatchCell,same.natHeap] using cell
 obtain ⟨u,actual,up,_,values,frame,out⟩ :=
  UniformSectorTransposeMachine.execution g f x s header cell data pc wb
 obtain ⟨u0,baseline,u0p,_,values0,frame0,out0⟩ :=
  UniformSectorTransposeMachine.execution g f0 (fun _=>0) s0 header0 cell0 data0
   (same.pc.trans pc) (same.wordBound wb)
 obtain ⟨u0',baseline',matched⟩ := boundedExecution_match (y:=fun _=>0) actual same
 have eq : u0'=u0 := (baseline'.executes.deterministic baseline.executes).2
 subst u0'
 exact ⟨u,u0,actual,baseline,matched,up,u0p,values,values0,frame,frame0,out,out0⟩

/-- One genuine complete child bank, including a charged runtime exponent loop.
The input equality describes the existing physical source cells only. -/
theorem actual_gather {W n : ℕ} (g : Native.Geometry W false)
 (f f0 : ℕ→ℕ→Scalar) (bank : Tape Tagged.T) (I : ℂ)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (header : Native.Header g s)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (data : Native.Source g f s) (data0 : Native.Source g f0 s0)
 (encoded : ∀r,r<W→∀j,j<g.sector.width→
  bank.look (r*g.volume+g.sector.start+j) Tagged.blank=encodePaired (f r j) (f0 r j))
 (width : g.sector.width=2^g.sector.pairs) (roles : 1≤W)
 (pc : s.pc=0) (wb : WordBound g.B s) :
 ∃u u0,
 BoundedExecution (UniformSectorTransposeMachine.programFor W false) n x g.B s
  (W*(7*g.sector.width+12)+17) u ∧
 BoundedExecution (UniformSectorTransposeMachine.programFor W false) n (fun _=>0) g.B s0
  (W*(7*g.sector.width+12)+17) u0 ∧
 StateMatch u u0 ∧ Native.Frame s u ∧ Native.Frame s0 u0 ∧
 Native.Outside g s.scalarHeap u ∧ Native.Outside g s0.scalarHeap u0 ∧
 (∀r,r<W→∀j,j<g.sector.width→
  u.scalarHeap (g.buffer+W*g.sector.start+r*g.sector.width+j)=some (f r j) ∧
  u0.scalarHeap (g.buffer+W*g.sector.start+r*g.sector.width+j)=some (f0 r j) ∧
  (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).val.2.2.look
   (r*g.sector.width+j) Tagged.blank=encodePaired (f r j) (f0 r j)) ∧
 (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).val.2.1=(g.sector.pairs,I) ∧
 (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).val.2.2.len=W*2^g.sector.pairs ∧
 (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).valid ∧
 (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).work≤
  10*(W*(7*g.sector.width+12)+17) ∧
 (run (argument Tagged) ((g.sector.pairs,I),((W,(g.volume,g.sector.start)),bank))).peak≤g.B := by
 obtain ⟨u,u0,actual,baseline,matched,_,_,values,values0,frame,frame0,out,out0⟩ :=
  paired_transpose g f f0 x s s0 same header cell data data0 pc wb
 refine ⟨u,u0,actual,baseline,matched,frame,frame0,out,out0,?_,?_,
  argument_length _ _ _ _ _ _ _,argument_valid _ _ _ _ _ _ _,?_,?_⟩
 · intro r hr j hj
   refine ⟨values r hr j hj,values0 r hr j hj,?_⟩
   rw [argument_value]
   change (gathered W g.volume g.sector.start (2^g.sector.pairs) bank Tagged.blank).look
    (r*g.sector.width+j) Tagged.blank=_
   rw [←width,←gather_value]
   exact (gather_lookup Tagged W g.volume g.sector.start g.sector.width r j bank hr hj).trans (encoded r hr j hj)
 · rw [argument_value]
 · have bound := argument_linear_work Tagged g.sector.pairs W g.volume g.sector.start I bank roles
   rw [←width] at bound
   nlinarith
 · exact (argument_peak Tagged g.sector.pairs W g.volume g.sector.start I bank roles
    (by rw [←width];exact g.fit)).trans (by have:=g.nativeFit;omega)

end
end ExactFourierCircuits.DFTModelSectorTranspose
