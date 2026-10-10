import DFTModelSectorTransposeSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
noncomputable section

/-- Reverse literal34 corresponds to a compact patch plus a readonly spectator
bank. The reader exposes exactly the actual returned Scalars, including tags. -/
theorem actual_scatter {W n : ℕ} (g : Native.Geometry W true)
 (f f0 : ℕ→ℕ→Scalar) (old child : Tape Tagged.T)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (header : Native.Header g s)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (data : Native.Source g f s) (data0 : Native.Source g f0 s0)
 (encoded : ∀r,r<W→∀j,j<g.sector.width→
  child.look (r*g.sector.width+j) Tagged.blank=encodePaired (f r j) (f0 r j))
 (spectators : ∀r,r<W→∀j,j<g.volume→j<g.sector.start ∨g.sector.start+g.sector.width≤j→
  ∃a a0,s.scalarHeap (g.native+r*g.volume+j)=some a ∧
  s0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
  old.look (r*g.volume+j) Tagged.blank=encodePaired a a0)
 (pc : s.pc=0) (wb : WordBound g.B s) :
 ∃u u0,
 BoundedExecution (UniformSectorTransposeMachine.programFor W true) n x g.B s
  (W*(7*g.sector.width+12)+17) u ∧
 BoundedExecution (UniformSectorTransposeMachine.programFor W true) n (fun _=>0) g.B s0
  (W*(7*g.sector.width+12)+17) u0 ∧
 StateMatch u u0 ∧ Native.Frame s u ∧ Native.Frame s0 u0 ∧
 Native.Outside g s.scalarHeap u ∧ Native.Outside g s0.scalarHeap u0 ∧
 (∀r,r<W→∀j,j<g.volume→∃a a0,
  u.scalarHeap (g.native+r*g.volume+j)=some a ∧
  u0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
  (run (reader Tagged) ((run (scatter Tagged)
    (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).val,r*g.volume+j)).val=
   encodePaired a a0) ∧
 (run (scatter Tagged) (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).val.1=
  ((W,(g.volume,(g.sector.start,g.sector.width))),old) ∧
 (run (scatter Tagged) (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).val.2.len=
  W*g.sector.width ∧
 (run (scatter Tagged) (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).valid ∧
 (run (scatter Tagged) (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).work≤
  2*(W*(7*g.sector.width+12)+17) ∧
 (run (scatter Tagged) (((W,(g.volume,(g.sector.start,g.sector.width))),old),child)).peak≤g.B := by
 obtain ⟨u,u0,actual,baseline,matched,_,_,values,values0,frame,frame0,out,out0⟩ :=
  paired_transpose g f f0 x s s0 same header cell data data0 pc wb
 refine ⟨u,u0,actual,baseline,matched,frame,frame0,out,out0,?_,
  scatter_retained _ _ _ _ _ _ _,scatter_length _ _ _ _ _ _ _,
  scatter_valid _ _ _ _ _ _ _,scatter_native_work _ _ _ _ _ _ _,?_⟩
 · intro r hr j hj
   by_cases before : j<g.sector.start
   · obtain ⟨a,a0,present,present0,paired⟩ := spectators r hr j hj (Or.inl before)
     refine ⟨a,a0,?_,?_,?_⟩
     · exact (UniformSectorTransposeMachine.native_spectators out r j hr hj (Or.inl before)).trans present
     · exact (UniformSectorTransposeMachine.native_spectators out0 r j hr hj (Or.inl before)).trans present0
     · rw [scatter_value,reader_value,overlay_spectator Tagged g.volume g.sector.start g.sector.width r j old _ hj (Or.inl before)]
       exact paired
   · by_cases after : g.sector.start+g.sector.width≤j
     · obtain ⟨a,a0,present,present0,paired⟩ := spectators r hr j hj (Or.inr after)
       refine ⟨a,a0,?_,?_,?_⟩
       · exact (UniformSectorTransposeMachine.native_spectators out r j hr hj (Or.inr after)).trans present
       · exact (UniformSectorTransposeMachine.native_spectators out0 r j hr hj (Or.inr after)).trans present0
       · rw [scatter_value,reader_value,overlay_spectator Tagged g.volume g.sector.start g.sector.width r j old _ hj (Or.inr after)]
         exact paired
     · let t := j-g.sector.start
       have inside : t<g.sector.width := by dsimp [t];omega
       have jt : j=g.sector.start+t := by dsimp [t];omega
       refine ⟨f r t,f0 r t,?_,?_,?_⟩
       · simpa only [UniformSectorTransposeMachine.targetAddress,ite_true,jt,Nat.add_assoc] using values r hr t inside
       · simpa only [UniformSectorTransposeMachine.targetAddress,ite_true,jt,Nat.add_assoc] using values0 r hr t inside
       · rw [scatter_value,reader_value]
         rw [show r*g.volume+j=r*g.volume+g.sector.start+t by omega]
         rw [overlay_sector Tagged g.volume g.sector.start g.sector.width r t old _ g.fit inside]
         have small : r*g.sector.width+t<W*g.sector.width := by nlinarith
         simpa only [Tape.look,Tape.tab,small,↓reduceDIte] using encoded r hr t inside
 · rw [scatter_peak]
   have width := Nat.mul_le_mul_left W (show g.sector.width≤g.volume by have:=g.fit;omega)
   have endFit := g.nativeFit
   omega

end
end ExactFourierCircuits.DFTModelSectorTranspose
