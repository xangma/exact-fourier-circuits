import DFTModelCacheRectanglePreparationProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDescriptor (rowEncode)
noncomputable section
attribute [local irreducible] program DFTModelCacheSpectrum.program

theorem metadata_value (r : ℕ) (q : UniformLocalRectangleDescriptors.Row) :
    DFTModelCacheDisplacement.metadata r (parameters r q)=
      (r,((q.a,q.e),((q.i0,q.j0),(q.split,2^Nat.clog 2 (2*(q.a+q.e)))))) := by
  simp only [DFTModelCacheDisplacement.metadata,parameters,width,
    UniformRadixTwoDAG.width_eq,height,UniformWorkspacePlanner.exponent]

theorem program_value (r D : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    (run program ((r,rowEncode q),(D,z))).val=
      (rowEncode q,(height q,
        (run DFTModelCacheSpectrum.program
          (DFTModelCacheDisplacement.metadata r (parameters r q),(D,z))).val)) := by
  rw [program_run]
  obtain ⟨logValue,_,_,_⟩:=DFTModelCacheDescriptor.logarithm_spec (2*(q.a+q.e))
  change (rowEncode q,((run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).val.1,
    (run DFTModelCacheSpectrum.program
      ((r,((q.a,q.e),((q.i0,q.j0),(q.split,
        (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).val.2)))),(D,z))).val))=_
  rw [logValue]
  rw [metadata_value]
  rfl

theorem program_valid {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row}
    (source : ProducedRow r q) (master : Master r D) :
    (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).valid := by
  rw [program_run]
  obtain ⟨lv,ld,_,_⟩:=DFTModelCacheDescriptor.logarithm_spec (2*(q.a+q.e))
  refine ⟨ld,?_,trivial⟩
  rw [lv]
  simpa only [metadata_value] using DFTModelCacheSpectrum.program_valid r D (parameters r q)
    (by have h:=(produced_shape source).positiveA;have g:=(produced_shape source).hRows;omega)
    master.positive master.radixDiv

theorem program_sharedBank {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row}
    (source : ProducedRow r q) (master : Master r D)
    (i : Fin (UniformToeplitzCrossDAG.bankSize (height q))) :
    (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).val.2.2.look i.val 0=
      UniformToeplitzCrossDAG.sharedBank (height q)
        (DFTModelCacheSpectrum.rankKernels r (parameters r q) (height q)
          (OAI.ExactFourier.zeta r)) i := by
  rw [program_value]
  exact DFTModelCacheSpectrum.program_sharedBank r D (parameters r q)
    (produced_shape source) (height q) rfl master.positive master.radixDiv
    (produced_divisor source master) i

theorem program_length {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row} (z : ℂ)
    (source : ProducedRow r q) :
    (run program ((r,rowEncode q),(D,z))).val.2.2.len=7*width q := by
  rw [program_value]
  exact DFTModelCacheSpectrum.program_length r D (parameters r q) z
    (by have h:=(produced_shape source).positiveA;have g:=(produced_shape source).hRows;omega)

theorem program_work {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row} (z : ℂ)
    (source : ProducedRow r q) :
    (run program ((r,rowEncode q),(D,z))).work≤
      100100*(r+1)^2+40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/width q+1)+1) := by
  rw [program_run]
  obtain ⟨lv,_,lw,_⟩:=DFTModelCacheDescriptor.logarithm_spec (2*(q.a+q.e))
  have work:=DFTModelCacheSpectrum.program_axis_work r D (parameters r q) z
    (produced_shape source) (produced_width source).2.2
  have hk:=produced_height source
  have logBound:=UniformWorkspaceSearchMachine.clog_bound r
  have hr:1≤r:=by
    have h:=(produced_shape source).positiveA
    have g:=(produced_shape source).hRows
    omega
  change (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).work+
    ((run DFTModelCacheSpectrum.program
      ((r,((q.a,q.e),((q.i0,q.j0),(q.split,
        (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).val.2)))),(D,z))).work+1)+132≤_
  rw [lv,lw]
  change 28*height q+23+(_+1)+132≤_
  change (run DFTModelCacheSpectrum.program
    ((r,((q.a,q.e),((q.i0,q.j0),(q.split,width q)))),(D,z))).work≤
      100000*(r+1)^2+40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/width q+1)+1) at work
  simp only [width,UniformRadixTwoDAG.width_eq,height,UniformWorkspacePlanner.exponent] at work hk ⊢
  nlinarith

theorem program_peak {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row} (z : ℂ)
    (source : ProducedRow r q) :
    (run program ((r,rowEncode q),(D,z))).peak ≤ max (D+2) (r+7*width q+7) := by
  rw [program_run]
  obtain ⟨lv,_,_,lp⟩:=DFTModelCacheDescriptor.logarithm_spec (2*(q.a+q.e))
  have spec:=DFTModelCacheSpectrum.program_peak r D (parameters r q) z (produced_shape source)
  have noAlias:=UniformWorkspacePlanner.no_alias q.a q.e
  change 2*(q.a+q.e)≤2^height q at noAlias
  change max (max (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).peak
    (max (run DFTModelCacheSpectrum.program
      ((r,((q.a,q.e),((q.i0,q.j0),(q.split,
        (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).val.2)))),(D,z))).peak 0))
      (max 2 (2*(q.a+q.e)))≤_
  rw [lv]
  change (run DFTModelCacheSpectrum.program
    ((r,((q.a,q.e),((q.i0,q.j0),(q.split,width q)))),(D,z))).peak≤_ at spec
  simp only [parameters,width,UniformRadixTwoDAG.width_eq,height,UniformWorkspacePlanner.exponent] at spec noAlias ⊢
  omega

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
