import DFTModelCacheSpectrumConjugateSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheSpectrumConjugate
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelCacheSpectrum.program

def workBudget (r D : ℕ) (p : UniformRankKernelMachine.Parameters) : ℕ :=
  2*(250*(r+1)^2+6*p.N*(52*p.split+300)+1200*(p.N+1)^2+
    40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/p.N+1)+1)+800)+133*p.N+20

theorem program_work_exact (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hr : 0<r) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).work=
      2*(run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,z))).work+
        133*p.N+20 := by
  rw [program_run]
  change (run DFTModelCacheSpectrum.program _).work+
    (run DFTModelCacheSpectrum.program _).work+(run zip _).work+14=_
  rw [zip_work,spectrum_inverse_run r D p z hz]
  change (run DFTModelCacheSpectrum.program _).work+
    (run DFTModelCacheSpectrum.program _).work+
      (19*(run DFTModelCacheSpectrum.program _).val.len+6)+14=_
  rw [DFTModelCacheSpectrum.program_length r D p z hr]
  omega

theorem program_work (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hr : 0<r) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).work≤workBudget r D p := by
  rw [program_work_exact r D p z hr hz]
  have h:=DFTModelCacheSpectrum.program_work r D p z hr
  unfold workBudget
  omega

theorem program_peak_exact (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hr : 0<r) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).peak=
      max (run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,z))).peak
        (7*p.N) := by
  rw [program_run]
  change max (run DFTModelCacheSpectrum.program _).peak
    (max (run DFTModelCacheSpectrum.program _).peak (run zip _).peak)=_
  rw [zip_peak,spectrum_inverse_run r D p z hz]
  change max (run DFTModelCacheSpectrum.program _).peak
    (max (run DFTModelCacheSpectrum.program _).peak (run DFTModelCacheSpectrum.program _).val.len)=_
  rw [DFTModelCacheSpectrum.program_length r D p z hr]
  omega

theorem program_peak (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (shape : DFTModelCacheDisplacement.Shape p r) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).peak≤
      max (D+2) (r+7*p.N+7) := by
  have hr : 0<r := shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  rw [program_peak_exact r D p z hr hz]
  have h:=DFTModelCacheSpectrum.program_peak r D p z shape
  omega

theorem program_valid (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (hr : 0<r) (hD : 0<D) (radixDiv : r∣D) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).valid := by
  have valid:=DFTModelCacheSpectrum.program_valid r D p hr hD radixDiv
  rw [program_run]
  refine ⟨valid,Complex.exp_ne_zero _,?_,zip_valid _ _⟩
  rw [spectrum_inverse_run r D p _ (canonical_norm D)]
  exact valid

theorem specification (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape : DFTModelCacheDisplacement.Shape p r) (K : ℕ)
    (width : p.N=UniformRadixTwoDAG.width K) (hD : 0<D)
    (radixDiv : r∣D) (fftDiv : UniformRadixTwoDAG.width K∣D) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.len=
      UniformToeplitzCrossDAG.bankSize K ∧
    (∀i : Fin (UniformToeplitzCrossDAG.bankSize K),
      (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.look
        i.val (0,0)=
        (UniformToeplitzCrossDAG.sharedBank K
          (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i,
         star (UniformToeplitzCrossDAG.sharedBank K
          (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i))) ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).valid ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).work≤
      workBudget r D p ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).peak≤
      max (D+2) (r+7*p.N+7) := by
  have hr : 0<r := shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  have source:=program_source r D p shape K width hD radixDiv fftDiv
  exact ⟨source.1,source.2,program_valid r D p hr hD radixDiv,
    program_work r D p _ hr (canonical_norm D),program_peak r D p _ shape (canonical_norm D)⟩

end
end ExactFourierCircuits.DFTModelCacheSpectrumConjugate
