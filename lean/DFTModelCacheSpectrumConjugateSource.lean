import DFTModelCacheSpectrumConjugateProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheSpectrumConjugate
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelCacheSpectrum.program

theorem spectrum_star_run (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) :
    run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,star z))=
      DFTModelConjugation.bill (Tape.map star)
        (run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,z))) := by
  simpa only [DFTModelConjugation.value,DFTModelCacheDisplacement.metadata] using
    (DFTModelConjugation.program_run DFTModelCacheSpectrum.program
      (DFTModelCacheDisplacement.metadata r p,(D,z)))

theorem spectrum_inverse_run (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hz : ‖z‖=1) :
    run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,z⁻¹))=
      DFTModelConjugation.bill (Tape.map star)
        (run DFTModelCacheSpectrum.program (DFTModelCacheDisplacement.metadata r p,(D,z))) := by
  rw [Complex.inv_eq_conj hz]
  exact spectrum_star_run r D p z

theorem canonical_norm (D : ℕ) : ‖OAI.ExactFourier.zeta D‖=1 := by
  simp [OAI.ExactFourier.zeta,Complex.norm_exp,Complex.div_re,Complex.mul_re,Complex.mul_im]

theorem zip_star_value (a : Tape ℂ) :
    (run zip (a,a.map star)).val=
      Tape.tab a.len (fun i=>(a.look i 0,star (a.look i 0))) := by
  rw [zip_value]
  congr 1
  funext i
  congr 1
  simpa only [star_zero] using DFTModelConjugation.map_look star a i (0:ℂ)

theorem program_value (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).val=
      Tape.tab (run DFTModelCacheSpectrum.program
        (DFTModelCacheDisplacement.metadata r p,(D,z))).val.len (fun i=>
          ((run DFTModelCacheSpectrum.program
            (DFTModelCacheDisplacement.metadata r p,(D,z))).val.look i 0,
            star ((run DFTModelCacheSpectrum.program
              (DFTModelCacheDisplacement.metadata r p,(D,z))).val.look i 0))) := by
  rw [program_run,spectrum_inverse_run r D p z hz]
  exact zip_star_value _

theorem program_length (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (z : ℂ) (hr : 0<r) (hz : ‖z‖=1) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).val.len=7*p.N := by
  rw [program_value r D p z hz]
  exact DFTModelCacheSpectrum.program_length r D p z hr

theorem tab_lookup {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (z : α) (hi : i<n) :
    (Tape.tab n f).look i z=f i := Tape.look_of_lt (Tape.tab n f) z hi

theorem program_sharedBank (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape : DFTModelCacheDisplacement.Shape p r) (K : ℕ)
    (width : p.N=UniformRadixTwoDAG.width K) (hD : 0<D)
    (radixDiv : r∣D) (fftDiv : UniformRadixTwoDAG.width K∣D)
    (i : Fin (UniformToeplitzCrossDAG.bankSize K)) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.look
      i.val (0,0)=
      (UniformToeplitzCrossDAG.sharedBank K
        (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i,
       star (UniformToeplitzCrossDAG.sharedBank K
        (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i)) := by
  have hr : 0<r := shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  have len:=DFTModelCacheSpectrum.program_length r D p (OAI.ExactFourier.zeta D) hr
  have hi : i.val < (run DFTModelCacheSpectrum.program
      (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.len := by
    rw [len,width]
    have bound:=i.isLt
    simp only [UniformToeplitzCrossDAG.bankSize] at bound
    omega
  rw [program_value r D p _ (canonical_norm D)]
  rw [tab_lookup _ _ _ _ hi]
  change (_,star _)=_
  rw [DFTModelCacheSpectrum.program_sharedBank r D p shape K width hD radixDiv fftDiv i]

theorem program_source (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape : DFTModelCacheDisplacement.Shape p r) (K : ℕ)
    (width : p.N=UniformRadixTwoDAG.width K) (hD : 0<D)
    (radixDiv : r∣D) (fftDiv : UniformRadixTwoDAG.width K∣D) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.len=
      UniformToeplitzCrossDAG.bankSize K ∧
    ∀i : Fin (UniformToeplitzCrossDAG.bankSize K),
      (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.look
        i.val (0,0)=
        (UniformToeplitzCrossDAG.sharedBank K
          (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i,
         star (UniformToeplitzCrossDAG.sharedBank K
          (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r)) i)) := by
  have hr : 0<r := shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  refine ⟨?_,program_sharedBank r D p shape K width hD radixDiv fftDiv⟩
  rw [program_length r D p _ hr (canonical_norm D),width]
  simp only [UniformToeplitzCrossDAG.bankSize]
  omega

end
end ExactFourierCircuits.DFTModelCacheSpectrumConjugate
