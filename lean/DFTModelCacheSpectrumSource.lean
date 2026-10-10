import DFTModelCacheSpectrumClosed
import DFTModelCacheDisplacementCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSpectrum
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def rankKernels (_r : ℕ) (p : UniformRankKernelMachine.Parameters) (K : ℕ) (omega : ℂ) :=
  UniformToeplitzCrossDAG.rankKernels K p.a p.e
    (UniformRankKernelMachine.matrixValue p (fun i=>PowerSeries.coeff i (OAI.ExactFourier.NewtonFourier.invH omega))
      (DFTModelCacheKernelNewton.gValue omega))
    (UniformRankKernelMachine.vValue p (fun i=>PowerSeries.coeff i (OAI.ExactFourier.NewtonFourier.invH omega)))
    (UniformRankKernelMachine.wValue p (DFTModelCacheKernelNewton.gValue omega))

/-- Exact original seven-block bank, including the six original rank kernels.
The only scalar entry is the one prepared canonical master root. -/
theorem program_sharedBank (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape:DFTModelCacheDisplacement.Shape p r) (K : ℕ)
    (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
    (radixDiv:r∣D) (fftDiv:UniformRadixTwoDAG.width K∣D)
    (i:Fin (UniformToeplitzCrossDAG.bankSize K)) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.look i.val 0=
      UniformToeplitzCrossDAG.sharedBank K (rankKernels r p K (OAI.ExactFourier.zeta r)) i := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  rw [program_run]
  change (run DFTModelCacheSpectrumMaster.program (p.N,(D,(OAI.ExactFourier.zeta D,
    (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,OAI.ExactFourier.zeta D))).val)).val)))).val.look i.val 0=_
  rw [DFTModelRootExtraction.divisor_root _ _ hr hD radixDiv]
  have h:=DFTModelCacheSpectrumMaster.source_sharedBank K D hD fftDiv
    (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,OAI.ExactFourier.zeta r)).val
    (rankKernels r p K (OAI.ExactFourier.zeta r))
    (fun b j=>DFTModelCacheDisplacement.program_rankKernels r p _ shape K width b j) i
  simpa only [width] using h

theorem program_length (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) (hr:0<r) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).val.len=7*p.N := by
  rw [program_value r D p z hr]
  rfl

/-- The selected FFT width is at most eight times the local radix. All
quadratic preparation is charged; no constant-factor native FFT claim is made. -/
theorem program_axis_work (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ)
    (shape:DFTModelCacheDisplacement.Shape p r) (width:p.N≤8*r) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).work≤
      100000*(r+1)^2+40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/p.N+1)+1) := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  have h:=program_work r D p z hr
  have split:=shape.gSplit
  nlinarith

theorem specification (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape:DFTModelCacheDisplacement.Shape p r) (K : ℕ)
    (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
    (radixDiv:r∣D) (fftDiv:UniformRadixTwoDAG.width K∣D) :
    (∀i:Fin (UniformToeplitzCrossDAG.bankSize K),
      (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).val.look i.val 0=
        UniformToeplitzCrossDAG.sharedBank K (rankKernels r p K (OAI.ExactFourier.zeta r)) i) ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).valid ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).work≤
      250*(r+1)^2+6*p.N*(52*p.split+300)+1200*(p.N+1)^2+
        40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/p.N+1)+1)+800 ∧
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).peak≤
      max (D+2) (r+7*p.N+7) := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  exact ⟨program_sharedBank r D p shape K width hD radixDiv fftDiv,
    program_valid r D p hr hD radixDiv,program_work r D p _ hr,program_peak r D p _ shape⟩

end
end ExactFourierCircuits.DFTModelCacheSpectrum
