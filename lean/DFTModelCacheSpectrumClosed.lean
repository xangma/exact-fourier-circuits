import DFTModelCacheSpectrumMaster
import DFTModelCacheDisplacementClosed

set_option autoImplicit false

/-! Raw rectangle metadata plus one prepared master root produce all seven
shared coefficient blocks. Neither kernels nor spectra are entry arguments. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrum
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelRootExtraction.program
  DFTModelCacheDisplacement.program DFTModelCacheSpectrumMaster.program

abbrev Input := p DFTModelCacheDisplacement.Metadata (p w sc)
def localArgument : Prog false Input DFTModelRootExtraction.Input :=
  .fork (.comp (.atom .fst) DFTModelCacheDisplacement.radix) (.atom .snd)
def localRoot : Prog false Input sc := .comp localArgument DFTModelRootExtraction.program
def kernelArgument : Prog false Input DFTModelCacheDisplacement.Input :=
  .fork (.atom .fst) localRoot
def kernels : Prog false Input (Ty.a (Ty.a sc)) :=
  .comp kernelArgument DFTModelCacheDisplacement.program
def argument : Prog false Input DFTModelCacheSpectrumMaster.Input :=
  .fork (.comp (.atom .fst) DFTModelCacheDisplacement.size)
    (.fork (.comp (.atom .snd) (.atom .fst))
      (.fork (.comp (.atom .snd) (.atom .snd)) kernels))
def program : Prog false Input (Ty.a sc) := .comp argument DFTModelCacheSpectrumMaster.program

theorem kernels_run (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) :
    run kernels (DFTModelCacheDisplacement.metadata r p,(D,z))=
      ((run DFTModelRootExtraction.program (r,(D,z))).pass
        (fun omega=>run DFTModelCacheDisplacement.program
          (DFTModelCacheDisplacement.metadata r p,omega))).pay 9 0 := by
  simp [kernels,kernelArgument,localRoot,localArgument,DFTModelCacheDisplacement.radix,
    DFTModelCacheDisplacement.metadata,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

attribute [local irreducible] kernels

theorem argument_run (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) :
    run argument (DFTModelCacheDisplacement.metadata r p,(D,z))=
      ((run kernels (DFTModelCacheDisplacement.metadata r p,(D,z))).pass
        (fun ks=>Bill.one (p.N,(D,(z,ks))))).pay 17 0 := by
  simp [argument,DFTModelCacheDisplacement.size,DFTModelCacheDisplacement.metadata,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

attribute [local irreducible] argument

theorem program_run (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) :
    run program (DFTModelCacheDisplacement.metadata r p,(D,z))=
      ((run DFTModelRootExtraction.program (r,(D,z))).pass (fun omega=>
        (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,omega)).pass
          (fun ks=>run DFTModelCacheSpectrumMaster.program (p.N,(D,(z,ks)))))).pay 28 0 := by
  change ((run argument (DFTModelCacheDisplacement.metadata r p,(D,z))).pass
    (run DFTModelCacheSpectrumMaster.program)).pay 1 0=_
  rw [argument_run,kernels_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  congr 1 <;> first | omega | simp [and_assoc]

def rawKernels (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) : Tape (Tape ℂ) :=
  DFTModelCacheDisplacement.rawValues p (DFTModelCacheKernelNewton.hValues r omega)
    (DFTModelCacheKernelNewton.gValues r omega)

theorem program_value (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) (hr:0<r) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).val=
      DFTModelCacheSpectrumBank.values p.N (z^(D/p.N)) (rawKernels r p (z^(D/r))) := by
  rw [program_run]
  change (run DFTModelCacheSpectrumMaster.program (p.N,(D,(z,
    (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,z))).val)).val)))).val=_
  rw [DFTModelRootExtraction.program_value,DFTModelCacheDisplacement.program_value r p _ hr,
    DFTModelCacheSpectrumMaster.program_value]
  rfl

theorem program_valid (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (hr:0<r) (hD:0<D) (hdiv:r∣D) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))).valid := by
  rw [program_run]
  refine ⟨DFTModelRootExtraction.program_valid _ _ _,?_⟩
  rw [DFTModelRootExtraction.divisor_root _ _ hr hD hdiv]
  exact ⟨DFTModelCacheDisplacement.program_valid p hr
      (Complex.isPrimitiveRoot_exp r (Nat.ne_of_gt hr)),DFTModelCacheSpectrumMaster.program_valid _ _ _ _⟩

theorem program_work (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ) (hr:0<r) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).work≤
      250*(r+1)^2+6*p.N*(52*p.split+300)+1200*(p.N+1)^2+
        40*(Nat.log2 (D/r+1)+1)+40*(Nat.log2 (D/p.N+1)+1)+800 := by
  rw [program_run]
  have a:=DFTModelRootExtraction.program_work r D z
  have b:=DFTModelCacheDisplacement.program_work r p
    (run DFTModelRootExtraction.program (r,(D,z))).val hr
  have c:=DFTModelCacheSpectrumMaster.program_work p.N D z
    (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,z))).val)).val
  change (run DFTModelRootExtraction.program (r,(D,z))).work+
    ((run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,z))).val)).work+
      (run DFTModelCacheSpectrumMaster.program (p.N,(D,(z,
        (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
          (run DFTModelRootExtraction.program (r,(D,z))).val)).val)))).work)+28≤_
  omega

theorem program_peak (r D : ℕ) (p : UniformRankKernelMachine.Parameters) (z : ℂ)
    (shape:DFTModelCacheDisplacement.Shape p r) :
    (run program (DFTModelCacheDisplacement.metadata r p,(D,z))).peak≤
      max (D+2) (r+7*p.N+7) := by
  rw [program_run]
  have a:=DFTModelRootExtraction.program_peak r D z
  have b:=DFTModelCacheDisplacement.program_peak r p
    (run DFTModelRootExtraction.program (r,(D,z))).val shape
  have c:=DFTModelCacheSpectrumMaster.program_peak p.N D z
    (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,z))).val)).val
  change max (max (run DFTModelRootExtraction.program (r,(D,z))).peak
    (max (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
      (run DFTModelRootExtraction.program (r,(D,z))).val)).peak
      (run DFTModelCacheSpectrumMaster.program (p.N,(D,(z,
        (run DFTModelCacheDisplacement.program (DFTModelCacheDisplacement.metadata r p,
          (run DFTModelRootExtraction.program (r,(D,z))).val)).val)))).peak)) 0≤_
  omega

end
end ExactFourierCircuits.DFTModelCacheSpectrum
