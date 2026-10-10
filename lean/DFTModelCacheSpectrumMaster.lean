import DFTModelCacheSpectrumBankCorrect
import DFTModelRootExtraction

set_option autoImplicit false

/-! The spectrum substage extracts its FFT root from the supplied master;
the raw rectangle wrapper is responsible for generating its six input tapes. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumMaster
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelRootExtraction.program DFTModelCacheSpectrumBank.program

abbrev Input := p w (p w (p sc (Ty.a (Ty.a sc))))
def rootArgument : Prog false Input DFTModelRootExtraction.Input :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def root : Prog false Input sc := .comp rootArgument DFTModelRootExtraction.program
def kernels : Prog false Input (Ty.a (Ty.a sc)) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def argument : Prog false Input DFTModelCacheSpectrumBank.Input :=
  .fork (.atom .fst) (.fork root kernels)
def program : Prog false Input (Ty.a sc) := .comp argument DFTModelCacheSpectrumBank.program

theorem argument_run (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    run argument (N,(D,(z,ks)))=
      ((run DFTModelRootExtraction.program (N,(D,z))).pass
        (fun omega=>Bill.one (N,(omega,ks)))).pay 19 0 := by
  simp [argument,root,rootArgument,kernels,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  omega

attribute [local irreducible] argument

theorem program_run (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    run program (N,(D,(z,ks)))=
      ((run DFTModelRootExtraction.program (N,(D,z))).pass
        (fun omega=>run DFTModelCacheSpectrumBank.program (N,(omega,ks)))).pay 21 0 := by
  change ((run argument (N,(D,(z,ks)))).pass (run DFTModelCacheSpectrumBank.program)).pay 1 0=_
  rw [argument_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  congr 1 <;> first | omega | simp

theorem program_value (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (N,(D,(z,ks)))).val=
      DFTModelCacheSpectrumBank.values N (z^(D/N)) ks := by
  rw [program_run]
  change (run DFTModelCacheSpectrumBank.program
    (N,((run DFTModelRootExtraction.program (N,(D,z))).val,ks))).val=_
  rw [DFTModelRootExtraction.program_value,DFTModelCacheSpectrumBank.program_value]

theorem program_valid (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (N,(D,(z,ks)))).valid := by
  rw [program_run]
  exact ⟨DFTModelRootExtraction.program_valid _ _ _,DFTModelCacheSpectrumBank.program_valid _ _ _⟩

theorem program_work (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (N,(D,(z,ks)))).work≤
      1200*(N+1)^2+40*(Nat.log2 (D/N+1)+1)+43 := by
  rw [program_run]
  change (run DFTModelRootExtraction.program (N,(D,z))).work+
    (run DFTModelCacheSpectrumBank.program
      (N,((run DFTModelRootExtraction.program (N,(D,z))).val,ks))).work+21≤_
  have a:=DFTModelRootExtraction.program_work N D z
  have b:=DFTModelCacheSpectrumBank.program_work N
    (run DFTModelRootExtraction.program (N,(D,z))).val ks
  omega

theorem program_peak (N D : ℕ) (z : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (N,(D,(z,ks)))).peak ≤ max (D+2) (7*N+7) := by
  rw [program_run]
  have a:=DFTModelRootExtraction.program_peak N D z
  have b:=DFTModelCacheSpectrumBank.program_peak N
    (run DFTModelRootExtraction.program (N,(D,z))).val ks
  change max (max (run DFTModelRootExtraction.program (N,(D,z))).peak
    (run DFTModelCacheSpectrumBank.program
      (N,((run DFTModelRootExtraction.program (N,(D,z))).val,ks))).peak) 0≤_
  omega

theorem source_sharedBank (K D : ℕ) (hD:0<D) (hdiv:UniformRadixTwoDAG.width K∣D)
    (ks : Tape (Tape ℂ)) (f:Fin 6→Fin (UniformRadixTwoDAG.width K)→ℂ)
    (hf:∀b j,(ks.look b.val (Tape.empty ℂ)).look j.val 0=f b j)
    (i:Fin (UniformToeplitzCrossDAG.bankSize K)) :
    (run program (UniformRadixTwoDAG.width K,(D,(OAI.ExactFourier.zeta D,ks)))).val.look i.val 0=
      UniformToeplitzCrossDAG.sharedBank K f i := by
  rw [program_run]
  change (run DFTModelCacheSpectrumBank.program (UniformRadixTwoDAG.width K,
    ((run DFTModelRootExtraction.program (UniformRadixTwoDAG.width K,(D,OAI.ExactFourier.zeta D))).val,
      ks))).val.look i.val 0=_
  rw [DFTModelRootExtraction.divisor_root _ _ (UniformRadixTwoDAG.width_pos K) hD hdiv]
  exact DFTModelCacheSpectrumBank.source_sharedBank K ks f hf i

end
end ExactFourierCircuits.DFTModelCacheSpectrumMaster
