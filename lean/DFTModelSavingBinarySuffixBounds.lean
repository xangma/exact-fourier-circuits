import DFTModelSavingBinarySuffixSemantics

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinarySuffix
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] program body DFTModelRecursiveBinary.body

theorem stages_work {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b j : ℕ) (cap : b+j≤k) :
    (stages b k Complex.I (paired f f0) j).work=1+j*(420*((R*2^k)/2)+123) := by
  induction j with
  | zero => simp only [stages,Bill.steps,Bill.one,Nat.zero_mul,Nat.add_zero]
  | succ j ih =>
    change (stages b k Complex.I (paired f f0) j).work+
      (run body ((b,((k,Complex.I),paired f f0)),
        (j,(stages b k Complex.I (paired f f0) j).val))).work+1=_
    rw [ih (by omega),stages_value f f0 b j (by omega),body_run]
    simp only [Bill.pay]
    rw [DFTModelRecursiveBinary.body_work]
    change 1+j*(420*((R*2^k)/2)+123)+(420*((R*2^k)/2)+116+6)+1=_
    ring

theorem program_work {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) :
    (run program (b,((k,Complex.I),paired f f0))).work=
      25+8*b+(k-b)*(420*((R*2^k)/2)+123) := by
  rw [program_run,tapeProgram,comp_run,loop_run]
  simp only [Bill.pass,Bill.pay,atom_run,Atom.run,Bill.one]
  rw [stages_work f f0 b (k-b) (by omega)]
  ring

theorem stages_peak {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b j B : ℕ) (cap : b+j≤k) (roles : 0<R) (two : 2≤B) (extent : R*2^k≤B) :
    (stages b k Complex.I (paired f f0) j).peak≤B := by
  have vb : 2^k≤R*2^k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^k) (show 1≤R by omega)
  have kb : k≤B := (DFTModelSavingBinary.bits_le_volume k).trans (vb.trans extent)
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : b+j<k := by omega
    have prior := ih (by omega)
    change max (max (stages b k Complex.I (paired f f0) j).peak
      (run body ((b,((k,Complex.I),paired f f0)),
        (j,(stages b k Complex.I (paired f f0) j).val))).peak) (j+1)≤B
    rw [stages_value f f0 b j (by omega),body_run]
    simp only [Bill.pay,max_zero]
    apply max_le (max_le prior ?_) (by omega)
    exact DFTModelSavingBinary.body_peak ⟨b+j,hj⟩ (partialAxes k b j f)
      (partialAxes k b j f0) j B (paired f f0) roles two extent

theorem program_peak {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b B : ℕ) (cap : b≤k) (roles : 0<R) (two : 2≤B) (extent : R*2^k≤B) :
    (run program (b,((k,Complex.I),paired f f0))).peak≤B := by
  have vb : 2^k≤R*2^k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^k) (show 1≤R by omega)
  have kb : k≤B := (DFTModelSavingBinary.bits_le_volume k).trans (vb.trans extent)
  have pb : 2^b≤B := (Nat.pow_le_pow_right (by omega) cap).trans (vb.trans extent)
  rw [program_run,tapeProgram,comp_run,loop_run]
  simp only [Bill.pass,Bill.pay,atom_run,Atom.run,Bill.one,max_zero]
  exact max_le (max_le (by omega) ((power_peak _ _).trans pb))
    (stages_peak f f0 b (k-b) B (by omega) roles two extent)

theorem program_native_work {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) (roles : 0<R) :
    (run program (b,((k,Complex.I),paired f f0))).work≤
      32*(4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+9) := by
  rw [program_work f f0 b cap]
  by_cases hk : k=0
  · subst k
    have hb : b=0 := by omega
    subst b
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.sub_self ]
    omega
  · rw [DFTModelSavingBinary.volume_half R k (by omega)]
    unfold UniformBinarySpectatorCMachine.arrayCost
    have h1 : 420*((k-b)*(R*2^(k-1)))≤800*((k-b)*(R*2^(k-1))) := by omega
    have h2 : 123*(k-b)≤352*R*(k-b) :=
      Nat.mul_le_mul_right (k-b) (by omega : 123≤352*R)
    nlinarith

end
end ExactFourierCircuits.DFTModelSavingBinarySuffix
