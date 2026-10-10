import DFTModelGlobalKernelJoinCore
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open UniformMachine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean
noncomputable section
lemma width_eq : KS.W=UniformBatching.width := by unfold UniformBatching.width; rfl
attribute [local irreducible] UniformBatching.width DFTModelSavingPeak.wholeCoeff
 DFTModelGlobalKernelAssembly.program Code.run

lemma entry_boolean {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T)
 (v v0 : ℕ→Fin c.packing.volume→Scalar) (entry : Entry c bank v v0)
 (length : bank.len=KS.W*c.packing.volume) : Boolean bank := by
 intro i hi
 rw[length] at hi
 have positive:0<c.packing.volume:=by
  have p:=DFTModelGlobalSectorPreparation.native_volume_pos (axes c)
  simpa only[c.physicalVolume] using p
 have role:i/c.packing.volume<KS.W:=(Nat.div_lt_iff_lt_mul positive).2 hi
 have index:i%c.packing.volume<c.packing.volume:=Nat.mod_lt i positive
 have original:=entry (i/c.packing.volume) role ⟨i%c.packing.volume,index⟩
 have decomposition:i/c.packing.volume*c.packing.volume+i%c.packing.volume=i:=
  by simpa only[Nat.mul_comm] using Nat.div_add_mod i c.packing.volume
 rw[decomposition] at original
 rw[original]
 simp only[encodePaired,tagged,flag]
 split <;> decide

/-- The whole typed bank is valid and keeps Boolean flags, using only the
original paired cells and its ordinary length. -/
theorem whole_peak {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T)
 (v v0 : ℕ→Fin c.packing.volume→Scalar) (entry : Entry c bank v v0)
 (length : bank.len=KS.W*c.packing.volume) :
 (run DFTModelGlobalKernelAssembly.program (input c bank)).valid ∧
 (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2.len=KS.W*c.packing.volume ∧
 Boolean (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2 ∧
 (run DFTModelGlobalKernelAssembly.program (input c bank)).peak≤
  DFTModelGlobalKernelAssembly.peakBudget (axes c) := by
 have old:=entry_boolean c bank v v0 entry length
 refine ⟨DFTModelGlobalKernelAssembly.program_valid (axes c) Complex.I KS.W bank,?_,
  DFTModelGlobalKernelAssembly.program_boolean (input c bank) old,?_⟩
 · have h:=DFTModelGlobalKernelAssembly.program_length (axes c) Complex.I KS.W bank
   simpa only[input,c.physicalVolume] using h
 · simpa only[input,width_eq] using
    DFTModelGlobalKernelAssembly.program_peak (axes c) Complex.I bank old

private lemma peak_arithmetic (V a W C : ℕ) :
 max (6*V+a+1) (max (W*V) (max (C*(V*V)) (6*(V+W*V+1))))≤
  20*(W+C+1)*(V+a+1)^2 := by
 have one:1≤(V+a+1)^2:=by
  have p:1≤V+a+1:=by omega
  simpa only[pow_two,one_mul] using Nat.mul_le_mul p p
 have vp:V≤(V+a+1)^2:=by
  have p:V+1≤V+a+1:=by omega
  have square: (V+1)*(V+1)≤(V+a+1)*(V+a+1):=Nat.mul_le_mul p p
  simp only[pow_two]
  nlinarith only[square]
 have ap:a≤(V+a+1)^2:=by nlinarith
 have square:V*V≤(V+a+1)^2:=by nlinarith
 have w:=Nat.mul_le_mul_left W vp
 have coeff:=Nat.mul_le_mul_left C square
 apply max_le ?_ (max_le ?_ (max_le ?_ ?_)) <;> nlinarith

/-- The explicit whole-assembly peak is a fixed quadratic polynomial in the
real physical volume and axis count. Complex values are not Nat word costs. -/
theorem peak_polynomial {F : ℕ} (c : KS.Context F) :
 DFTModelGlobalKernelAssembly.peakBudget (axes c)≤
  20*(KS.W+DFTModelSavingPeak.wholeCoeff+1)*(c.packing.volume+(axes c).length+1)^2 := by
 have v:(UniformSectorPacking.radices (axes c)).prod=c.packing.volume:=c.physicalVolume
 unfold DFTModelGlobalKernelAssembly.peakBudget
 dsimp only
 rw[v,←width_eq]
 exact peak_arithmetic _ _ _ _

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin
