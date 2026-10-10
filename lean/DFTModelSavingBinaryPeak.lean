import DFTModelSavingBinarySemantics

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired)
open UniformBinaryTensorCoordinates
noncomputable section
attribute [local irreducible] DFTModelBinaryStage.program DFTModelBinaryPhysical.program
  DFTModelRecursiveBinary.body DFTModelRecursiveBinary.program

theorem affine_peak_flags {M : ℕ} (v : Fin M → Fin 2 → Tagged.T)
    (flags : ∀j t,(v j t).1≤1) :
    (run DFTModelBinaryAffine.program (DFTModelBinaryAffine.input v)).peak≤ max M 2 := by
  change max (max 0 (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run DFTModelBinaryAffine.cell ((M,((ExactFourierCircuits.a,ExactFourierCircuits.b),
      DFTModelBinaryAffine.data v)),j))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,zero_max]
  refine max_le (le_max_left _ _) ?_
  apply Finset.sup_le
  intro j hj
  have lt : j<M := Finset.mem_range.mp hj
  rw [DFTModelBinaryAffine.cell_run]
  change ((DFTModelBinaryAffine.data v).look j ((0,(0,0)),(0,(0,0)))).1.1+
    ((DFTModelBinaryAffine.data v).look j ((0,(0,0)),(0,(0,0)))).2.1≤ max M 2
  simp only [DFTModelBinaryAffine.data,Tape.look,lt,↓reduceDIte]
  exact (Nat.add_le_add (flags ⟨j,lt⟩ 0) (flags ⟨j,lt⟩ 1)).trans (le_max_right _ _)

theorem physical_peak_flags (P Q B : ℕ) (v : Tape Tagged.T)
    (flags : ∀j t,(DFTModelBinaryPhysical.view P Q v j t).1≤1)
    (positive : 0<P) (extent : P*2*Q≤B) (two : 2≤B) :
    (run DFTModelBinaryPhysical.program (P*Q,(P,((ExactFourierCircuits.a,ExactFourierCircuits.b),v)))).peak≤B := by
  rw [DFTModelBinaryPhysical.program,comp_run,DFTModelBinaryPhysical.ready_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  apply max_le (DFTModelBinaryPacking.program_peak P Q B v positive extent two)
  rw [DFTModelBinaryPacking.physical_view]
  exact (affine_peak_flags (DFTModelBinaryPhysical.view P Q v) flags).trans
    (max_le (by nlinarith) two)

theorem stage_peak_flags (P Q B : ℕ) (v : Tape Tagged.T)
    (flags : ∀j t,(DFTModelBinaryPhysical.view P Q v j t).1≤1)
    (positive : 0<P) (extent : P*2*Q≤B) (two : 2≤B) :
    (run DFTModelBinaryStage.program (P*Q,(P,((ExactFourierCircuits.a,ExactFourierCircuits.b),v)))).peak≤B := by
  rw [DFTModelBinaryStage.program,comp_run,DFTModelBinaryStage.ready_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  apply max_le (physical_peak_flags P Q B v flags positive extent two)
  apply DFTModelBinaryUnpacking.program_peak _ _ _ _ _ two
  convert extent using 1;ring

theorem paired_flag {R V : ℕ} (f f0 : Fin R → Fin V → Scalar) (a : Fin (R*V)) :
    ((paired f f0).look a.val Tagged.blank).1≤1 := by
  rw [paired_flatten]
  change flag (flatten f a).dependent≤1
  cases (flatten f a).dependent <;> simp [flag]

theorem body_peak {R k : ℕ} (i : Fin k) (f f0 : Fin R → Fin (2^k) → Scalar)
    (j B : ℕ) (old : Tape Tagged.T) (roles : 0<R) (two : 2≤B) (extent : R*2^k≤B) :
    (run DFTModelRecursiveBinary.body (((k,Complex.I),old),(j,(2^i.val,paired f f0)))).peak≤B := by
  let Q := R*2^(k-(i.val+1))
  have volume : 2^i.val*2*Q=R*2^k := global_volume R k i
  have divide : (paired f f0).len/2=2^i.val*Q := by
    change (R*2^k)/2=_
    rw [←volume,show 2^i.val*2*Q=(2^i.val*Q)*2 by ring,Nat.mul_div_cancel _ (by omega)]
  have flags : ∀a t,(DFTModelBinaryPhysical.view (2^i.val) Q (paired f f0) a t).1≤1 := by
    intro a t
    let z := (finCongr volume) (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 Q (a,t))
    exact paired_flag f f0 z
  have peak := stage_peak_flags (2^i.val) Q B (paired f f0) flags (by positivity)
    (by rwa [volume]) two
  have vb : 2^k≤R*2^k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^k) (show 1≤R by omega)
  have doubled : 2*2^i.val≤B := by
    rw [Nat.mul_comm,←Nat.pow_succ]
    exact (Nat.pow_le_pow_right (by omega) (by omega : i.val+1≤k)).trans (vb.trans extent)
  rw [DFTModelRecursiveBinary.body,fork_run,DFTModelRecursiveBinary.doubled_run,
    comp_run,DFTModelRecursiveBinary.argument_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero]
  rw [divide]
  exact max_le (max_le two doubled) (max_le (max_le two extent) peak)

theorem bits_le_volume (k : ℕ) : k≤2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
    rw [Nat.pow_succ]
    omega

theorem stages_peak {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (j B : ℕ) (cap : j≤k) (roles : 0<R) (two : 2≤B) (extent : R*2^k≤B) :
    (DFTModelRecursiveBinary.stages k Complex.I (paired f f0) j).peak≤B := by
  have vb : 2^k≤R*2^k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^k) (show 1≤R by omega)
  have kb : k≤B := (bits_le_volume k).trans (vb.trans extent)
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : j<k := by omega
    have prior := ih (by omega)
    change max (max (DFTModelRecursiveBinary.stages k Complex.I (paired f f0) j).peak
      (run DFTModelRecursiveBinary.body (((k,Complex.I),paired f f0),
        (j,(DFTModelRecursiveBinary.stages k Complex.I (paired f f0) j).val))).peak) (j+1)≤B
    rw [DFTModelRecursiveBinary.stages_value,states_paired f f0 j (by omega)]
    exact max_le (max_le prior (body_peak ⟨j,hj⟩ (partialAxes k j f) (partialAxes k j f0) j B
      (paired f f0) roles two extent)) (by omega)

theorem program_peak {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (B : ℕ) (roles : 0<R) (two : 2≤B) (extent : R*2^k≤B) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).peak≤B := by
  rw [DFTModelRecursiveBinary.program,comp_run,DFTModelRecursiveBinary.loop_run]
  simp only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero]
  exact max_le (by omega) (stages_peak f f0 k B (le_refl _) roles two extent)

end
end ExactFourierCircuits.DFTModelSavingBinary
