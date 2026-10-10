import DFTModelGlobalSectorSavingSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorSaving
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarSource
open DFTModelSectorTranspose
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.program

def natural {W V : ℕ} (f : Fin W→Fin V→Scalar) (r j : ℕ) : Scalar :=
 if hr:r<W then if hj:j<V then f ⟨r,hr⟩ ⟨j,hj⟩ else Scalar.zero else Scalar.zero

lemma natural_fin {W V : ℕ} (f : Fin W→Fin V→Scalar) (r : Fin W) (j : Fin V) :
 natural f r.val j.val=f r j := by simp [natural,r.isLt,j.isLt]

lemma gathered_paired {W q V a : ℕ} (bank : Tape Tagged.T)
 (f f0 : Fin W→Fin (2^q)→Scalar)
 (encoded : ∀(r : Fin W)(j : Fin (2^q)),
  bank.look (r.val*V+a+j.val) Tagged.blank=encodePaired (f r j) (f0 r j)) :
 gathered W V a (2^q) bank Tagged.blank=paired f f0 := by
 apply DFTModelSavingY.tape_ext (a:=gathered W V a (2^q) bank Tagged.blank)
   (b:=paired f f0) Tagged.blank rfl
 intro j
 by_cases hj:j<W*2^q
 · let r : Fin W := ⟨j/(2^q),(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).2 hj⟩
   let t : Fin (2^q) := ⟨j%(2^q),Nat.mod_lt _ (Nat.two_pow_pos q)⟩
   have addr:r.val*2^q+t.val=j := by
     change (j/(2^q))*2^q+j%(2^q)=j
     rw [Nat.mul_comm]
     exact Nat.div_add_mod j (2^q)
   rw [←addr,paired_lookup,←gather_value]
   exact (gather_lookup Tagged W V a (2^q) r.val t.val bank r.isLt t.isLt).trans
     (encoded r t)
 · rw [Tape.look_of_le _ _ (by change W*2^q≤j;omega),
       Tape.look_of_le _ _ (by change W*2^q≤j;omega)]

/-- The only typed child is the held closed saving program. Its exact output
comes from the two actual source witnesses, with the original Scalar flags. -/
theorem value {n B q A F K ticks W V a : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {f f0 out out0 : Fin DFTModelSavingNativeRoot.W→Fin (2^q)→Scalar}
 (bank : Tape Tagged.T) (roles : W=DFTModelSavingNativeRoot.W)
 (encoded : ∀r j,bank.look (r.val*V+a+j.val) Tagged.blank=encodePaired (f r j) (f0 r j))
 (result : DFTModelSavingNativeRoot.Result n B q A F K x s s0 u u0 ticks f f0 out out0) :
 (run saving ((q,Complex.I),((W,(V,a)),bank))).val=
   ((((q,Complex.I),((W,(V,a)),bank)),2^q),paired out out0) := by
 subst W
 rw [saving_value,gathered_paired bank f f0 encoded,result.compiled]

theorem work {n B q A F K ticks W V a : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {f f0 out out0 : Fin DFTModelSavingNativeRoot.W→Fin (2^q)→Scalar}
 (bank : Tape Tagged.T) (roles : W=DFTModelSavingNativeRoot.W) (positive : 1≤W)
 (encoded : ∀r j,bank.look (r.val*V+a+j.val) Tagged.blank=encodePaired (f r j) (f0 r j))
 (result : DFTModelSavingNativeRoot.Result n B q A F K x s s0 u u0 ticks f f0 out out0) :
 (run saving ((q,Complex.I),((W,(V,a)),bank))).work≤
   (K+11)*(W*(7*2^q+12)+17+9+ticks) := by
 have eq : gathered W V a (2^q) bank Tagged.blank=paired f f0 := by
   subst W;exact gathered_paired bank f f0 encoded
 rw [saving_work,eq]
 have child:=result.work
 have qp:q≤2^q := Nat.le_of_lt q.lt_two_pow_self
 have v:2^q≤W*2^q := Nat.le_mul_of_pos_left _ positive
 have overhead:61*(W*2^q)+8*q+74≤11*(W*(7*2^q+12)+17) := by nlinarith
 have add:=Nat.add_le_add overhead child
 nlinarith

lemma paired_boolean {R V : ℕ} (f f0 : Fin R→Fin V→Scalar) :
 DFTModelSavingResidualBoolean.Boolean (paired f f0) := by
 intro j hj
 rw [Tape.look_of_lt _ _ hj]
 change DFTModelAffine.flag (_ : Scalar).dependent<2
 cases (_ : Scalar).dependent <;> decide

/-- The physical input's finite Scalar flags supply the child's Boolean
condition. No Boolean output or child peak is supplied by the caller. -/
theorem peak {q V a : ℕ} (bank : Tape Tagged.T)
 (f f0 : Fin DFTModelSavingNativeRoot.W→Fin (2^q)→Scalar)
 (encoded : ∀r j,bank.look (r.val*V+a+j.val) Tagged.blank=encodePaired (f r j) (f0 r j))
 (roles : 1≤DFTModelSavingNativeRoot.W) (fit : a+2^q≤V) :
 (run saving ((q,Complex.I),((DFTModelSavingNativeRoot.W,(V,a)),bank))).peak≤
   max (DFTModelSavingNativeRoot.W*V) (DFTModelSavingPeak.wholeCoeff*(2^q*2^q)) := by
 have outer := argument_peak Tagged q DFTModelSavingNativeRoot.W V a Complex.I bank roles fit
 have child := DFTModelSavingPeak.program_peak_bound q Complex.I (paired f f0) rfl
   (paired_boolean f f0)
 simp only [saving,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
 change max (run (argument Tagged)
   ((q,Complex.I),((DFTModelSavingNativeRoot.W,(V,a)),bank))).peak
   (run DFTModelSavingProgram.program
     (run (argument Tagged) ((q,Complex.I),((DFTModelSavingNativeRoot.W,(V,a)),bank))).val.2).peak≤_
 rw [argument_value,gathered_paired bank f f0 encoded]
 exact max_le_max outer child

end
end ExactFourierCircuits.DFTModelGlobalSectorSaving
