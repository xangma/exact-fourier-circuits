import DFTModelChirp

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirp
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] double publish DFTModelPreparation.program

theorem pow_mod (z : ℂ) (m e : ℕ) (hm : z^m=1) : z^(e%m)=z^e := by
  conv_rhs => rw [← Nat.mod_add_div e m]
  rw [pow_add,pow_mul,hm,one_pow,mul_one]

theorem negative_pow_mod (z : ℂ) (m e : ℕ) (hm : z^m=1) (hpos : 0 < m) :
    z^((m-e%m)%m) = (z⁻¹)^e := by
  have hz : z≠0 := by
    intro hz
    subst z
    simp [hpos.ne'] at hm
  rw [pow_mod z m (m-e%m) hm, inv_pow]
  have hr : e%m ≤ m := (Nat.mod_lt _ hpos).le
  calc
    z^(m-e%m) = (z^(e%m))⁻¹ := by
      apply mul_right_cancel₀ (pow_ne_zero (e%m) hz)
      rw [inv_mul_cancel₀ (pow_ne_zero (e%m) hz),←pow_add,Nat.sub_add_cancel hr,hm]
    _ = (z^e)⁻¹ := congrArg Inv.inv (pow_mod z m e hm)

def bank (n : ℕ) (z : ℂ) : Tape ℂ := Tape.tab (2*n) (fun i =>
  if i%2=0 then UniformChirp.chirp z (i/2) else UniformChirp.chirp z⁻¹ (i/2))

theorem address_lt (n i : ℕ) (hn : 0 < n) : address n i < 2*n := by
  unfold address
  split <;> exact Nat.mod_lt _ (by omega)

theorem publish_powers (n : ℕ) (z : ℂ) (hn : 0 < n) (hz : z^(2*n)=1) :
    (run publish ((n,z),Tape.tab (2*n) (fun i => z^i))).val = bank n z := by
  rw [publish_value]
  change Tape.mk (2*n) _ = Tape.mk (2*n) _
  congr 1
  funext i
  have hi := address_lt n i.val hn
  dsimp only
  rw [Tape.look_of_lt _ _ hi]
  change z^(address n i.val) = _
  unfold address
  by_cases he : i.val%2=0
  · simp only [he,↓reduceIte,UniformChirp.chirp]
    exact pow_mod z (2*n) ((i.val/2)^2) hz
  · simp only [he,↓reduceIte,UniformChirp.chirp]
    exact negative_pow_mod z (2*n) ((i.val/2)^2) hz (by omega)

theorem program_run (n : ℕ) (z : ℂ) :
    run program (n,z) =
      ((run DFTModelPreparation.program (2*n,z)).pass
        (fun v => run publish ((n,z),v))).pay 11 (max 2 (2*n)) := by
  simp only [program,Code.run,Atom.run]
  have hd : Code.run double () (n,z) = ⟨2*n,5,max 2 (2*n),True⟩ := double_run n z
  rw [hd]
  simp only [Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true,zero_max,max_zero]
  dsimp only [run]
  congr 1 <;> omega

theorem program_value (n : ℕ) (z : ℂ) (hn : 0 < n) (hz : z^(2*n)=1) :
    (run program (n,z)).val = bank n z := by
  rw [program_run]
  change (run publish ((n,z),(run DFTModelPreparation.program (2*n,z)).val)).val = _
  rw [DFTModelPreparation.program_value,publish_powers n z hn hz]

theorem program_valid (n : ℕ) (z : ℂ) : (run program (n,z)).valid := by
  rw [program_run]
  exact ⟨DFTModelPreparation.program_valid _ _,publish_valid _ _ _⟩

theorem program_work (n : ℕ) (z : ℂ) :
    (run program (n,z)).work ≤ 530*n+46 := by
  rw [program_run]
  change (run DFTModelPreparation.program (2*n,z)).work+
    (run publish ((n,z),(run DFTModelPreparation.program (2*n,z)).val)).work+11 ≤ _
  have hp := DFTModelPreparation.program_work (2*n) z
  have ht := publish_work n z (run DFTModelPreparation.program (2*n,z)).val
  omega

theorem publish_peak (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run publish ((n,z),v)).peak ≤ (n+2)^2 := by
  rw [publish_run]
  change max (Bill.tab (2*n) sc.blank (fun i => run cell (((n,z),v),i))).peak
    (max 2 (2*n)) ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs : (Finset.range (2*n)).sup (fun i => (run cell (((n,z),v),i)).peak) ≤ (n+2)^2 := by
    apply Finset.sup_le
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hd : i/2 < n := by omega
    have hp : (i/2)^2 ≤ n^2 := Nat.pow_le_pow_left (by omega : i/2 ≤ n) 2
    rw [cell_run]
    dsimp only [Bill.peak]
    have h2 : 2 ≤ (n+2)^2 := by nlinarith
    have hn : 2*n ≤ (n+2)^2 := by nlinarith
    have hpow : (i/2)^2 ≤ (n+2)^2 := by nlinarith
    omega
  have hn : 2*n ≤ (n+2)^2 := by nlinarith
  have h2 : 2 ≤ (n+2)^2 := by nlinarith
  omega

theorem program_peak (n : ℕ) (z : ℂ) :
    (run program (n,z)).peak ≤ (n+2)^2 := by
  rw [program_run]
  change max (max (run DFTModelPreparation.program (2*n,z)).peak
    (run publish ((n,z),(run DFTModelPreparation.program (2*n,z)).val)).peak)
      (max 2 (2*n)) ≤ _
  have hp := DFTModelPreparation.program_peak (2*n) z
  have ht := publish_peak n z (run DFTModelPreparation.program (2*n,z)).val
  have hn : 2*n+2 ≤ (n+2)^2 := by nlinarith
  omega

theorem bank_even (n j : ℕ) (z : ℂ) (hj : j<n) :
    (bank n z).look (2*j) 0 = UniformChirp.chirp z j := by
  have hi : 2*j < 2*n := by omega
  simp [bank,Tape.look,Tape.tab,hi]

theorem bank_odd (n j : ℕ) (z : ℂ) (hj : j<n) :
    (bank n z).look (2*j+1) 0 = UniformChirp.chirp z⁻¹ j := by
  have hi : 2*j+1 < 2*n := by omega
  have hd : (2*j+1)/2=j := by omega
  simp [bank,Tape.look,Tape.tab,hi,hd]

theorem specified_period (n : ℕ) (hn : 0<n) : OAI.ExactFourier.zeta (2*n)^(2*n)=1 := by
  simpa [OAI.ExactFourier.zeta] using
    UniformRoots.specifiedRoot_mul_power 1 (2*n) (by omega) (by omega)

theorem specified_value (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (2*n))).val = bank n (OAI.ExactFourier.zeta (2*n)) :=
  program_value n _ hn (specified_period n hn)

end
end ExactFourierCircuits.DFTModelChirp
