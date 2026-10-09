import DFTModelPreparation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] halfInput expand small large

theorem half_lt (n : ℕ) (hn : 2 ≤ n) : half n < n := by
  unfold half
  omega

theorem half_shrink (n : ℕ) (hn : 2 ≤ n) : 3 * half n ≤ 2*n := by
  unfold half
  omega

theorem half_index (n i : ℕ) (hi : i < n) : i/2 < half n := by
  unfold half
  omega

theorem square_parity (z : ℂ) (i : ℕ) :
    (z^(i/2))^2 * (if i%2=0 then 1 else z) = z^i := by
  have hm : i%2=0 ∨ i%2=1 := by omega
  rcases hm with hm | hm
  · simp only [hm, ↓reduceIte, mul_one]
    rw [← pow_mul]
    congr 1
    omega
  · simp only [show ¬i%2=0 by omega, ↓reduceIte]
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega

theorem small_powers {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) (hn : n ≤ 1) :
    (small.run h (n,z)).val = Tape.tab n (fun i => z^i) := by
  rw [small_value]
  cases n with
  | zero =>
    change Tape.mk 0 _ = Tape.mk 0 _
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n =>
    have he : n=0 := by omega
    subst n
    change Tape.mk 1 _ = Tape.mk 1 _
    congr 1
    funext i
    simp

theorem expand_powers {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    (expand.run h ((n,z),Tape.tab (half n) (fun i => z^i))).val =
      Tape.tab n (fun i => z^i) := by
  rw [expand_value]
  change Tape.mk n _ = Tape.mk n _
  congr 1
  funext i
  have hi := half_index n i.val i.isLt
  simp only [Tape.look, Tape.tab, hi, ↓reduceDIte]
  exact square_parity z i.val

theorem large_run (h : Handler RecPort) (n : ℕ) (z : ℂ) :
    large.run h (n,z) =
      ((h (half n,z)).pass (fun v => expand.run h ((n,z),v))).pay
        16 (max 2 (n+1)) := by
  simp only [large, Code.run, Atom.run]
  rw [halfInput_run (r := RecPort) h n z]
  simp only [Bill.one, Bill.pass, Bill.pay]
  simp only [zero_max, max_zero, true_and, and_true]
  congr 1 <;> omega

theorem step_small (h : Handler RecPort) (n : ℕ) (z : ℂ) (hn : n < 2) :
    step.run h (n,z) = (small.run h (n,z)).pay 6 2 := by
  simp [step, test, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word, hn, Nat.add_assoc]
  constructor <;> omega

theorem step_large (h : Handler RecPort) (n : ℕ) (z : ℂ) (hn : 2 ≤ n) :
    step.run h (n,z) = (large.run h (n,z)).pay 6 2 := by
  simp [step, test, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word, show ¬n<2 by omega, Nat.add_assoc]
  constructor <;> omega

def result (fuel n : ℕ) (z : ℂ) : Bill (Tape ℂ) :=
  depthRun ((small (r := none)).run ()) step.run fuel (n,z)

theorem result_zero (n : ℕ) (z : ℂ) :
    result 0 n z = ((small (r := none)).run () (n,z)).pay 1 0 := rfl

theorem result_succ_small (fuel n : ℕ) (z : ℂ) (hn : n < 2) :
    result (fuel+1) n z = (((small (r := RecPort)).run (fun x : Input.T => result fuel x.1 x.2) (n,z)).pay 6 2).pay 1 (fuel+1) := by
  change (step.run (fun x : Input.T => result fuel x.1 x.2) (n,z)).pay 1 (fuel+1) = _
  rw [step_small _ _ _ hn]

theorem result_succ_large (fuel n : ℕ) (z : ℂ) (hn : 2 ≤ n) :
    result (fuel+1) n z =
      (((result fuel (half n) z).pass
        (fun v => (expand (r := RecPort)).run (fun x : Input.T => result fuel x.1 x.2) ((n,z),v))).pay
          22 (max 2 (n+1))).pay 1 (fuel+1) := by
  change (step.run (fun x : Input.T => result fuel x.1 x.2) (n,z)).pay 1 (fuel+1) = _
  rw [step_large _ _ _ hn, large_run]
  simp [Bill.pay, Nat.add_assoc, max_assoc]

/-- Actual charged recurrence: one child plus one linear parent publication. -/
theorem result_work_large (fuel n : ℕ) (z : ℂ) (hn : 2 ≤ n) :
    (result (fuel+1) n z).work ≤ (result fuel (half n) z).work+49*n+29 := by
  rw [result_succ_large _ _ _ hn]
  change (result fuel (half n) z).work +
    ((expand (r := RecPort)).run (fun x : Input.T => result fuel x.1 x.2)
      ((n,z),(result fuel (half n) z).val)).work+22+1 ≤ _
  have he := expand_work (r := RecPort) (fun x : Input.T => result fuel x.1 x.2)
    n z (result fuel (half n) z).val
  omega

/-- The fuel is only a syntactic recursion bound. Work depends on table length,
not unused fuel. The recursion's actual fuel words are included in `peak`. -/
theorem result_spec (fuel n : ℕ) (z : ℂ) (hn : n ≤ fuel+1) :
    (result fuel n z).val = Tape.tab n (fun i => z^i) ∧
    (result fuel n z).valid ∧
    (result fuel n z).work ≤ 200*n+20 ∧
    (result fuel n z).peak ≤ max fuel (n+2) := by
  induction fuel generalizing n with
  | zero =>
    rw [result_zero]
    refine ⟨small_powers (r := none) () n z (by omega), small_valid (r := none) () n z, ?_, ?_⟩
    · change ((small (r := none)).run () (n,z)).work+1 ≤ _
      rw [small_work]
      omega
    · change max ((small (r := none)).run () (n,z)).peak 0 ≤ _
      rw [small_peak]
      omega
  | succ fuel ih =>
    by_cases hs : n < 2
    · rw [result_succ_small _ _ _ hs]
      let h : Handler RecPort := fun x => result fuel x.1 x.2
      refine ⟨small_powers h n z (by omega), small_valid h n z, ?_, ?_⟩
      · change ((small (r := RecPort)).run h (n,z)).work+6+1 ≤ _
        rw [small_work]
        omega
      · change max (max ((small (r := RecPort)).run h (n,z)).peak 2) (fuel+1) ≤ _
        rw [small_peak]
        omega
    · have hlarge : 2 ≤ n := by omega
      have hhalf := half_lt n hlarge
      obtain ⟨hv,hvalid,hw,hp⟩ := ih (half n) (by omega)
      let h : Handler RecPort := fun x => result fuel x.1 x.2
      rw [result_succ_large _ _ _ hlarge]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (expand.run h ((n,z),(result fuel (half n) z).val)).val = _
        rw [hv, expand_powers]
      · change (result fuel (half n) z).valid ∧
          (expand.run h ((n,z),(result fuel (half n) z).val)).valid
        exact ⟨hvalid, expand_valid h n z _⟩
      · change (result fuel (half n) z).work +
          (expand.run h ((n,z),(result fuel (half n) z).val)).work+22+1 ≤ _
        have he := expand_work h n z (result fuel (half n) z).val
        have shrink := half_shrink n hlarge
        omega
      · change max (max (max (result fuel (half n) z).peak
          (expand.run h ((n,z),(result fuel (half n) z).val)).peak)
            (max 2 (n+1))) (fuel+1) ≤ _
        have he := expand_peak h n z (result fuel (half n) z).val
        omega

theorem program_run (n : ℕ) (z : ℂ) :
    run program (n,z) = (result n n z).pay 5 n := by
  simp only [program, run, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay, result]
  simp only [zero_max, max_zero, true_and, and_true]
  congr 1
  omega

/-- Exact power table, including N=0 and root=0. No root nonzero premise. -/
theorem program_value (n : ℕ) (z : ℂ) :
    (run program (n,z)).val = Tape.tab n (fun i => z^i) := by
  rw [program_run]
  exact (result_spec n n z (by omega)).1

theorem program_valid (n : ℕ) (z : ℂ) : (run program (n,z)).valid := by
  rw [program_run]
  exact (result_spec n n z (by omega)).2.1

theorem program_work (n : ℕ) (z : ℂ) :
    (run program (n,z)).work ≤ 200*n+25 := by
  rw [program_run]
  change (result n n z).work+5 ≤ _
  have h := (result_spec n n z (by omega)).2.2.1
  omega

theorem program_peak (n : ℕ) (z : ℂ) :
    (run program (n,z)).peak ≤ n+2 := by
  rw [program_run]
  change max (result n n z).peak n ≤ _
  have h := (result_spec n n z (by omega)).2.2.2
  omega

theorem program_length (n : ℕ) (z : ℂ) : (run program (n,z)).val.len = n := by
  rw [program_value]
  rfl

theorem program_look (n i : ℕ) (z : ℂ) (hi : i < n) :
    (run program (n,z)).val.look i 0 = z^i := by
  rw [program_value]
  simp [Tape.look, Tape.tab, hi]

/-- One fixed prepared-scalar program, with linear work and polynomial words. -/
theorem program_contract (n : ℕ) (z : ℂ) :
    (run program (n,z)).val = Tape.tab n (fun i => z^i) ∧
    (run program (n,z)).valid ∧
    (run program (n,z)).work ≤ 200*(n+1) ∧
    (run program (n,z)).peak ≤ (n+2)^1 := by
  refine ⟨program_value n z, program_valid n z, ?_, ?_⟩
  · have h := program_work n z
    omega
  · simpa using program_peak n z

end
end ExactFourierCircuits.DFTModelPreparation
