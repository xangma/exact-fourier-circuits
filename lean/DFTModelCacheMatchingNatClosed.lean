import DFTModelCacheMatchingNatPermutation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open UniformMatchingAxisTableMachine
noncomputable section

attribute [local irreducible] Code.run

theorem compiled_lengths (r : ℕ) (z : Tape Row.T) :
    (run compiled (r,z)).val.2.1.len=862 ∧
      (run compiled (r,z)).val.2.2.len=heapSize r z.len := by
  have same := congrArg (fun b : Bill LocalValue=>b.val) (compiled_run r z)
  dsimp only [Bill.pass,Bill.pay] at same
  have fuel:=DFTModelCacheNatDispatch.fuel_value instructions (runtime r z.len)
    (run initializeProgram (r,z)).val
  have h:=DFTModelCacheNatDispatch.trajectory_lengths instructions
    (run initializeProgram (r,z)).val (runtime r z.len)
  have regs : (run initializeProgram (r,z)).val.2.1.len=862 :=
    congrArg (fun v : LocalValue=>v.2.1.len) (initialize_value r z)
  have heap : (run initializeProgram (r,z)).val.2.2.len=heapSize r z.len :=
    congrArg (fun v : LocalValue=>v.2.2.len) (initialize_value r z)
  exact ⟨(congrArg (fun v : LocalValue=>v.2.1.len) (same.trans fuel)).trans (h.1.trans regs),
    (congrArg (fun v : LocalValue=>v.2.2.len) (same.trans fuel)).trans (h.2.trans heap)⟩

private theorem pair_run {s t u : Ty} (f : Prog false s t)
    (g : Prog false (p s t) u) (x : s.T) :
    run (.comp (.fork (.atom .id) f) (.fork (.atom .snd) g)) x=
      ⟨((run f x).val,(run g (x,(run f x).val)).val),
       (run f x).work+(run g (x,(run f x).val)).work+5,
       max (run f x).peak (run g (x,(run f x).val)).peak,
       (run f x).valid ∧ (run g (x,(run f x).val)).valid⟩ := by
  simp only [comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
    zero_max,max_zero,true_and,and_true]
  congr 1;omega

theorem program_run (r : ℕ) (z : Tape Row.T) :
    run program (r,z)=
      ⟨((run compiled (r,z)).val,(run extract ((r,z),(run compiled (r,z)).val)).val),
       (run compiled (r,z)).work+(run extract ((r,z),(run compiled (r,z)).val)).work+5,
       max (run compiled (r,z)).peak (run extract ((r,z),(run compiled (r,z)).val)).peak,
       (run compiled (r,z)).valid ∧ (run extract ((r,z),(run compiled (r,z)).val)).valid⟩ :=
  pair_run compiled extract (r,z)

private theorem polynomial_work (r M : ℕ) (cap : 2*M≤r) :
    200025+204*(867+3*M+3*r)+
      (17*r+8*M+21)*(35*(862+(867+3*M+3*r))+435)+31*r+11≤
        3000000*(r+1)^2 := by
  have size:867+3*M+3*r≤867+6*r := by omega
  have time:17*r+8*M+21≤21*r+21 := by omega
  have product:=Nat.mul_le_mul time
    (Nat.add_le_add_right (Nat.mul_le_mul_left 35 (Nat.add_le_add_left size 862)) 435)
  nlinarith

private theorem polynomial_peak (r M : ℕ) (cap : 2*M≤r) :
    max (max (2*(867+3*M+3*r)+2000) (17*r+8*M+21))
      (max r (max 3 (3*M+r)))≤4000*(r+1) := by omega

/-- A closed Nat-only typed producer, from runtime radix and selected raw rows.
The endpoint projection, initialization, all 55-instruction dispatch steps and
ordered-bank readback are charged. Raw matching selection is the input boundary. -/
theorem execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hm : Matching E) (hr : InRange r E) : ∃u,
    UniformMachine.BoundedExecution UniformMatchingAxisTableMachine.program n x
      (wordBound r z.len) (sourceState r z) (runtime r M) u ∧
    (run program (r,z)).valid ∧ Represents (run program (r,z)).val.1 u ∧
    (run program (r,z)).val.2.len=r ∧
    (∀j : Fin r,(run program (r,z)).val.2.look j.val 0=
      (ordered r E)[j.val]'(by rw [ordered_length r E hm hr];exact j.isLt)) ∧
    Bank (W r z.len) (widths r M) u ∧
    AxisRow (A r z.len) r M (W r z.len) (P z.len) u ∧
    (run program (r,z)).work≤3000000*(r+1)^2 ∧
    (run program (r,z)).peak≤4000*(r+1) := by
  obtain ⟨u,actual,valid,rep,bank,widths,axis,work,peak⟩:=
    compiled_execution r n x z E rows hm hr
  have lengths:=compiled_lengths r z
  have read:=extracted_ordered r z (run compiled (r,z)).val u E hm hr lengths.2 rep bank
  have bounds:=extract_bounds r z (run compiled (r,z)).val
  have cap:2*z.len≤r := rows.length.symm ▸ matching_capacity r E hm hr
  have arithmeticWork:=polynomial_work r z.len cap
  have arithmeticPeak:=polynomial_peak r z.len cap
  rw [program_run]
  refine ⟨u,actual,⟨valid,bounds.1⟩,rep,read.1,read.2,widths,axis,?_,?_⟩
  · change (run compiled (r,z)).work+_+5≤_
    have w: (run compiled (r,z)).work≤200025+204*heapSize r z.len+
        runtime r z.len*(35*(862+heapSize r z.len)+435) := by
      simpa only [←rows.length] using work
    have geometry:heapSize r z.len=867+3*z.len+3*r := by
      unfold heapSize wordBound A U W P;omega
    rw [geometry] at w
    unfold runtime at w
    have readWork:=bounds.2.1
    omega
  · change max (run compiled (r,z)).peak _≤_
    have p:(run compiled (r,z)).peak≤
        max (2*heapSize r z.len+2000) (runtime r z.len) := by
      simpa only [←rows.length] using peak
    have geometry:heapSize r z.len=867+3*z.len+3*r := by
      unfold heapSize wordBound A U W P;omega
    have q:=max_le_max p bounds.2.2
    rw [geometry] at q
    unfold runtime P at q
    exact q.trans arithmeticPeak

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
