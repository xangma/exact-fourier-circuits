import DFTModelCacheCompactSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheCompact
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

attribute [local irreducible] DFTModelCacheAxisRoots.program localProgram

def rawProgram : Prog false (p w sc) (Ty.a (Ty.a sc)) :=
  .comp DFTModelCacheAxisRoots.program (DFTModelCacheOddAxes.applyOdd localProgram)

def values (n : ℕ) : Tape (Tape ℂ) :=
  Tape.tab (UniformWorkingLength.axisCount n) (fun j=>
    Tape.tab (5*UniformWorkingLength.oddPrime j)
      (expected (pairValues (UniformWorkingLength.oddPrime j)
        (OAI.ExactFourier.zeta (UniformWorkingLength.oddPrime j)))))

def budget (n : ℕ) : ℕ := DFTModelCacheAxisRoots.budget n+9+
  6*UniformWorkingLength.axisCount n+
  ∑j∈Finset.range (UniformWorkingLength.axisCount n),
    (200*(UniformWorkingLength.oddPrime j+1)^2+1000*(UniformWorkingLength.oddPrime j+1)+1)

theorem raw_value (n : ℕ) (hn : 0<n) :
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n := by
  change (run (DFTModelCacheOddAxes.applyOdd localProgram)
    (run DFTModelCacheAxisRoots.program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val).val=_
  rw [DFTModelCacheAxisRoots.selected_value n hn,DFTModelCacheOddAxes.apply_value]
  change Tape.tab (UniformWorkingLength.axisCount n) _=values n
  unfold values
  apply DFTModelCacheLiteral.tab_ext
  intro j hj
  rw [DFTModelCacheOddAxes.root_lookup n j hj,
    local_value _ _ (UniformWorkingLength.oddPrime_prime j).pos]

theorem raw_valid (n : ℕ) (hn : 0<n) :
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid := by
  change (run DFTModelCacheAxisRoots.program _).valid ∧
    (run (DFTModelCacheOddAxes.applyOdd localProgram) (run DFTModelCacheAxisRoots.program _).val).valid
  refine ⟨DFTModelCacheAxisRoots.selected_valid n hn _,?_⟩
  rw [DFTModelCacheAxisRoots.selected_value n hn]
  apply DFTModelCacheOddAxes.apply_valid
  intro j hj
  change j<UniformWorkingLength.axisCount n at hj
  rw [DFTModelCacheOddAxes.root_lookup n j hj]
  exact local_valid _ (UniformWorkingLength.oddPrime_prime j).pos _
    (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt (UniformWorkingLength.oddPrime_prime j).pos))

theorem raw_work (n : ℕ) (hn : 0<n) :
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤budget n := by
  change (run DFTModelCacheAxisRoots.program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work+
    (run (DFTModelCacheOddAxes.applyOdd localProgram)
      (run DFTModelCacheAxisRoots.program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val).work+1≤_
  rw [DFTModelCacheAxisRoots.selected_value n hn,DFTModelCacheOddAxes.apply_work]
  have hlen : (DFTModelCacheAxisRoots.values n).len-1=UniformWorkingLength.axisCount n := rfl
  rw [hlen]
  have hr:=DFTModelCacheAxisRoots.selected_work n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have hs : (∑j∈Finset.range (UniformWorkingLength.axisCount n),
      (run localProgram ((DFTModelCacheAxisRoots.values n).look j (0,0))).work)≤
      ∑j∈Finset.range (UniformWorkingLength.axisCount n),
        (200*(UniformWorkingLength.oddPrime j+1)^2+1000*(UniformWorkingLength.oddPrime j+1)+1) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [DFTModelCacheOddAxes.root_lookup n j (Finset.mem_range.mp hj)]
    exact local_work _ _
  unfold budget
  omega

theorem raw_peak (n : ℕ) (hn : 0<n) :
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^14 := by
  have hr:=DFTModelCacheAxisRoots.selected_peak n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have hc:=DFTModelCRTMetadata.selected_count_le hn
  have hv:=(UniformWorkingLength.workingLength_upper hn).le
  change UniformCRTTraversalCycle.len n≤4*n at hv
  have hb : 5*(4*n+1)≤(n+2)^14 := by
    have h3 : 5*(4*n+1)≤(n+2)^4 := by nlinarith [sq_nonneg (n*n)]
    exact h3.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpow : (n+2)^13≤(n+2)^14 := Nat.pow_le_pow_right (by omega) (by omega)
  change max (max (run DFTModelCacheAxisRoots.program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak
    (run (DFTModelCacheOddAxes.applyOdd localProgram)
      (run DFTModelCacheAxisRoots.program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val).peak) 0≤_
  refine max_le (max_le (hr.trans hpow) ?_) (Nat.zero_le _)
  rw [DFTModelCacheAxisRoots.selected_value n hn]
  apply DFTModelCacheOddAxes.apply_peak
  · change UniformWorkingLength.axisCount n+1≤_;omega
  · exact Nat.one_le_pow _ _ (by omega)
  · intro j hj
    change j<UniformWorkingLength.axisCount n at hj
    rw [DFTModelCacheOddAxes.root_lookup n j hj]
    exact (local_peak _ _).trans (by
      have h:=DFTModelCacheOddAxes.odd_prime_le_length n j hn hj
      omega)

theorem raw_lane (n : ℕ) (hn : 0<n) (i : Fin (UniformWorkingLength.axisCount n))
    (q : Fin 5) (j : Fin (UniformWorkingLength.oddPrime i.val)) :
    ((run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.look
      i.val (Tape.empty ℂ)).look (q.val*UniformWorkingLength.oddPrime i.val+j.val) 0=
      UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta (UniformWorkingLength.oddPrime i.val)) q j.val := by
  rw [raw_value n hn]
  have outer := Tape.look_of_lt (values n) (Tape.empty ℂ) i.isLt
  rw [outer]
  change (Tape.tab _ _).look _ _=_
  rw [←local_value _ _ (UniformWorkingLength.oddPrime_prime i.val).pos]
  exact lane_value _ _ q j

theorem specification (n : ℕ) (hn : 0<n) :
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n ∧
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid ∧
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤budget n ∧
    (run rawProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^14 :=
  ⟨raw_value n hn,raw_valid n hn,raw_work n hn,raw_peak n hn⟩

end
end ExactFourierCircuits.DFTModelCacheCompact
