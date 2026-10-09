import DFTModelWorkingHeadersSelection

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] aux prepend finish DFTModelRoot.prime

/-- Reference for the actual stopping scan; accepted candidates are prepended on return. -/
def scan (n p R : ℕ) : ℕ → PrimeResult.T
  | 0 => (0,Tape.empty ℕ)
  | fuel+1 =>
    if (UniformWorkingPreparation.trialPrime p).value=true then
      if 2*n<R*p then (R,Tape.empty ℕ)
      else let t := scan n (p+1) (R*p) fuel; (t.1,cons p t.2)
    else scan n (p+1) R fuel

theorem cons_len (p : ℕ) (v : Tape ℕ) : (cons p v).len=v.len+1 := rfl

theorem scan_len (n p R fuel : ℕ) : (scan n p R fuel).2.len≤fuel := by
  induction fuel generalizing p R with
  | zero => simp [scan,Tape.empty]
  | succ f ih =>
    simp only [scan]
    split
    · split
      · simp [Tape.empty]
      · change (scan n (p+1) (R*p) f).2.len+1≤f+1
        exact Nat.add_le_add_right (ih _ _) 1
    · exact (ih _ _).trans (by omega)

theorem aux_spec (n : ℕ) (hn : 0<n) (p j R fuel P : ℕ)
    (hR : R≤2*n) (h2 : 2≤P) (hf : fuel≤P) (hprod : 2*n*(p+fuel)≤P) :
    (aux fuel n p R).val=scan n p R fuel ∧
    (aux fuel n p R).work≤8*(UniformWorkingPreparation.selectLoop n p j R fuel).cost+
      17*(scan n p R fuel).2.len^2+100*(scan n p R fuel).2.len ∧
    (aux fuel n p R).peak≤P ∧ (aux fuel n p R).valid := by
  induction fuel generalizing p j R with
  | zero =>
    rw [aux_zero]
    simp [scan,Tape.empty,UniformWorkingPreparation.selectLoop]
  | succ f ih =>
    obtain ⟨pv,pw,pp,pd⟩ := DFTModelRoot.prime_spec p
    have pc := DFTModelRoot.totalCost_le_counted p
    have pwork : (run DFTModelRoot.prime p).work≤4*(UniformWorkingPreparation.trialPrime p).cost+20 := by omega
    have hsum : p+(f+1)≤P := by
      have hm := Nat.mul_le_mul_right (p+(f+1)) (show 1≤2*n by omega)
      simp only [Nat.one_mul] at hm
      exact hm.trans hprod
    have hp : p≤P := by omega
    have ppeak : (run DFTModelRoot.prime p).peak≤P := pp.trans (max_le h2 hp)
    have hnew : R*p≤P :=
      (Nat.mul_le_mul hR (show p≤p+(f+1) by omega)).trans hprod
    have hn2 : 2*n≤P := by
      have hm := Nat.mul_le_mul_left (2*n) (show 1≤p+(f+1) by omega)
      simp only [Nat.mul_one] at hm
      exact hm.trans hprod
    have childProd : 2*n*(p+1+f)≤P := by
      have he : p+1+f=p+(f+1) := by omega
      rw [he]
      exact hprod
    rw [aux_step]
    dsimp only [Bill.pass,Bill.pay]
    rw [pv]
    cases hc : (UniformWorkingPreparation.trialPrime p).value with
    | false =>
      obtain ⟨iv,iw,ip,id⟩ := ih (p+1) j R hR (by omega) childProd
      simp only [UniformPrimeMachine.boolCode,hc,Bool.false_eq_true,ite_false,ite_true,
        Nat.max_zero,UniformWorkingPreparation.selectLoop,scan]
      refine ⟨iv,by omega,?_,⟨pd,id⟩⟩
      exact max_le (max_le ppeak (max_le ip (by omega))) (by omega)
    | true =>
      by_cases hb : 2*n<R*p
      · simp only [UniformPrimeMachine.boolCode,hc,ite_true,Nat.one_ne_zero,ite_false,
          hb,Nat.max_zero,UniformWorkingPreparation.selectLoop,scan,Tape.empty]
        refine ⟨trivial,by omega,?_,⟨pd,True.intro⟩⟩
        exact max_le (max_le ppeak (max_le h2 (max_le hn2 hnew))) (by omega)
      · obtain ⟨iv,iw,ip,id⟩ := ih (p+1) (j+1) (R*p) (by omega) (by omega) childProd
        have fw := prepend_work p (scan n (p+1) (R*p) f).2
        have fp := prepend_peak p (scan n (p+1) (R*p) f).2
        have fd := prepend_valid p (scan n (p+1) (R*p) f).2
        have fl := scan_len n (p+1) (R*p) f
        generalize hchild : aux f n (p+1) (R*p)=child at iv iw ip id ⊢
        generalize hs : scan n (p+1) (R*p) f=t at iv iw fw fp fd fl ⊢
        obtain ⟨Q,v⟩ := t
        simp only [UniformPrimeMachine.boolCode,hc,ite_true,Nat.one_ne_zero,ite_false,
          hb,Nat.max_zero,UniformWorkingPreparation.selectLoop,scan]
        rw [hs]
        rw [iv,finish_run]
        dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid]
        have fv := prepend_value p v
        generalize hprep : run prepend (p,v)=prep at fw fp fd fv ⊢
        rw [fv]
        refine ⟨rfl,?_,?_,⟨pd,⟨id,fd⟩⟩⟩
        · simp only [cons_len]
          nlinarith
        · exact max_le (max_le ppeak
            (max_le (max_le ip (fp.trans (by omega)))
              (max_le h2 (max_le hn2 (max_le hnew (by omega)))))) (by omega)

end
end ExactFourierCircuits.DFTModelWorkingHeaders
