import DFTModelResidualBlockXor

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualPeakBlock
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualBlockXor DFTModelResidualCore
noncomputable section

theorem evolve_place (q : ℕ) (z : Acc.T) (h : ℕ) :
    (evolve q z h).2.1=z.2.1*(2^q)^h := by
  induction h with
  | zero => simp [evolve]
  | succ h ih => simp only [evolve,step,ih,Nat.pow_succ];ring

theorem body_peak (q m a b i : ℕ) (z : Acc.T) (R : ℕ)
    (ha : z.1.1≤R) (hb : z.1.2≤R) (hp : z.2.1*2^q≤R)
    (hc : (step q z).2.2≤R) (hn : 2^q*2^q≤R) :
    (run body (input q m a b,(i,z))).peak≤R := by
  rcases z with ⟨⟨l,r⟩,⟨p,c⟩⟩
  dsimp only [Ty.T] at *
  have pos:=Nat.two_pow_pos q
  have lm:=Nat.mod_lt l pos
  have rm:=Nat.mod_lt r pos
  have ld:=Nat.div_le_self l (2^q)
  have rd:=Nat.div_le_self r (2^q)
  have ix : (l % (2^q)) * (2^q) + (r % (2^q)) < (2^q)*(2^q) := by
    have h:=Nat.mul_le_mul_right (2^q) (Nat.succ_le_iff.mpr lm)
    simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at h
    exact (Nat.add_lt_add_left rm _).trans_le h
  have indexBound:=ix.le.trans hn
  have ht:=DFTModelResidualTable.table_look q (l%2^q) (r%2^q) lm rm
  change c+(l%2^q^^^r%2^q)*p≤R at hc
  have product : (l%2^q^^^r%2^q)*p≤R := (Nat.le_add_left _ _).trans hc
  have mul : l%2^q*2^q≤R := (Nat.le_add_right _ _).trans ix.le |>.trans hn
  have smallL : l%2^q≤R := lm.le.trans ((Nat.le_mul_of_pos_right _ pos).trans hn)
  have smallR : r%2^q≤R := rm.le.trans ((Nat.le_mul_of_pos_right _ pos).trans hn)
  simp only [body,left,right,place,accumulated,digit,old,table,radix,binary,input,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,ht,max_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem steps_peak (q m a b h : ℕ) (hh : h ≤ m)
    (ha : a < 2^(q*m)) (hb : b < 2^(q*m)) :
    (steps (input q m a b) ((a,b),(1,0)) h).peak≤2^(q*m)+2^q*2^q+m+2 := by
  induction h with
  | zero => change 0≤_;omega
  | succ h ih =>
    have prior:=ih (by omega)
    have hv:=steps_value q m a b ((a,b),(1,0)) h
    have halves:=evolve_halves q ((a,b),(1,0)) h
    have pl:=evolve_place q ((a,b),(1,0)) h
    have inv:=evolve_invariant q ((a,b),(1,0)) (h+1)
    have xor:=Nat.xor_lt_two_pow ha hb
    have next : (step q (evolve q ((a,b),(1,0)) h)).2.2≤2^(q*m)+2^q*2^q+m+2 := by
      change (evolve q ((a,b),(1,0)) (h+1)).2.2≤_
      calc
        _ ≤ (evolve q ((a,b),(1,0)) (h+1)).2.2+
            (evolve q ((a,b),(1,0)) (h+1)).2.1*
              ((evolve q ((a,b),(1,0)) (h+1)).1.1^^^(evolve q ((a,b),(1,0)) (h+1)).1.2) := Nat.le_add_right _ _
        _ = a^^^b := by simpa only [Nat.one_mul,Nat.zero_add] using inv
        _ ≤ _ := by omega
    have pb : (evolve q ((a,b),(1,0)) h).2.1*2^q≤2^(q*m)+2^q*2^q+m+2 := by
      rw [pl]
      dsimp only
      rw [Nat.one_mul,←Nat.pow_succ,←Nat.pow_mul]
      have exp : q*(h+1)≤q*m := Nat.mul_le_mul_left q hh
      exact (Nat.pow_le_pow_right (by decide) exp).trans (by omega)
    have one:=body_peak q m a b h (evolve q ((a,b),(1,0)) h)
      (2^(q*m)+2^q*2^q+m+2)
      (by rw [halves.1];exact (Nat.div_le_self a _).trans ha.le |>.trans (by omega))
      (by rw [halves.2];exact (Nat.div_le_self b _).trans hb.le |>.trans (by omega)) pb next (by omega)
    change max (max (steps (input q m a b) ((a,b),(1,0)) h).peak
      (run body (input q m a b,(h,(steps (input q m a b) ((a,b),(1,0)) h).val))).peak) (h+1)≤_
    rw [hv]
    omega

theorem program_peak (q m a b : ℕ) (ha : a < 2^(q*m)) (hb : b < 2^(q*m)) :
    (run program (input q m a b)).peak≤2^(q*m)+2^q*2^q+m+2 := by
  have h:=steps_peak q m a b m le_rfl ha hb
  have lb : (run loop (input q m a b)).peak≤2^(q*m)+2^q*2^q+m+2 := by
    change max (max 0 (max (max 0 (max 1 (max 0 0)))
      (steps (input q m a b) ((a,b),(1,0)) m).peak)) 0≤_
    omega
  simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero] using lb

end
end ExactFourierCircuits.DFTModelResidualPeakBlock
