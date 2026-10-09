import DFTModelRecursiveYMovement

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveYMovement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

attribute [local irreducible] DFTModelResidualBlockXor.program

theorem argument_peak (t : Ty) (q m k R r a j B : ℕ) (v : Tape t.T)
    (extent : R*2^k≤B) (rr : r<R) (jj : j<R*2^k) (_maskSmall : a<2^k)
    (roles : R≤B) :
    (run (argument t) (input t q m (2^k) r a v,j)).peak≤2*B := by
  have vp:=Nat.two_pow_pos k
  have quotientSmall : j/2^k<R := (Nat.div_lt_iff_lt_mul vp).2 (by simpa [Nat.mul_comm] using jj)
  have remainderSmall:=Nat.mod_lt j vp
  have volumeBound : 2^k≤B := (Nat.le_mul_of_pos_left _ (by omega : 0<R)).trans extent
  have leftBound:=Nat.sub_le (j/2^k) r
  have rightBound:=Nat.sub_le r (j/2^k)
  by_cases eq:j/2^k-r=0 ∧ r-j/2^k=0 <;>
    simp [argument,blocks,radix,table,remainder,selectedMask,difference,quotient,
      role,volume,mask,binary,input,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,eq]
  all_goals repeat' apply And.intro
  all_goals omega

theorem cell_peak (t : Ty) (q m k R r a j B : ℕ) (v : Tape t.T)
    (extent : R*2^k≤B) (rr : r<R) (jj : j<R*2^k) (maskSmall : a<2^k)
    (roles : R≤B) (padded : 2^(q*m)≤B) (square : 2^q*2^q≤B)
    (width : m≤B) (native : k≤q*m) :
    (run (cell t) (input t q m (2^k) r a v,j)).peak≤4*B+2 := by
  have vp:=Nat.two_pow_pos k
  have rem:=Nat.mod_lt j vp
  have qs : j/2^k<R := (Nat.div_lt_iff_lt_mul vp).2 (by simpa [Nat.mul_comm] using jj)
  have vb : 2^k≤B := (Nat.le_mul_of_pos_left _ (by omega : 0<R)).trans extent
  have pad : 2^k≤2^(q*m) := Nat.pow_le_pow_right (by decide) native
  have cm : chosen (2^k) r a j<2^k := by
    unfold chosen;split_ifs
    · exact maskSmall
    · exact vp
  have blockBound:=DFTModelResidualPeakBlock.program_peak q m (j%2^k)
    (chosen (2^k) r a j) (rem.trans_le pad) (cm.trans_le pad)
  have argBound:=argument_peak t q m k R r a j B v extent rr jj maskSmall roles
  have shiftPeak : (run (shifted t) (input t q m (2^k) r a v,j)).peak≤3*B+2 := by
    change max (max (run (argument t) (input t q m (2^k) r a v,j)).peak
      (run DFTModelResidualBlockXor.program
        (run (argument t) (input t q m (2^k) r a v,j)).val).peak) 0≤_
    rw [argument_value]
    apply max_le (max_le (argBound.trans (by omega)) (blockBound.trans (by omega))) (by omega)
  have shiftValue : (run (shifted t) (input t q m (2^k) r a v,j)).val=
      j%2^k^^^chosen (2^k) r a j := by
    change (run DFTModelResidualBlockXor.program
      (run (argument t) (input t q m (2^k) r a v,j)).val).val=_
    rw [argument_value]
    exact DFTModelResidualBlockXor.program_value q m _ _ (rem.trans_le pad) (cm.trans_le pad)
  have xs:=Nat.xor_lt_two_pow rem cm
  have product : j/2^k*2^k≤B := by
    exact (Nat.mul_le_mul_right _ qs.le).trans extent
  have total : j/2^k*2^k+(j%2^k^^^chosen (2^k) r a j)≤B := by
    have h:=Nat.mul_le_mul_right (2^k) (Nat.succ_le_iff.mpr qs)
    dsimp only [Nat.succ_eq_add_one] at h
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  simp only [cell,address,bank,quotient,volume,binary,input,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  dsimp only [input,run] at shiftPeak shiftValue
  rw [shiftValue]
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem program_peak (t : Ty) (q m k R r a B : ℕ) (v : Tape t.T)
    (len : v.len=R*2^k) (extent : R*2^k≤B) (rr : r<R) (maskSmall : a<2^k)
    (roles : R≤B) (padded : 2^(q*m)≤B) (square : 2^q*2^q≤B)
    (width : m≤B) (native : k≤q*m) :
    (run (program t) (input t q m (2^k) r a v)).peak≤4*B+2 := by
  change (((run (length t) (input t q m (2^k) r a v)).pass (fun L=>
    Bill.tab L t.blank (fun j=>run (cell t) (input t q m (2^k) r a v,j)))).pay 1 0).peak≤_
  simp only [length,input,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  simp only [max_zero,zero_max]
  change max v.len (Bill.tab v.len t.blank
    (fun j=>run (cell t) (input t q m (2^k) r a v,j))).peak≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_le_iff]
  refine ⟨by omega,⟨by omega,?_⟩⟩
  apply Finset.sup_le
  intro j hj
  exact cell_peak t q m k R r a j B v extent rr (by simpa [len] using Finset.mem_range.mp hj)
    maskSmall roles padded square width native

end
end ExactFourierCircuits.DFTModelRecursiveYMovement
