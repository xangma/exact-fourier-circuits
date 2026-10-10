import DFTModelSectorMapCarryProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapCarry
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def Ordered (d : Tape (ℕ×ℕ)) : Prop :=
  ∀ i j, i ≤ j → j < d.len → start d i ≤ start d j
def Bracket (d : Tape (ℕ×ℕ)) (t l h : ℕ) : Prop :=
  l ≤ h  ∧  h ≤ d.len  ∧  (∀ i, i < l → start d i ≤ t)  ∧
    (∀ i, h ≤ i → i < d.len → t < start d i)
def Cut (d : Tape (ℕ×ℕ)) (t s : ℕ) : Prop := Bracket d t s s

theorem mid_bounds (l h : ℕ) (hh : l < h) : l ≤ mid l h  ∧  mid l h < h := by
  dsimp [mid]
  omega

theorem left_bracket (d : Tape (ℕ×ℕ)) (t l h : ℕ) (ho : Ordered d)
    (hb : Bracket d t l h) (hh : l < h) (ht : t < start d (mid l h)) :
    Bracket d t l (mid l h) := by
  obtain ⟨hlm,hmh⟩:=mid_bounds l h hh
  obtain ⟨hlh,hlen,hlo,hhi⟩:=hb
  refine ⟨hlm,by omega,hlo,?_⟩
  intro i hi hin
  exact ht.trans_le (ho _ _ hi hin)

theorem right_bracket (d : Tape (ℕ×ℕ)) (t l h : ℕ) (ho : Ordered d)
    (hb : Bracket d t l h) (hh : l < h) (ht : ¬t < start d (mid l h)) :
    Bracket d t (mid l h+1) h := by
  obtain ⟨hlm,hmh⟩:=mid_bounds l h hh
  obtain ⟨hlh,hlen,hlo,hhi⟩:=hb
  refine ⟨by omega,hlen,?_,hhi⟩
  intro i hi
  exact (ho i (mid l h) (by omega) (by omega)).trans (by omega)

theorem mid_shrink (l h k : ℕ) (hh : l < h) (hw : h-l < 2^(k+1)) :
    mid l h-l < 2^k  ∧  h-(mid l h+1) < 2^k := by
  dsimp [mid]
  rw [pow_succ] at hw
  omega

attribute [local irreducible] searchAux

theorem searchAux_spec (k fuel : ℕ) (d : Tape (ℕ×ℕ)) (t l h : ℕ)
    (ho : Ordered d) (hb : Bracket d t l h) (hw : h-l < 2^k) (hf : k < fuel) :
    Cut d t (searchAux fuel d t l h).val  ∧
    (searchAux fuel d t l h).valid  ∧
    (searchAux fuel d t l h).work ≤ 70*k+14  ∧
    (searchAux fuel d t l h).peak ≤ max fuel (d.len+2) := by
  induction k generalizing fuel l h with
  | zero =>
    have he : l=h := by simp only [pow_zero] at hw; obtain ⟨_,_,_,_⟩:=hb;omega
    subst h
    cases fuel with
    | zero => omega
    | succ f =>
      rw [searchAux_stop]
      dsimp only
      exact ⟨hb,trivial,by omega,le_max_left _ _⟩
  | succ k ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      by_cases he : l=h
      · subst h
        rw [searchAux_stop]
        dsimp only
        exact ⟨hb,trivial,by omega,le_max_left _ _⟩
      · have hh : l < h := by have h:=hb.1;omega
        obtain ⟨hlm,hmh⟩:=mid_bounds l h hh
        obtain ⟨hwl,hwr⟩:=mid_shrink l h k hh hw
        by_cases ht : t < start d (mid l h)
        · obtain ⟨hv,hd,hwork,hpeak⟩:=ih f l (mid l h)
            (left_bracket d t l h ho hb hh ht) hwl (by omega)
          rw [searchAux_left _ _ _ _ _ hh ht]
          dsimp only [Bill.pay]
          refine ⟨hv,hd,by omega,?_⟩
          have hlen:=hb.2.1
          exact max_le (hpeak.trans (max_le_max (by omega) (le_refl _)))
            (max_le (max_le (by omega) (by omega)) (max_le (by omega) (le_max_left _ _)))
        · obtain ⟨hv,hd,hwork,hpeak⟩:=ih f (mid l h+1) h
            (right_bracket d t l h ho hb hh ht) hwr (by omega)
          rw [searchAux_right _ _ _ _ _ hh ht]
          dsimp only [Bill.pay]
          refine ⟨hv,hd,by omega,?_⟩
          have hlen:=hb.2.1
          exact max_le (hpeak.trans (max_le_max (by omega) (le_refl _)))
            (max_le (max_le (by omega) (by omega)) (max_le (by omega) (le_max_left _ _)))

theorem closedSearch_spec (d : Tape (ℕ×ℕ)) (t : ℕ) (ho : Ordered d) :
    Cut d t (run closedSearch (d,t)).val  ∧
    (run closedSearch (d,t)).valid  ∧
    (run closedSearch (d,t)).work ≤ 70*Nat.clog 2 (d.len+1)+31  ∧
    (run closedSearch (d,t)).peak ≤ d.len+2 := by
  have hb : Bracket d t 0 d.len := by
    refine ⟨by omega,le_refl _,?_,?_⟩ <;> intro i hi <;> omega
  have hw : d.len-0 < 2^Nat.clog 2 (d.len+1) := by
    have h:=Nat.le_pow_clog (by decide : 1 < 2) (d.len+1)
    omega
  have hf : Nat.clog 2 (d.len+1) < d.len+1 := by
    have h : d.len+1 ≤ 2^d.len := by have h:=Nat.lt_two_pow_self (n:=d.len);omega
    have h':=Nat.clog_le_of_le_pow h
    omega
  obtain ⟨hv,hd,hh,hp⟩:=searchAux_spec (Nat.clog 2 (d.len+1)) (d.len+1) d t 0 d.len ho hb hw hf
  rw [closedSearch_run]
  dsimp only [Bill.pay]
  exact ⟨hv,hd,by omega,max_le (hp.trans (by omega)) (by omega)⟩

end
end ExactFourierCircuits.DFTModelSectorMapCarry
