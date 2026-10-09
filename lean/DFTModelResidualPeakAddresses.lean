import DFTModelResidualPeakBlock
import DFTModelResidualAddressProof

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualPeakAddresses
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore DFTModelResidualAddresses
noncomputable section
attribute [local irreducible] DFTModelResidualTable.program

theorem argument_peak (q m h : ℕ) (images v : Tape ℕ) (j : ℕ) (hv : 0<v.len) :
    (run argument (((parameters q m images,h),v),j)).peak≤v.len+1 := by
  have mod:=Nat.mod_lt j hv
  by_cases hj:j<v.len <;>
    simp only [argument,context,oldRead,old,length,mask,image,parameters,binary,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,
      hj,↓reduceIte,one_ne_zero,max_le_iff]
  all_goals repeat' apply And.intro
  all_goals omega

theorem cell_peak (q m h : ℕ) (images v : Tape ℕ) (j : ℕ)
    (hv : 0<v.len) (small : ∀i,i<v.len→v.look i 0<2^(q*m))
    (im : images.look h 0<2^(q*m)) :
    (run cell (((parameters q m images,h),v),j)).peak≤
      2^(q*m)+2^q*2^q+m+v.len+2 := by
  have arg : (run argument (((parameters q m images,h),v),j)).val=
      DFTModelResidualBlockXor.input q m (v.look (j%v.len) 0)
        (if j<v.len then 0 else images.look h 0) := by
    by_cases hj:j<v.len <;>
      simp [argument,context,oldRead,old,length,mask,image,parameters,
        DFTModelResidualBlockXor.input,binary,run,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,hj]
  have a:=argument_peak q m h images v j hv
  have b:=DFTModelResidualPeakBlock.program_peak q m (v.look (j%v.len) 0)
    (if j<v.len then 0 else images.look h 0)
    (small _ (Nat.mod_lt j hv)) (by split_ifs;exact Nat.two_pow_pos _;exact im)
  change max (max (run argument (((parameters q m images,h),v),j)).peak
    (run DFTModelResidualBlockXor.program (run argument (((parameters q m images,h),v),j)).val).peak) 0≤_
  rw [arg]
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem grow_peak (q m h : ℕ) (images v : Tape ℕ)
    (hv : 0<v.len) (small : ∀i,i<v.len→v.look i 0<2^(q*m))
    (im : images.look h 0<2^(q*m)) :
    (run grow ((parameters q m images,h),v)).peak≤
      2^(q*m)+2^q*2^q+m+2*v.len+2 := by
  have cells : (Finset.range (v.len*2)).sup
      (fun j=>(run cell (((parameters q m images,h),v),j)).peak)≤
      2^(q*m)+2^q*2^q+m+v.len+2 := by
    apply Finset.sup_le
    intro j _
    exact cell_peak q m h images v j hv small im
  simp only [grow,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  rw [ModelEquivalenceInterpreter.tab_peak]
  change (Finset.range (v.len*2)).sup (fun j=>(Code.run cell () (((parameters q m images,h),v),j)).peak) ≤ _ at cells
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem steps_peak (q m k h : ℕ) (images : Tape ℕ) (hk : h ≤ k)
    (small : ∀i,i < k →images.look i 0<2^(q*m)) :
    (steps (k,parameters q m images) h).peak≤2^(q*m)+2^q*2^q+m+2^h+2 := by
  have positive:=Nat.two_pow_pos (q*m)
  induction h with
  | zero => change 0≤_;exact Nat.zero_le _
  | succ h ih =>
    have hh:h≤k:=by omega
    have prior:=ih hh
    have value:=steps_value q m k h images hh small
    have grown:=grow_peak q m h images (reference images h) (Nat.two_pow_pos h)
      (fun j _=>reference_small q m k h images hh small j) (small h (by omega))
    change max (max (steps (k,parameters q m images) h).peak
      (run body ((k,parameters q m images),(h,(steps (k,parameters q m images) h).val))).peak) (h+1)≤_
    rw [value]
    change (run grow ((parameters q m images,h),reference images h)).peak≤
      2^(q*m)+2^q*2^q+m+2*2^h+2 at grown
    have idx:h+1≤2^(h+1)+2 := (h+1).lt_two_pow_self.le.trans (by omega)
    change max (max (steps (k,parameters q m images) h).peak
      (max (max 0 (run grow ((parameters q m images,h),reference images h)).peak) 0)) (h+1)≤_
    have powpos:=Nat.two_pow_pos h
    rw [Nat.pow_succ] at idx ⊢
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega

theorem program_peak (q m k : ℕ) (images : Tape ℕ)
    (small : ∀i,i < k →images.look i 0<2^(q*m)) :
    (run program (k,parameters q m images)).peak≤2^(q*m)+2^q*2^q+m+2^k+2 := by
  have positive:=Nat.two_pow_pos (q*m)
  have powerpos:=Nat.two_pow_pos k
  have h:=steps_peak q m k k images le_rfl small
  have initial : (run DFTModelResidualAddresses.initial (k,parameters q m images)).peak=1 := by rfl
  change max (max 0 (max (run DFTModelResidualAddresses.initial (k,parameters q m images)).peak
    (steps (k,parameters q m images) k).peak)) 0≤_
  rw [initial]
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals omega

end
end ExactFourierCircuits.DFTModelResidualPeakAddresses
