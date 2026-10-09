import DFTModelCRTRecursion

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem sow_value {α : Type} (L C : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) :
    (Bill.sow L C z f).val = Tape.sow L C z (fun j => (f j).val) := by
  suffices h : ∀ k, (Bill.steps (Tape.tab L (fun _ => z))
    (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).val =
      Tape.sow.iter L z (fun j => (f j).val) k from h C
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change (Bill.steps (Tape.tab L (fun _ => z))
        (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).val.set
          (f k).val.1 (f k).val.2 =
        (Tape.sow.iter L z (fun j => (f j).val) k).set (f k).val.1 (f k).val.2
      exact congrArg (fun t : Tape α => t.set (f k).val.1 (f k).val.2) ih

theorem sow_work {α : Type} (L C : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) :
    (Bill.sow L C z f).work = 2+L+2*C+∑j ∈ Finset.range C,(f j).work := by
  suffices h : ∀ k, (Bill.steps (Tape.tab L (fun _ => z))
    (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).work =
      1+2*k+∑j ∈ Finset.range k,(f j).work by
    change _+ (1+L) = _
    rw [h]
    omega
  intro k
  induction k with
  | zero => simp [Bill.steps,Bill.one]
  | succ k ih =>
      change (Bill.steps (Tape.tab L (fun _ => z))
        (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).work+
          ((f k).work+1)+1 = _
      rw [ih]
      rw [Finset.sum_range_succ]
      omega

theorem sow_peak {α : Type} (L C : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) :
    (Bill.sow L C z f).peak =
      max L (max C ((Finset.range C).sup (fun j => (f j).peak))) := by
  suffices h : ∀ k, (Bill.steps (Tape.tab L (fun _ => z))
    (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).peak =
      max k ((Finset.range k).sup (fun j => (f j).peak)) by
    change max _ L = _
    rw [h]
    omega
  intro k
  induction k with
  | zero => simp [Bill.steps,Bill.one]
  | succ k ih =>
      change max (max _ (max (f k).peak 0)) (k+1) = _
      rw [ih,Finset.range_add_one,Finset.sup_insert]
      omega

theorem sow_valid {α : Type} (L C : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) :
    (Bill.sow L C z f).valid ↔ ∀j<C,(f j).valid := by
  suffices h : ∀ k, (Bill.steps (Tape.tab L (fun _ => z))
    (fun i v => (f i).pass (fun s => Bill.one (v.set s.1 s.2))) k).valid ↔
      ∀j<k,(f j).valid from h C
  intro k
  induction k with
  | zero => simp [Bill.steps,Bill.one]
  | succ k ih =>
      change ((_ ∧ ((f k).valid ∧ True))) ↔ _
      rw [ih]
      simp only [and_true]
      constructor
      · rintro ⟨h,hk⟩ j hj
        by_cases he : j=k
        · simpa [he] using hk
        · exact h j (by omega)
      · intro h
        exact ⟨fun j hj => h j (by omega),h k (by omega)⟩

theorem alpha_value (t : Tape (ℕ × ℕ)) :
    (run alpha t).val = Tape.tab t.len (fun j => (t.look j (0,0)).1) := by
  change (Bill.tab t.len w.blank _).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem alpha_work (t : Tape (ℕ × ℕ)) : (run alpha t).work = 7*t.len+4 := by
  change 1+(Bill.tab t.len w.blank _).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem alpha_peak (t : Tape (ℕ × ℕ)) : (run alpha t).peak = t.len := by
  change max (max t.len (Bill.tab t.len w.blank _).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem alpha_valid (t : Tape (ℕ × ℕ)) : (run alpha t).valid := by
  change True ∧ (Bill.tab t.len w.blank _).valid
  rw [ModelEquivalenceInterpreter.tab_valid]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem inverse_value (t : Tape (ℕ × ℕ)) :
    (run inverseBeta t).val = Tape.sow t.len t.len 0
      (fun j => ((t.look j (0,0)).2,j)) := by
  change (Bill.sow t.len t.len w.blank _).val = _
  rw [sow_value]
  rfl

theorem inverse_work (t : Tape (ℕ × ℕ)) :
    (run inverseBeta t).work = 8*t.len+5 := by
  change 1+(1+(Bill.sow t.len t.len w.blank _).work)+1 = _
  rw [sow_work]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem inverse_peak (t : Tape (ℕ × ℕ)) :
    (run inverseBeta t).peak = t.len := by
  change max (max t.len (max t.len (Bill.sow t.len t.len w.blank _).peak)) 0 = _
  rw [sow_peak]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem inverse_valid (t : Tape (ℕ × ℕ)) : (run inverseBeta t).valid := by
  change True ∧ (True ∧ (Bill.sow t.len t.len w.blank _).valid)
  rw [sow_valid]
  simp [Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem sow_iter_len {α : Type} (V C : ℕ) (z : α) (f : ℕ → ℕ × α) :
    (Tape.sow.iter V z f C).len=V := by
  induction C with
  | zero => rfl
  | succ C ih => exact ih

theorem sow_permutation {V : ℕ} (beta : Fin V ≃ Fin V) (f : ℕ → ℕ)
    (hf : ∀j : Fin V, f j.val = (beta j).val) (k : Fin V) :
    (Tape.sow V V 0 (fun j => (f j,j))).look k.val 0 = (beta.symm k).val := by
  have hi : ∀ C, C≤V →
      (Tape.sow.iter V 0 (fun j => (f j,j)) C).look k.val 0 =
        if (beta.symm k).val<C then (beta.symm k).val else 0 := by
    intro C hC
    induction C with
    | zero => simp [Tape.sow.iter,Tape.tab,Tape.look,k.isLt]
    | succ C ih =>
        have hCV : C<V := by omega
        have len := sow_iter_len V C 0 (fun j => (f j,j))
        have write : (Tape.sow.iter V 0 (fun j => (f j,j)) (C+1)).look k.val 0 =
            if k.val=f C then C else
              (Tape.sow.iter V 0 (fun j => (f j,j)) C).look k.val 0 := by
          simp [Tape.sow.iter,Tape.set,Tape.look,len,k.isLt]
        have eq : k.val=f C ↔ (beta.symm k).val=C := by
          rw [hf ⟨C,hCV⟩]
          constructor
          · intro he
            have hk : k=beta ⟨C,hCV⟩ := Fin.ext he
            simp [hk]
          · intro he
            have hk : beta.symm k=⟨C,hCV⟩ := Fin.ext he
            exact congrArg Fin.val ((Equiv.symm_apply_eq beta).1 hk)
        rw [write,ih (by omega)]
        simp only [eq]
        split_ifs <;> omega
  simpa [Tape.sow,k.isLt] using hi V (by omega)

theorem inverse_permutation {V : ℕ} (t : Tape (ℕ × ℕ))
    (length : t.len=V) (beta : Fin V ≃ Fin V)
    (values : ∀j : Fin V,(t.look j.val (0,0)).2=(beta j).val) (k : Fin V) :
    (run inverseBeta t).val.look k.val 0 = (beta.symm k).val := by
  rw [inverse_value,length]
  exact sow_permutation beta _ values k

theorem program_work (k : ℕ) (x : Args.T) :
    (run program (k,x)).work =
      24+119*volumeSum k x+35*k+15*(prefixTable k x).len := by
  change (run tables (k,x)).work+
    ((run alpha (run tables (k,x)).val).work+
      (run inverseBeta (run tables (k,x)).val).work+1)+1 = _
  rw [tables_work,tables_value,alpha_work,inverse_work]
  omega

theorem program_valid (k : ℕ) (x : Args.T) : (run program (k,x)).valid := by
  change (run tables (k,x)).valid ∧
    ((run alpha (run tables (k,x)).val).valid ∧
      ((run inverseBeta (run tables (k,x)).val).valid ∧ True))
  exact ⟨tables_valid _ _,alpha_valid _,inverse_valid _,trivial⟩

end
end ExactFourierCircuits.DFTModelCRT
