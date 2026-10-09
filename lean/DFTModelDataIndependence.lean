import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

/-! Homogeneous data values cannot affect typed control or resource bills. -/
namespace ExactFourierCircuits.DFTModelDataIndependence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Prepared scalars and words agree; homogeneous data may vary. -/
def Related : (t : Ty) → t.T → t.T → Prop
  | .w, x, y => x=y
  | .c .scalar, x, y => x=y
  | .c _, _, _ => True
  | .p s t, x, y => Related s x.1 y.1 ∧ Related t x.2 y.2
  | .a s, x, y => x.len=y.len ∧ ∀ i, Related s (x.look i s.blank) (y.look i s.blank)

theorem related_refl (t : Ty) (x : t.T) : Related t x x := by
  induction t with
  | w => rfl
  | c p => cases p <;> first | rfl | trivial
  | p s t hs ht => exact ⟨hs x.1,ht x.2⟩
  | a s hs => exact ⟨rfl,fun i => hs _⟩

/-- Equal bills except for related result values. -/
structure Bills (t : Ty) (x y : Bill t.T) : Prop where
  val : Related t x.val y.val
  work : x.work=y.work
  peak : x.peak=y.peak
  valid : x.valid=y.valid

theorem bills_one {t : Ty} {x y : t.T} (h : Related t x y) :
    Bills t (Bill.one x) (Bill.one y) := ⟨h,rfl,rfl,rfl⟩

theorem bills_word {x y : ℕ} (h : x=y) : Bills w (Bill.word x) (Bill.word y) := by
  subst y
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem bills_pay {t : Ty} {x y : Bill t.T} (h : Bills t x y) (n m : ℕ) :
    Bills t (x.pay n m) (y.pay n m) := by
  exact ⟨h.val,by simp [Bill.pay,h.work],by simp [Bill.pay,h.peak],h.valid⟩

theorem bills_pass {s t : Ty} {x y : Bill s.T} {f g : s.T → Bill t.T}
    (h : Bills s x y) (hf : ∀ a b,Related s a b → Bills t (f a) (g b)) :
    Bills t (x.pass f) (y.pass g) := by
  have hd := hf x.val y.val h.val
  exact ⟨hd.val,by simp [Bill.pass,h.work,hd.work],
    by simp [Bill.pass,h.peak,hd.peak],by simp [Bill.pass,h.valid,hd.valid]⟩

theorem tape_tab {t : Ty} (n : ℕ) {f g : ℕ → t.T}
    (h : ∀ i,Related t (f i) (g i)) : Related (a t) (Tape.tab n f) (Tape.tab n g) := by
  refine ⟨rfl,?_⟩
  intro i
  by_cases hi : i<n
  · simpa [Tape.look,Tape.tab,hi] using h i
  · simpa [Tape.look,Tape.tab,hi] using related_refl t t.blank

theorem tape_set_look {α : Type} (v : Tape α) (i : ℕ) (x z : α) (j : ℕ) :
    (v.set i x).look j z = if j=i ∧ j<v.len then x else v.look j z := by
  by_cases he : j=i
  · subst j
    by_cases hi : i<v.len <;> simp [Tape.look,Tape.set,hi]
  · by_cases hj : j<v.len <;> simp [Tape.look,Tape.set,hj,he]

theorem tape_set {t : Ty} {v u : Tape t.T} (h : Related (a t) v u)
    (i : ℕ) {x y : t.T} (hx : Related t x y) : Related (a t) (v.set i x) (u.set i y) := by
  refine ⟨h.1,?_⟩
  intro j
  rw [tape_set_look,tape_set_look,← h.1]
  split_ifs
  · exact hx
  · exact h.2 j

theorem bills_steps {t : Ty} {x y : t.T} {f g : ℕ → t.T → Bill t.T}
    (h : Related t x y)
    (hf : ∀ i a b,Related t a b → Bills t (f i a) (g i b)) (n : ℕ) :
    Bills t (Bill.steps x f n) (Bill.steps y g n) := by
  induction n with
  | zero => exact bills_one h
  | succ n ih => exact bills_pay (bills_pass ih (hf n)) 1 (n+1)

theorem bills_sow {t : Ty} (len count : ℕ) {x y : t.T} {f g : ℕ → Bill (ℕ × t.T)}
    (h : Related t x y) (hf : ∀ i,Bills (p w t) (f i) (g i)) :
    Bills (a t) (Bill.sow len count x f) (Bill.sow len count y g) := by
  apply bills_pay
  apply bills_steps (tape_tab len (fun _ => h))
  intro i u v huv
  apply bills_pass (hf i)
  intro z z0 hz
  apply bills_one
  have eq : z.1=z0.1 := hz.1
  rw [← eq]
  exact tape_set huv z.1 hz.2

theorem bills_tab {t : Ty} (len : ℕ) {x y : t.T} {f g : ℕ → Bill t.T}
    (h : Related t x y) (hf : ∀ i,Bills t (f i) (g i)) :
    Bills (a t) (Bill.tab len x f) (Bill.tab len y g) := by
  apply bills_sow len len h
  intro i
  apply bills_pass (hf i)
  intro z z0 hz
  exact bills_one ⟨rfl,hz⟩

end
end ExactFourierCircuits.DFTModelDataIndependence
