import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelConjugation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def value : (t : Ty) → t.T → t.T
  | .w, x => x
  | .c _, x => star x
  | .p s t, x => (value s x.1, value t x.2)
  | .a t, x => x.map (value t)

def bill {α β : Type} (f : α → β) (b : Bill α) : Bill β :=
  ⟨f b.val,b.work,b.peak,b.valid⟩

@[simp] theorem bill_one {α β : Type} (f : α → β) (x : α) :
    bill f (Bill.one x)=Bill.one (f x) := rfl

@[simp] theorem bill_pay {α β : Type} (f : α → β) (b : Bill α) (n m : ℕ) :
    bill f (b.pay n m)=(bill f b).pay n m := rfl

theorem bill_pass {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (b : Bill α) (k : α → Bill γ) (l : β → Bill δ)
    (h : ∀x,l (f x)=bill g (k x)) :
    (bill f b).pass l=bill g (b.pass k) := by
  simp only [Bill.pass,bill,h]

@[simp] theorem map_tab {α β : Type} (f : α → β) (n : ℕ) (g : ℕ → α) :
    (Tape.tab n g).map f=Tape.tab n (fun i=>f (g i)) := rfl

@[simp] theorem map_set {α β : Type} (f : α → β) (t : Tape α) (i : ℕ) (x : α) :
    (t.set i x).map f=(t.map f).set i (f x) := by
  cases t
  simp only [Tape.set,Tape.map]
  congr 1
  funext j
  split <;> rfl

@[simp] theorem map_look {α β : Type} (f : α → β) (t : Tape α) (i : ℕ) (z : α) :
    (t.map f).look i (f z)=f (t.look i z) := by
  unfold Tape.look Tape.map
  split <;> rfl

@[simp] theorem value_blank (t : Ty) : value t t.blank=t.blank := by
  induction t with
  | w => rfl
  | c _ => exact star_zero _
  | p s t hs ht => exact congrArg₂ Prod.mk hs ht
  | a t _ =>
    unfold value Ty.blank Tape.map Tape.empty
    congr 1
    funext i
    exact Fin.elim0 i

theorem steps {α β : Type} (f : α → β) (z : α)
    (a : ℕ → α → Bill α) (b : ℕ → β → Bill β)
    (h : ∀i x,b i (f x)=bill f (a i x)) (n : ℕ) :
    Bill.steps (f z) b n=bill f (Bill.steps z a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Bill.steps,ih]
    exact congrArg (fun q=>q.pay 1 (n+1)) (bill_pass f f _ _ _ (h n))

theorem sow {α β : Type} (f : α → β) (len count : ℕ) (z : α)
    (a : ℕ → Bill (ℕ × α)) (b : ℕ → Bill (ℕ × β))
    (h : ∀i,b i=bill (fun x=>(x.1,f x.2)) (a i)) :
    Bill.sow len count (f z) b=bill (Tape.map f) (Bill.sow len count z a) := by
  unfold Bill.sow
  rw [show Tape.tab len (fun _=>f z)=(Tape.tab len (fun _=>z)).map f from rfl]
  rw [steps (Tape.map f) _ _ _ ?_ count]
  · rfl
  · intro i v
    rw [h i]
    apply bill_pass
    intro x
    simp only [bill_one,map_set]

theorem tab {α β : Type} (f : α → β) (len : ℕ) (z : α)
    (a : ℕ → Bill α) (b : ℕ → Bill β)
    (h : ∀i,b i=bill f (a i)) :
    Bill.tab len (f z) b=bill (Tape.map f) (Bill.tab len z a) := by
  unfold Bill.tab
  apply sow
  intro i
  rw [h i]
  apply bill_pass
  intro x
  rfl

end
end ExactFourierCircuits.DFTModelConjugation
