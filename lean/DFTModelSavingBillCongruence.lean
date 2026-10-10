import DFTModelSavingControl

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBillCongruence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
noncomputable section

/-- Observable value and charged work, without asserting equal fuel peaks. -/
def Related {α : Type} (a b : Bill α) : Prop := a.val=b.val ∧ a.work=b.work

lemma refl {α : Type} (a : Bill α) : Related a a:=⟨rfl,rfl⟩

lemma pay {α : Type} {a b : Bill α} (h : Related a b) (n m : ℕ) :
    Related (a.pay n m) (b.pay n m) :=
  ⟨h.1,congrArg (fun w=>w+n) h.2⟩

lemma pass {α β : Type} {a b : Bill α} {f g : α→Bill β}
    (h : Related a b) (next : ∀x,Related (f x) (g x)) :
    Related (a.pass f) (b.pass g) := by
  constructor
  · change (f a.val).val=(g b.val).val
    rw [h.1]
    exact (next b.val).1
  · change a.work+(f a.val).work=b.work+(g b.val).work
    rw [h.1,h.2,(next b.val).2]

lemma pass_at {α β : Type} {a b : Bill α} {f g : α→Bill β}
    (h : Related a b) (next : Related (f a.val) (g a.val)) :
    Related (a.pass f) (b.pass g) := by
  constructor
  · change (f a.val).val=(g b.val).val
    rw [←h.1]
    exact next.1
  · change a.work+(f a.val).work=b.work+(g b.val).work
    rw [←h.1,←h.2,next.2]

lemma comp_at {s t u : Ty} (f : Code false ChildPort s t) (g : Code false ChildPort t u)
    (h h' : Handler ChildPort) (x : s.T)
    (first : Related (f.run h x) (f.run h' x))
    (next : Related (g.run h (f.run h x).val) (g.run h' (f.run h x).val)) :
    Related ((Code.comp f g).run h x) ((Code.comp f g).run h' x) :=
  pay (pass_at first next) 1 0

lemma steps {α : Type} (x : α) (f g : ℕ→α→Bill α) (n : ℕ)
    (same : ∀i<n,∀z,Related (f i z) (g i z)) :
    Related (Bill.steps x f n) (Bill.steps x g n) := by
  induction n with
  | zero=>exact refl _
  | succ n ih=>
    exact pay (pass (ih (fun i hi z=>same i (by omega) z))
      (same n (by omega))) 1 (n+1)

lemma closed {s t : Ty} (f : Prog false s t) (h h' : Handler ChildPort) (x : s.T) :
    Related ((Code.importClosed f).run h x) ((Code.importClosed f).run h' x):=refl _

lemma comp {s t u : Ty} (f : Code false ChildPort s t) (g : Code false ChildPort t u)
    (h h' : Handler ChildPort) (x : s.T)
    (first : Related (f.run h x) (f.run h' x))
    (next : ∀y,Related (g.run h y) (g.run h' y)) :
    Related ((Code.comp f g).run h x) ((Code.comp f g).run h' x) :=
  pay (pass first next) 1 0

lemma fork {s t u : Ty} (f : Code false ChildPort s t) (g : Code false ChildPort s u)
    (h h' : Handler ChildPort) (x : s.T)
    (first : Related (f.run h x) (f.run h' x))
    (second : Related (g.run h x) (g.run h' x)) :
    Related ((Code.fork f g).run h x) ((Code.fork f g).run h' x) := by
  apply pass first
  intro y
  apply pass second
  intro z
  exact refl _

lemma ifz_closed {s t : Ty} (test : Prog false s w)
    (f g : Code false ChildPort s t) (h h' : Handler ChildPort) (x : s.T)
    (left : Related (f.run h x) (f.run h' x))
    (right : Related (g.run h x) (g.run h' x)) :
    Related ((Code.ifz (.importClosed test) f g).run h x)
      ((Code.ifz (.importClosed test) f g).run h' x) := by
  apply pay
  apply pass (closed test h h' x)
  intro z
  split_ifs <;> assumption

end
end ExactFourierCircuits.DFTModelSavingBillCongruence
