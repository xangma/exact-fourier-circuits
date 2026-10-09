import DFTModelDataIndependence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelDataIndependence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem atom_run {s t : Ty} (f : Atom false s t) {x y : s.T}
    (h : Related s x y) : Bills t (f.run x) (f.run y) := by
  cases f with
  | lit n => exact bills_word rfl
  | int op =>
    have eq : x=y := Prod.ext h.1 h.2
    subst y
    exact ⟨rfl,rfl,rfl,rfl⟩
  | cz paint => exact bills_one (related_refl _ _)
  | cone => exact bills_one rfl
  | add paint =>
    cases paint <;> apply bills_one
    · exact congrArg₂ (fun a b : ℂ => a+b) h.1 h.2
    all_goals trivial
  | sub paint =>
    cases paint <;> apply bills_one
    · exact congrArg₂ (fun a b : ℂ => a-b) h.1 h.2
    all_goals trivial
  | scale paint =>
    cases paint <;> apply bills_one
    · exact congrArg₂ (fun a b : ℂ => a*b) h.1 h.2
    all_goals trivial
  | inv =>
    have eq : x=y := h
    subst y
    exact ⟨rfl,rfl,rfl,rfl⟩
  | cross impossible => cases impossible
  | id => exact bills_one h
  | fst => exact bills_one h.1
  | snd => exact bills_one h.2
  | len => exact bills_word h.1
  | look =>
    apply bills_one
    have eq : x.2=y.2 := h.2
    change Related _ (x.1.look x.2 _) (y.1.look y.2 _)
    rw [← eq]
    exact h.1.2 x.2

/-- Recursive handlers agree in control and billing on related arguments. -/
def Handlers : (r : Port) → Handler r → Handler r → Prop
  | none, _, _ => True
  | some (s,t), f, g => ∀ x y,Related s x y → Bills t (f x) (g y)

theorem depth_run {s t : Ty} (base base0 : s.T → Bill t.T)
    (step step0 : (s.T → Bill t.T) → s.T → Bill t.T)
    (hb : ∀ x y,Related s x y → Bills t (base x) (base0 y))
    (hs : ∀ f g,(∀ x y,Related s x y → Bills t (f x) (g y)) →
      ∀ x y,Related s x y → Bills t (step f x) (step0 g y)) (k : ℕ) :
    ∀ x y,Related s x y →
      Bills t (depthRun base step k x) (depthRun base0 step0 k y) := by
  induction k with
  | zero =>
    intro x y h
    exact bills_pay (hb x y h) 1 0
  | succ k ih =>
    intro x y h
    exact bills_pay (hs _ _ ih x y h) 1 (k+1)

end
end ExactFourierCircuits.DFTModelDataIndependence
