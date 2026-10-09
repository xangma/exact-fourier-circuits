import DFTModelDataIndependenceAtoms

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelDataIndependence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Every actual false-mode code preserves control, validity and resource bills. -/
theorem code_run {r : Port} {s t : Ty} (f : Code false r s t) :
    ∀ h h0,Handlers r h h0 → ∀ x y,Related s x y →
      Bills t (f.run h x) (f.run h0 y) := by
  induction f with
  | atom op =>
    intro h h0 hh x y hxy
    exact atom_run op hxy
  | comp f g ihf ihg =>
    intro h h0 hh x y hxy
    apply bills_pay
    exact bills_pass (ihf h h0 hh x y hxy) (fun a b hab => ihg h h0 hh a b hab)
  | fork f g ihf ihg =>
    intro h h0 hh x y hxy
    apply bills_pass (ihf h h0 hh x y hxy)
    intro a b hab
    apply bills_pass (ihg h h0 hh x y hxy)
    intro c d hcd
    exact bills_one ⟨hab,hcd⟩
  | ifz q f g ihq ihf ihg =>
    intro h h0 hh x y hxy
    apply bills_pay
    apply bills_pass (ihq h h0 hh x y hxy)
    intro a b hab
    have eq : a=b := hab
    subst b
    split
    · exact ihf h h0 hh x y hxy
    · exact ihg h h0 hh x y hxy
  | loop n init body ihn ihi ihb =>
    intro h h0 hh x y hxy
    apply bills_pay
    apply bills_pass (ihn h h0 hh x y hxy)
    intro l l0 hl
    have eq : l=l0 := hl
    subst l0
    apply bills_pass (ihi h h0 hh x y hxy)
    intro a b hab
    apply bills_steps hab
    intro i z z0 hz
    exact ihb h h0 hh (x,(i,z)) (y,(i,z0)) ⟨hxy,rfl,hz⟩
  | tab n body ihn ihb =>
    intro h h0 hh x y hxy
    apply bills_pay
    apply bills_pass (ihn h h0 hh x y hxy)
    intro l l0 hl
    have eq : l=l0 := hl
    subst l0
    apply bills_tab l (related_refl _ _)
    intro i
    exact ihb h h0 hh (x,i) (y,i) ⟨hxy,rfl⟩
  | sow n count body ihn ihc ihb =>
    intro h h0 hh x y hxy
    apply bills_pay
    apply bills_pass (ihn h h0 hh x y hxy)
    intro l l0 hl
    have eq : l=l0 := hl
    subst l0
    apply bills_pass (ihc h h0 hh x y hxy)
    intro k k0 hk
    have eq : k=k0 := hk
    subst k0
    apply bills_sow l k (related_refl _ _)
    intro i
    exact ihb h h0 hh (x,i) (y,i) ⟨hxy,rfl⟩
  | importClosed f ihf =>
    intro h h0 hh x y hxy
    exact bills_pay (ihf () () trivial x y hxy) 1 0
  | call =>
    intro h h0 hh x y hxy
    exact bills_pay (hh x y hxy) 1 0
  | descend base body ihbase ihbody =>
    intro h h0 hh x y hxy
    have eq : x.1=y.1 := hxy.1
    change Bills _ ((depthRun _ _ x.1 x.2).pay 1 x.1)
      ((depthRun _ _ y.1 y.2).pay 1 y.1)
    rw [← eq]
    apply bills_pay
    apply depth_run (base.run ()) (base.run ()) body.run body.run
    · exact ihbase () () trivial
    · intro f g hfg
      exact ihbody f g hfg
    · exact hxy.2

/-- Closed typed programs have no data-dependent resource charges. -/
theorem prog_run {s t : Ty} (f : Prog false s t) {x y : s.T}
    (h : Related s x y) : Bills t (run f x) (run f y) :=
  code_run f () () trivial x y h

end
end ExactFourierCircuits.DFTModelDataIndependence
