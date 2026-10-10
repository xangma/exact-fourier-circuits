import DFTModelSectorTransposeProgram

set_option autoImplicit false

/-! Optional internal port composition. This has exactly one syntactic call,
receiving one complete paired child bank. It supplies no closed child compiler. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
abbrev ChildPort (t : Ty) := some (Node t,Ty.a t)
def oneCall (t : Ty) : Code false (ChildPort t) (RawInput t) (p (Context t) (Ty.a t)) :=
 .comp (.importClosed (argument t)) (.fork (.atom .fst) (.comp (.atom .snd) .call))

attribute [local irreducible] argument

theorem oneCall_value (t : Ty) (h : Handler (ChildPort t)) (q W V a : ℕ)
 (I : ℂ) (v : Tape t.T) :
 (Code.run (oneCall t) h ((q,I),((W,(V,a)),v))).val =
 ((((q,I),((W,(V,a)),v)),2^q),
  (h ((q,I),gathered W V a (2^q) v t.blank)).val) := by
 change ((run (argument t) ((q,I),((W,(V,a)),v))).val.1,
  (h (run (argument t) ((q,I),((W,(V,a)),v))).val.2).val) = _
 rw [argument_value]

theorem oneCall_work (t : Ty) (h : Handler (ChildPort t)) (q W V a : ℕ)
 (I : ℂ) (v : Tape t.T) :
 (Code.run (oneCall t) h ((q,I),((W,(V,a)),v))).work =
 61*(W*2^q)+8*q+76+(h ((q,I),gathered W V a (2^q) v t.blank)).work := by
 change (run (argument t) ((q,I),((W,(V,a)),v))).work+1+
  (1+(1+((h (run (argument t) ((q,I),((W,(V,a)),v))).val.2).work+1)+1)+1)+1 = _
 rw [argument_work,argument_value]
 dsimp only [Prod.snd]
 omega

theorem oneCall_valid (t : Ty) (h : Handler (ChildPort t)) (q W V a : ℕ)
 (I : ℂ) (v : Tape t.T) :
 (Code.run (oneCall t) h ((q,I),((W,(V,a)),v))).valid ↔
 (h ((q,I),gathered W V a (2^q) v t.blank)).valid := by
 simp only [oneCall,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,true_and,and_true]
 change (run (argument t) ((q,I),((W,(V,a)),v))).valid ∧
  (h (run (argument t) ((q,I),((W,(V,a)),v))).val.2).valid ↔ _
 rw [argument_value]
 exact and_iff_right (argument_valid t q W V a I v)

end
end ExactFourierCircuits.DFTModelSectorTranspose
