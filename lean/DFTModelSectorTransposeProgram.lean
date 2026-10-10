import DFTModelSectorTransposeBounds

set_option autoImplicit false

/-! Runtime-q entry. The width is computed by actual integer loop syntax,
then all roles form one child argument. No child handler is used here. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section
abbrev RawInput (t : Ty) := p (p w sc) (p (p w (p w w)) (Ty.a t))
abbrev Context (t : Ty) := p (RawInput t) w
abbrev Node (t : Ty) := p (p w sc) (Ty.a t)
def prepare (t : Ty) : Prog false (RawInput t) (Context t) :=
 .fork (.atom .id) (.comp (.comp (.atom .fst) (.atom .fst)) power)
def rawGeometry (t : Ty) : Prog false (Context t) (p w (p w w)) :=
 .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def coreArgs (t : Ty) : Prog false (Context t) (Input t) :=
 .fork
  (.fork (.comp (rawGeometry t) (.atom .fst))
   (.fork (.comp (rawGeometry t) (.comp (.atom .snd) (.atom .fst)))
    (.fork (.comp (rawGeometry t) (.comp (.atom .snd) (.atom .snd))) (.atom .snd))))
  (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
def childArgs (t : Ty) : Prog false (Context t) (Node t) :=
 .fork (.comp (.atom .fst) (.atom .fst)) (.comp (coreArgs t) (gather t))
def argument (t : Ty) : Prog false (RawInput t) (p (Context t) (Node t)) :=
 .comp (prepare t) (.fork (.atom .id) (childArgs t))

theorem prepare_value (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (prepare t) ((q,I),((W,(V,a)),v))).val =
 (((q,I),((W,(V,a)),v)),2^q) := by
 change (_, (run power q).val) = _
 rw [power_value]
 rfl

theorem prepare_work (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (prepare t) ((q,I),((W,(V,a)),v))).work = 8*q+10 := by
 change 1+(3+(run power q).work+1)+1 = _
 rw [power_work]; omega

theorem prepare_valid (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (prepare t) ((q,I),((W,(V,a)),v))).valid := by
 change True ∧ ((True ∧ True) ∧ (run power q).valid) ∧ True
 exact ⟨trivial,⟨⟨trivial,trivial⟩,power_valid q⟩,trivial⟩

theorem prepare_peak (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (prepare t) ((q,I),((W,(V,a)),v))).peak ≤ 2^q := by
 simpa only [prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
  using power_peak q

theorem coreArgs_run (t : Ty) (q W V a T : ℕ) (I : ℂ) (v : Tape t.T) :
 run (coreArgs t) (((q,I),((W,(V,a)),v)),T) =
 ⟨((W,(V,(a,T))),v),35,0,True⟩ := by
 simp [coreArgs,rawGeometry,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] gather coreArgs prepare

theorem childArgs_run (t : Ty) (q W V a T : ℕ) (I : ℂ) (v : Tape t.T) :
 run (childArgs t) (((q,I),((W,(V,a)),v)),T) =
 ⟨((q,I),(run (gather t) ((W,(V,(a,T))),v)).val),
  40+(run (gather t) ((W,(V,(a,T))),v)).work,
  (run (gather t) ((W,(V,(a,T))),v)).peak,
  (run (gather t) ((W,(V,(a,T))),v)).valid⟩ := by
 simp only [childArgs,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [show Code.run (coreArgs t) () (((q,I),((W,(V,a)),v)),T)=_
  from coreArgs_run t q W V a T I v]
 simp only [zero_max,max_zero,true_and,and_true]
 congr 1; omega

theorem argument_value (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (argument t) ((q,I),((W,(V,a)),v))).val =
 ((((q,I),((W,(V,a)),v)),2^q),((q,I),gathered W V a (2^q) v t.blank)) := by
 change ((run (prepare t) ((q,I),((W,(V,a)),v))).val,
  (run (childArgs t) (run (prepare t) ((q,I),((W,(V,a)),v))).val).val) = _
 rw [prepare_value,childArgs_run,gather_value]

theorem argument_work (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (argument t) ((q,I),((W,(V,a)),v))).work = 61*(W*2^q)+8*q+69 := by
 change (run (prepare t) ((q,I),((W,(V,a)),v))).work+
  (1+(run (childArgs t) (run (prepare t) ((q,I),((W,(V,a)),v))).val).work+1)+1 = _
 rw [prepare_work,prepare_value,childArgs_run]
 dsimp only [Bill.work]
 rw [gather_work]
 omega

theorem argument_valid (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (argument t) ((q,I),((W,(V,a)),v))).valid := by
 change (run (prepare t) ((q,I),((W,(V,a)),v))).valid ∧
  True ∧ (run (childArgs t) (run (prepare t) ((q,I),((W,(V,a)),v))).val).valid ∧ True
 rw [prepare_value,childArgs_run]
 exact ⟨prepare_valid _ _ _ _ _ _ _,trivial,gather_valid _ _ _ _ _ _,trivial⟩

theorem argument_length (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T) :
 (run (argument t) ((q,I),((W,(V,a)),v))).val.2.2.len=W*2^q := by
 rw [argument_value]; rfl

theorem argument_linear_work (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T)
 (roles : 1≤W) :
 (run (argument t) ((q,I),((W,(V,a)),v))).work ≤ 69*(W*2^q+1) := by
 rw [argument_work]
 have qfit : q≤2^q := Nat.le_of_lt (q.lt_two_pow_self)
 have ext : 2^q≤W*2^q := by nlinarith
 omega

theorem argument_peak (t : Ty) (q W V a : ℕ) (I : ℂ) (v : Tape t.T)
 (roles : 1≤W) (fit : a+2^q≤V) :
 (run (argument t) ((q,I),((W,(V,a)),v))).peak ≤ W*V := by
 have positive : 0<2^q := Nat.two_pow_pos q
 have extent : 2^q≤W*V := by nlinarith
 have first := prepare_peak t q W V a I v
 change max (max (run (prepare t) ((q,I),((W,(V,a)),v))).peak
  (max 0 (max (run (childArgs t)
   (run (prepare t) ((q,I),((W,(V,a)),v))).val).peak 0))) 0 ≤ _
 rw [prepare_value,childArgs_run]
 have latter := gather_peak t W V a (2^q) v positive fit
 dsimp only [Bill.peak]
 simp only [zero_max,max_zero]

 exact max_le (first.trans extent) latter

end
end ExactFourierCircuits.DFTModelSectorTranspose
