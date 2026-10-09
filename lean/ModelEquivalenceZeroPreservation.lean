import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

/-! A semantic obstruction to unrestricted, data-preserving model equivalence.
Every typed upstream program preserves zero data. Prepared scalars and words
are unrestricted; this theorem does not assume that a run is valid. -/
namespace ExactFourierCircuits.ModelEquivalenceZeroPreservation
open OAI.PowerSaving OAI.PowerSaving.RAM

/-- All non-scalar data leaves are zero; words and prepared scalars are free. -/
def ZeroData : (t : Ty) → t.T → Prop
  | .w, _ => True
  | .c .scalar, _ => True
  | .c .left, x => x = 0
  | .c .right, x => x = 0
  | .c .both, x => x = 0
  | .p s t, x => ZeroData s x.1 ∧ ZeroData t x.2
  | .a t, x => ∀ i, ZeroData t (x.pos i)

def HandlerPreserves : (r : Port) → Handler r → Prop
  | none, _ => True
  | some (s,t), h => ∀ x, ZeroData s x → ZeroData t (h x).val

theorem blank_zero (t : Ty) : ZeroData t t.blank := by
  induction t with
  | w => trivial
  | c paint => cases paint <;> simp [ZeroData,Ty.blank]
  | p s t hs ht => exact ⟨hs,ht⟩
  | a t ht => intro i; exact Fin.elim0 i

theorem tape_set {α : Type} (P : α → Prop) (v : Tape α) (i : ℕ) (x : α)
    (hv : ∀ j, P (v.pos j)) (hx : P x) : ∀ j, P ((v.set i x).pos j) := by
  intro j
  change P (if j.val = i then x else v.pos j)
  split
  · exact hx
  · exact hv j

theorem tape_look {α : Type} (P : α → Prop) (v : Tape α) (i : ℕ) (z : α)
    (hv : ∀ j, P (v.pos j)) (hz : P z) : P (v.look i z) := by
  unfold Tape.look
  split
  · exact hv _
  · exact hz

theorem bill_steps {α : Type} (P : α → Prop) (init : α)
    (f : ℕ → α → Bill α) (hinit : P init)
    (hf : ∀ i x, P x → P (f i x).val) (n : ℕ) :
    P (Bill.steps init f n).val := by
  induction n with
  | zero => exact hinit
  | succ n hn => exact hf n _ hn

theorem bill_sow {α : Type} (P : α → Prop) (len count : ℕ) (z : α)
    (f : ℕ → Bill (ℕ × α)) (hz : P z) (hf : ∀ i, P (f i).val.2) :
    ∀ j, P ((Bill.sow len count z f).val.pos j) := by
  apply bill_steps (fun v : Tape α => ∀ j, P (v.pos j))
    (Tape.tab len (fun _ => z)) _ (fun _ => hz)
  intro i v hv
  exact tape_set P v (f i).val.1 (f i).val.2 hv (hf i)

theorem bill_tab {α : Type} (P : α → Prop) (len : ℕ) (z : α)
    (f : ℕ → Bill α) (hz : P z) (hf : ∀ i, P (f i).val) :
    ∀ j, P ((Bill.tab len z f).val.pos j) := by
  exact bill_sow P len len z _ hz hf

theorem atom_zero {allow : Bool} {s t : Ty} (op : Atom allow s t)
    (x : s.T) (hx : ZeroData s x) : ZeroData t (op.run x).val := by
  cases op with
  | lit n => trivial
  | int f => trivial
  | cz paint => cases paint <;> simp [ZeroData,Atom.run,Bill.one]
  | cone => trivial
  | add paint => cases paint <;> simp_all [ZeroData,Atom.run,Bill.one]
  | sub paint => cases paint <;> simp_all [ZeroData,Atom.run,Bill.one]
  | scale paint => cases paint <;> simp_all [ZeroData,Atom.run,Bill.one]
  | inv => trivial
  | cross h =>
      change x.1 * x.2 = 0
      rw [show x.1 = 0 from hx.1,zero_mul]
  | id => exact hx
  | fst => exact hx.1
  | snd => exact hx.2
  | len => trivial
  | look => exact tape_look _ x.1 x.2 _ hx.1 (blank_zero _)

theorem depth_zero {s t : Ty} (base : s.T → Bill t.T)
    (step : (s.T → Bill t.T) → s.T → Bill t.T)
    (hb : ∀ x, ZeroData s x → ZeroData t (base x).val)
    (hs : ∀ h, (∀ x, ZeroData s x → ZeroData t (h x).val) →
      ∀ x, ZeroData s x → ZeroData t (step h x).val)
    (n : ℕ) (x : s.T) (hx : ZeroData s x) :
    ZeroData t (depthRun base step n x).val := by
  induction n generalizing x with
  | zero => exact hb x hx
  | succ n hn => exact hs _ (fun x hx => hn x hx) x hx

/-- Every constructor, including arrays, loops and bounded recursive calls,
preserves zero data. The result holds in both upstream product modes. -/
theorem code_zero {allow : Bool} {r : Port} {s t : Ty} (code : Code allow r s t) :
    ∀ h : Handler r, HandlerPreserves r h →
    ∀ x : s.T, ZeroData s x → ZeroData t (code.run h x).val := by
  induction code with
  | atom op => intro h hh x hx; exact atom_zero op x hx
  | comp f g hf hg =>
      intro h hh x hx
      exact hg h hh _ (hf h hh x hx)
  | fork f g hf hg =>
      intro h hh x hx
      exact ⟨hf h hh x hx,hg h hh x hx⟩
  | ifz q f g hq hf hg =>
      intro h hh x hx
      simp only [Code.run,Bill.pay,Bill.pass]
      split
      · exact hf h hh x hx
      · exact hg h hh x hx
  | loop n init body hn hi hb =>
      intro h hh x hx
      exact bill_steps (ZeroData _) _ _ (hi h hh x hx)
        (fun i y hy => hb h hh (x,(i,y)) ⟨hx,True.intro,hy⟩) _
  | tab n body hn hb =>
      intro h hh x hx
      exact bill_tab (ZeroData _) _ _ _ (blank_zero _)
        (fun i => hb h hh (x,i) ⟨hx,True.intro⟩)
  | sow n count body hn hc hb =>
      intro h hh x hx
      exact bill_sow (ZeroData _) _ _ _ _ (blank_zero _)
        (fun i => (hb h hh (x,i) ⟨hx,True.intro⟩).2)
  | importClosed f hf =>
      intro h hh x hx
      exact hf () True.intro x hx
  | call => intro h hh x hx; exact hh x hx
  | descend base body hb hs =>
      intro h hh x hx
      exact depth_zero _ _ (hb () True.intro)
        (fun h hh => hs h hh) x.1 x.2 hx.2

/-- Closed programs require no external handler-preservation premise. -/
theorem prog_zero {allow : Bool} {s t : Ty} (code : Prog allow s t)
    (x : s.T) (hx : ZeroData s x) : ZeroData t (run code x).val :=
  code_zero code () True.intro x hx

/-- In particular, a left-data output is zero for every zero-data input. -/
theorem left_output_zero {s : Ty} (code : Prog false s (.c .left))
    (x : s.T) (hx : ZeroData s x) : (run code x).val = 0 :=
  prog_zero code x hx

end ExactFourierCircuits.ModelEquivalenceZeroPreservation
