import DFTModelConjugationCore

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelConjugation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem atom {allow : Bool} {s t : Ty} (op : Atom allow s t) (x : s.T) :
    op.run (value s x)=bill (value t) (op.run x) := by
  cases op <;> simp only [Atom.run,value,bill,Bill.one,Bill.word]
  case cz t => simp only [star_zero]
  case cone => simp only [star_one]
  case len => rfl
  case add t => simp only [star_add]
  case sub t => simp only [star_sub]
  case scale t => simp only [star_mul,mul_comm]
  case inv =>
    simp only [star_inv₀]
    congr 1
    exact propext (star_ne_zero)
  case cross h => simp only [star_mul,mul_comm]
  case look => simpa only [value_blank,Bill.one] using congrArg Bill.one (map_look (value t) x.1 x.2 t.blank)

def HandlerEquivariant : (r : Port) → Handler r → Prop
  | none, _ => True
  | some (s,t), h => ∀x,h (value s x)=bill (value t) (h x)

theorem depth {s t : Ty} (a : s.T → Bill t.T)
    (b : (s.T → Bill t.T) → s.T → Bill t.T)
    (ha : ∀x,a (value s x)=bill (value t) (a x))
    (hb : ∀h, (∀x,h (value s x)=bill (value t) (h x)) →
      ∀x,b h (value s x)=bill (value t) (b h x)) (n : ℕ) (x : s.T) :
    depthRun a b n (value s x)=bill (value t) (depthRun a b n x) := by
  induction n generalizing x with
  | zero => simp only [depthRun,ha,bill_pay]
  | succ n ih => simp only [depthRun,hb _ ih,bill_pay]

theorem code {allow : Bool} {r : Port} {s t : Ty} (p : Code allow r s t) :
    ∀(h : Handler r),HandlerEquivariant r h → ∀x,
      p.run h (value s x)=bill (value t) (p.run h x) := by
  induction p with
  | atom op => intro h hh x; exact atom op x
  | comp f g hf hg =>
    intro h hh x
    simp only [Code.run,hf h hh,bill_pay]
    exact congrArg (fun b=>Bill.pay b 1 0) (bill_pass _ _ _ _ _ (hg h hh))
  | fork f g hf hg =>
    intro h hh x
    simp only [Code.run,hf h hh]
    apply bill_pass
    intro y
    rw [hg h hh]
    apply bill_pass
    intro z
    rfl
  | ifz q f g hq hf hg =>
    intro h hh x
    simp only [Code.run,hq h hh,bill_pay]
    apply congrArg (fun b=>Bill.pay b 1 0)
    apply bill_pass
    intro y
    change (if y=0 then _ else _) = _
    split
    · exact hf h hh x
    · exact hg h hh x
  | loop n init body hn hi hb =>
    intro h hh x
    simp only [Code.run,hn h hh,bill_pay]
    apply congrArg (fun b=>Bill.pay b 1 0)
    apply bill_pass
    intro l
    rw [hi h hh]
    apply bill_pass
    intro y
    apply steps
    intro i z
    exact hb h hh (x,(i,z))
  | tab n body hn hb =>
    intro h hh x
    simp only [Code.run,hn h hh,bill_pay]
    apply congrArg (fun b=>Bill.pay b 1 0)
    apply bill_pass
    intro l
    conv_lhs => rw [←value_blank]
    apply tab
    intro i
    exact hb h hh (x,i)
  | sow n count body hn hc hb =>
    intro h hh x
    simp only [Code.run,hn h hh,bill_pay]
    apply congrArg (fun b=>Bill.pay b 1 0)
    apply bill_pass
    intro l
    rw [hc h hh]
    apply bill_pass
    intro k
    conv_lhs => rw [←value_blank]
    apply sow
    intro i
    exact hb h hh (x,i)
  | importClosed f hf =>
    intro h hh x
    simp only [Code.run,hf () trivial,bill_pay]
  | call =>
    intro h hh x
    simp only [Code.run,hh x,bill_pay]
  | descend base body hbase hbody =>
    intro h hh x
    simp only [Code.run,value,bill_pay]
    apply congrArg (fun b=>Bill.pay b 1 x.1)
    apply depth
    · exact hbase () trivial
    · intro f hf
      exact hbody f hf

theorem program_run {allow : Bool} {s t : Ty} (p : Prog allow s t) (x : s.T) :
    run p (value s x)=bill (value t) (run p x) := code p () trivial x

theorem program_value {allow : Bool} {s t : Ty} (p : Prog allow s t) (x : s.T) :
    (run p (value s x)).val=value t (run p x).val := congrArg Bill.val (program_run p x)

theorem program_work {allow : Bool} {s t : Ty} (p : Prog allow s t) (x : s.T) :
    (run p (value s x)).work=(run p x).work := by rw [program_run];rfl

theorem program_peak {allow : Bool} {s t : Ty} (p : Prog allow s t) (x : s.T) :
    (run p (value s x)).peak=(run p x).peak := by rw [program_run];rfl

theorem program_valid {allow : Bool} {s t : Ty} (p : Prog allow s t) (x : s.T) :
    (run p (value s x)).valid↔(run p x).valid := by rw [program_run];rfl

end
end ExactFourierCircuits.DFTModelConjugation
