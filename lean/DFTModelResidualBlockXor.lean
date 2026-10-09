import DFTModelResidualTable

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBlockXor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Input := p w (p w (p (Ty.a w) (p w w)))
abbrev Acc := DFTModelResidualXor.Acc
abbrev BodyInput := p Input (p w Acc)

def old : Prog false BodyInput Acc := .comp (.atom .snd) (.atom .snd)
def left : Prog false BodyInput w := .comp old (.comp (.atom .fst) (.atom .fst))
def right : Prog false BodyInput w := .comp old (.comp (.atom .fst) (.atom .snd))
def place : Prog false BodyInput w := .comp old (.comp (.atom .snd) (.atom .fst))
def accumulated : Prog false BodyInput w := .comp old (.comp (.atom .snd) (.atom .snd))
def radix : Prog false BodyInput w := .comp (.atom .fst)
  (.comp (.atom .snd) (.atom .fst))
def table : Prog false BodyInput (Ty.a w) := .comp (.atom .fst)
  (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def digit : Prog false BodyInput w := .comp (.fork table
  (binary .add (binary .mul (binary .mod left radix) radix) (binary .mod right radix)))
  (.atom .look)
def body : Prog false BodyInput Acc :=
  .fork (.fork (binary .div left radix) (binary .div right radix))
    (.fork (binary .mul place radix)
      (binary .add accumulated (binary .mul digit place)))
def initial : Prog false Input Acc :=
  .fork (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
    (.fork (.atom (.lit 1)) (.atom (.lit 0)))
def loop : Prog false Input Acc := .loop (.atom .fst) initial body
def program : Prog false Input w := .comp loop (.comp (.atom .snd) (.atom .snd))

def input (q m a b : ℕ) : Input.T := (m,(2^q,((run DFTModelResidualTable.program q).val,(a,b))))
def step (q : ℕ) (z : Acc.T) : Acc.T :=
  ((z.1.1/2^q,z.1.2/2^q),(z.2.1*2^q,z.2.2+(z.1.1%2^q^^^z.1.2%2^q)*z.2.1))
def evolve (q : ℕ) (z : Acc.T) : ℕ → Acc.T
  | 0 => z
  | i+1 => step q (evolve q z i)

theorem body_value (q m a b i : ℕ) (z : Acc.T) :
    (run body (input q m a b,(i,z))).val = step q z := by
  have ht := DFTModelResidualTable.table_look q (z.1.1%2^q) (z.1.2%2^q)
    (Nat.mod_lt _ (Nat.two_pow_pos q)) (Nat.mod_lt _ (Nat.two_pow_pos q))
  simpa only [body,left,right,place,accumulated,digit,old,table,radix,binary,
    input,step,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank] using
    congrArg (fun d : ℕ => ((z.1.1/2^q,z.1.2/2^q),(z.2.1*2^q,z.2.2+d*z.2.1))) ht

theorem body_work (x : Input.T) (i : ℕ) (z : Acc.T) : (run body (x,(i,z))).work = 119 := by
  simp [body,left,right,place,accumulated,digit,old,table,radix,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem body_valid (x : Input.T) (i : ℕ) (z : Acc.T) : (run body (x,(i,z))).valid := by
  simp [body,left,right,place,accumulated,digit,old,table,radix,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

def steps (x : Input.T) (z : Acc.T) (j : ℕ) : Bill Acc.T :=
  Bill.steps z (fun i a => run body (x,(i,a))) j

theorem steps_value (q m a b : ℕ) (z : Acc.T) (j : ℕ) :
    (steps (input q m a b) z j).val = evolve q z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run body (input q m a b,(j,(steps (input q m a b) z j).val))).val = _
    rw [body_value,ih]
    rfl

theorem steps_work (x : Input.T) (z : Acc.T) (j : ℕ) : (steps x z j).work = 120*j+1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (steps x z j).work+(run body (x,(j,(steps x z j).val))).work+1 = _
    rw [body_work,ih]
    omega

theorem steps_valid (x : Input.T) (z : Acc.T) (j : ℕ) : (steps x z j).valid := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨ih,body_valid x j _⟩

theorem evolve_halves (q : ℕ) (z : Acc.T) (j : ℕ) :
    (evolve q z j).1.1 = z.1.1/(2^q)^j ∧ (evolve q z j).1.2 = z.1.2/(2^q)^j := by
  induction j with
  | zero => simp [evolve]
  | succ j ih =>
    simp only [evolve,step,ih.1,ih.2]
    constructor <;> rw [Nat.div_div_eq_div_mul,Nat.pow_succ]

theorem step_invariant (q : ℕ) (z : Acc.T) :
    (step q z).2.2+(step q z).2.1*((step q z).1.1^^^(step q z).1.2) =
      z.2.2+z.2.1*(z.1.1^^^z.1.2) := by
  simp only [step]
  rw [UniformBlockXorMachine.xor_split q z.1.1 z.1.2]
  ring

theorem evolve_invariant (q : ℕ) (z : Acc.T) (j : ℕ) :
    (evolve q z j).2.2+(evolve q z j).2.1*((evolve q z j).1.1^^^(evolve q z j).1.2) =
      z.2.2+z.2.1*(z.1.1^^^z.1.2) := by
  induction j with
  | zero => rfl
  | succ j ih => exact (step_invariant q (evolve q z j)).trans ih

theorem program_value (q m a b : ℕ) (ha : a<2^(q*m)) (hb : b<2^(q*m)) :
    (run program (input q m a b)).val = a^^^b := by
  change (steps (input q m a b) ((a,b),(1,0)) m).val.2.2 = _
  rw [steps_value]
  have halves := evolve_halves q ((a,b),(1,0)) m
  have inv := evolve_invariant q ((a,b),(1,0)) m
  have ha' : a<(2^q)^m := by simpa only [←Nat.pow_mul] using ha
  have hb' : b<(2^q)^m := by simpa only [←Nat.pow_mul] using hb
  simpa [halves.1,halves.2,Nat.div_eq_of_lt ha',Nat.div_eq_of_lt hb'] using inv

theorem program_work (x : Input.T) : (run program x).work = 120*x.1+16 := by
  change (1+(9+(steps x (x.2.2.2,(1,0)) x.1).work)+1)+3+1 = _
  rw [steps_work]
  omega

theorem program_valid (x : Input.T) : (run program x).valid := by
  simpa only [program,loop,initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,
    Bill.one,Bill.word,steps,and_true,true_and] using steps_valid x (x.2.2.2,(1,0)) x.1

end
end ExactFourierCircuits.DFTModelResidualBlockXor
