import DFTModelResidualCore

set_option autoImplicit false

/-! Closed typed-RAM XOR arithmetic and its once-per-node lookup-table producer.
There is no bitwise atom: each bit executes integer div/mod/add/mul. -/
namespace ExactFourierCircuits.DFTModelResidualXor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Input := p w (p w w)
abbrev Acc := p (p w w) (p w w)
abbrev BodyInput := p Input (p w Acc)

def old : Prog false BodyInput Acc := .comp (.atom .snd) (.atom .snd)
def left : Prog false BodyInput w := .comp old (.comp (.atom .fst) (.atom .fst))
def right : Prog false BodyInput w := .comp old (.comp (.atom .fst) (.atom .snd))
def place : Prog false BodyInput w := .comp old (.comp (.atom .snd) (.atom .fst))
def accumulated : Prog false BodyInput w := .comp old (.comp (.atom .snd) (.atom .snd))
def digit : Prog false BodyInput w := binary .mod
  (binary .add (binary .mod left (.atom (.lit 2)))
    (binary .mod right (.atom (.lit 2)))) (.atom (.lit 2))
def body : Prog false BodyInput Acc :=
  .fork (.fork (binary .div left (.atom (.lit 2))) (binary .div right (.atom (.lit 2))))
    (.fork (binary .mul place (.atom (.lit 2)))
      (binary .add accumulated (binary .mul digit place)))
def initial : Prog false Input Acc := .fork (.atom .snd)
  (.fork (.atom (.lit 1)) (.atom (.lit 0)))
def loop : Prog false Input Acc := .loop (.atom .fst) initial body
def program : Prog false Input w := .comp loop (.comp (.atom .snd) (.atom .snd))

def step (z : Acc.T) : Acc.T :=
  ((z.1.1/2,z.1.2/2),(z.2.1*2,z.2.2+UniformXorTableMachine.parity z.1.1 z.1.2*z.2.1))
def evolve (z : Acc.T) : ℕ → Acc.T
  | 0 => z
  | i+1 => step (evolve z i)

theorem body_value (x : Input.T) (i : ℕ) (z : Acc.T) :
    (run body (x,(i,z))).val = step z := by
  simp [body,left,right,place,accumulated,digit,old,binary,step,UniformXorTableMachine.parity,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem body_work (x : Input.T) (i : ℕ) (z : Acc.T) :
    (run body (x,(i,z))).work = 85 := by
  simp [body,left,right,place,accumulated,digit,old,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem body_valid (x : Input.T) (i : ℕ) (z : Acc.T) : (run body (x,(i,z))).valid := by
  simp [body,left,right,place,accumulated,digit,old,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

def steps (x : Input.T) (z : Acc.T) (j : ℕ) : Bill Acc.T :=
  Bill.steps z (fun i a => run body (x,(i,a))) j

theorem steps_value (x : Input.T) (z : Acc.T) (j : ℕ) :
    (steps x z j).val = evolve z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run body (x,(j,(steps x z j).val))).val = _
    rw [body_value,ih]
    rfl

theorem steps_work (x : Input.T) (z : Acc.T) (j : ℕ) :
    (steps x z j).work = 86*j+1 := by
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

theorem evolve_halves (z : Acc.T) (j : ℕ) :
    (evolve z j).1.1 = z.1.1/2^j ∧ (evolve z j).1.2 = z.1.2/2^j := by
  induction j with
  | zero => simp [evolve]
  | succ j ih =>
    simp only [evolve,step,ih.1,ih.2]
    constructor <;> rw [Nat.div_div_eq_div_mul,Nat.pow_succ]

theorem step_invariant (z : Acc.T) :
    (step z).2.2+(step z).2.1*((step z).1.1^^^(step z).1.2) =
      z.2.2+z.2.1*(z.1.1^^^z.1.2) := by
  simp only [step]
  rw [UniformXorTableMachine.xor_decompose z.1.1 z.1.2]
  ring

theorem evolve_invariant (z : Acc.T) (j : ℕ) :
    (evolve z j).2.2+(evolve z j).2.1*((evolve z j).1.1^^^(evolve z j).1.2) =
      z.2.2+z.2.1*(z.1.1^^^z.1.2) := by
  induction j with
  | zero => rfl
  | succ j ih => exact (step_invariant (evolve z j)).trans ih

theorem loop_value (q a b : ℕ) :
    (run loop (q,(a,b))).val = evolve ((a,b),(1,0)) q := by
  change (steps (q,(a,b)) ((a,b),(1,0)) q).val = _
  exact steps_value _ _ _

theorem program_value (q a b : ℕ) (ha : a<2^q) (hb : b<2^q) :
    (run program (q,(a,b))).val = a^^^b := by
  change (run loop (q,(a,b))).val.2.2 = _
  rw [loop_value]
  have halves := evolve_halves ((a,b),(1,0)) q
  have inv := evolve_invariant ((a,b),(1,0)) q
  simpa [halves.1,halves.2,Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hb] using inv

theorem program_work (q a b : ℕ) : (run program (q,(a,b))).work = 86*q+12 := by
  change (1+(5+(steps (q,(a,b)) ((a,b),(1,0)) q).work)+1)+3+1 = _
  rw [steps_work]
  omega

theorem program_valid (q a b : ℕ) : (run program (q,(a,b))).valid := by
  simpa only [program,loop,initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,
    Bill.one,Bill.word,steps,and_true,true_and] using steps_valid (q,(a,b)) ((a,b),(1,0)) q

theorem evolve_place (z : Acc.T) (j : ℕ) : (evolve z j).2.1=z.2.1*2^j := by
  induction j with
  | zero => simp [evolve]
  | succ j ih => simp only [evolve,step,ih,Nat.pow_succ];ring

theorem body_peak (x : Input.T) (i : ℕ) (z : Acc.T) (R : ℕ)
    (ha : z.1.1≤R) (hb : z.1.2≤R) (hp : z.2.1*2≤R)
    (hc : (step z).2.2≤R) (two : 2≤R) :
    (run body (x,(i,z))).peak≤R := by
  rcases z with ⟨⟨a,b⟩,⟨p,c⟩⟩
  dsimp only [Ty.T] at *
  have am:=Nat.mod_lt a (by decide:0<2)
  have bm:=Nat.mod_lt b (by decide:0<2)
  have pm:=Nat.mod_lt (a%2+b%2) (by decide:0<2)
  have ad:=Nat.div_le_self a 2
  have bd:=Nat.div_le_self b 2
  change c+((a%2+b%2)%2)*p≤R at hc
  have product : ((a%2+b%2)%2)*p≤R := (Nat.le_add_left _ _).trans hc
  simp only [body,left,right,place,accumulated,digit,old,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,max_le_iff]
  repeat' apply And.intro
  all_goals omega

theorem steps_peak (q a b h : ℕ) (hh : h≤q) (ha : a<2^q) (hb : b<2^q) :
    (steps (q,(a,b)) ((a,b),(1,0)) h).peak≤2^q+2 := by
  induction h with
  | zero => change 0≤_;omega
  | succ h ih =>
    have prior:=ih (by omega)
    have hv:=steps_value (q,(a,b)) ((a,b),(1,0)) h
    have halves:=evolve_halves ((a,b),(1,0)) h
    have pl:=evolve_place ((a,b),(1,0)) h
    have inv:=evolve_invariant ((a,b),(1,0)) (h+1)
    have xor:=Nat.xor_lt_two_pow ha hb
    have next : (step (evolve ((a,b),(1,0)) h)).2.2≤2^q+2 := by
      change (evolve ((a,b),(1,0)) (h+1)).2.2≤_
      calc
        _ ≤ (evolve ((a,b),(1,0)) (h+1)).2.2+
            (evolve ((a,b),(1,0)) (h+1)).2.1*
              ((evolve ((a,b),(1,0)) (h+1)).1.1^^^(evolve ((a,b),(1,0)) (h+1)).1.2) :=
          Nat.le_add_right _ _
        _ = a^^^b := by simpa only [Nat.one_mul,Nat.zero_add] using inv
        _ ≤ 2^q+2 := by omega
    have bound:=body_peak (q,(a,b)) h (evolve ((a,b),(1,0)) h) (2^q+2)
      (by rw [halves.1];exact (Nat.div_le_self a _).trans ha.le |>.trans (by omega))
      (by rw [halves.2];exact (Nat.div_le_self b _).trans hb.le |>.trans (by omega))
      (by rw [pl];dsimp only;rw [Nat.one_mul,←Nat.pow_succ];
          exact (Nat.pow_le_pow_right (by decide) hh).trans (by omega)) next (by omega)
    change max (max (steps (q,(a,b)) ((a,b),(1,0)) h).peak
      (run body ((q,(a,b)),(h,(steps (q,(a,b)) ((a,b),(1,0)) h).val))).peak) (h+1)≤_
    rw [hv]
    have idx : h+1≤2^q+2 := by have hq:=q.lt_two_pow_self;omega
    omega

theorem program_peak (q a b : ℕ) (ha : a<2^q) (hb : b<2^q) :
    (run program (q,(a,b))).peak≤2^q+2 := by
  have h:=steps_peak q a b q le_rfl ha hb
  have loopBound : (run loop (q,(a,b))).peak≤2^q+2 := by
    change max (max 0 (max (max 0 (max 1 (max 0 0)))
      (steps (q,(a,b)) ((a,b),(1,0)) q).peak)) 0≤_
    omega
  simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero] using loopBound

end
end ExactFourierCircuits.DFTModelResidualXor
