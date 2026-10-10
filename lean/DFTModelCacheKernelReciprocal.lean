import ModelEquivalenceInterpreter
import UniformReciprocalPreparation

set_option autoImplicit false

/-! Charged reciprocal-series preparation. Each coefficient uses the preceding
coefficients, then publishes a fresh dense tape. The linear cost of that update
is charged explicitly; no mutable-tape operation or coefficient oracle is used.
The source Newton producer supplies the input coefficient tape in composition. -/
namespace ExactFourierCircuits.DFTModelCacheKernelReciprocal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

attribute [local irreducible] ModelEquivalenceInterpreter.update

abbrev Input := p w (Ty.a sc)
abbrev Context := p Input sc
abbrev StepInput := p Context (p w (Ty.a sc))
abbrev SumInput := p StepInput (p w sc)

def binary {s : Ty} (op : Atom false (p sc sc) sc)
    (f g : Prog false s sc) : Prog false s sc := .comp (.fork f g) (.atom op)
def integer {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

def inputH : Prog false Input (Ty.a sc) := .atom .snd
def hZero : Prog false Input sc :=
  .comp (.fork inputH (.atom (.lit 0))) (.atom .look)
def prepare : Prog false Input Context :=
  .fork (.atom .id) (.comp hZero (.atom .inv))
def count : Prog false Context w := .comp (.atom .fst) (.atom .fst)
def initial : Prog false Context (Ty.a sc) := .tab count (.atom (.cz .scalar))
def degree : Prog false StepInput w := .comp (.atom .snd) (.atom .fst)
def inverse : Prog false StepInput sc := .comp (.atom .fst) (.atom .snd)
def old : Prog false StepInput (Ty.a sc) := .comp (.atom .snd) (.atom .snd)
def termIndex : Prog false SumInput w := .comp (.atom .snd) (.atom .fst)
def termDegree : Prog false SumInput w := .comp (.atom .fst) degree
def termH : Prog false SumInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) inputH))
def termG : Prog false SumInput (Ty.a sc) := .comp (.atom .fst) old
def hRead : Prog false SumInput sc :=
  .comp (.fork termH (integer .add termIndex (.atom (.lit 1)))) (.atom .look)
def gRead : Prog false SumInput sc :=
  .comp (.fork termG (integer .sub
    (integer .sub termDegree (.atom (.lit 1))) termIndex)) (.atom .look)
def term : Prog false SumInput sc := binary (.add .scalar)
  (.comp (.atom .snd) (.atom .snd)) (binary (.scale .scalar) hRead gRead)
def sum : Prog false StepInput sc := .loop degree (.atom (.cz .scalar)) term
def coefficient : Prog false StepInput sc := .ifz degree inverse
  (binary (.sub .scalar) (.atom (.cz .scalar)) (binary (.scale .scalar) inverse sum))
def step : Prog false StepInput (Ty.a sc) :=
  .comp (.fork (.fork old degree) coefficient) (ModelEquivalenceInterpreter.update sc)
def loop : Prog false Context (Ty.a sc) := .loop count initial step
def program : Prog false Input (Ty.a sc) := .comp prepare loop

theorem prepare_run (n : ℕ) (h : Tape ℂ) :
    run prepare (n,h)=⟨((n,h),(h.look 0 0)⁻¹),9,0,h.look 0 0≠0⟩ := by
  simp [prepare,hZero,inputH,run,Code.run,Atom.run,Bill.pass,Bill.pay,
    Bill.one,Bill.word,Ty.blank]

theorem term_run (n k j : ℕ) (h g : Tape ℂ) (a z : ℂ) :
    run term ((((n,h),a),(k,g)),(j,z))=
      ⟨z+h.look (j+1) 0*g.look (k-1-j) 0,49,
        max (j+1) (k-1),True⟩ := by
  simp [term,binary,hRead,gRead,integer,termH,termG,termDegree,termIndex,
    degree,inputH,old,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,
    Bill.one,Bill.word,Ty.blank]
  omega

attribute [local irreducible] term

theorem degree_run (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    run degree (((n,h),a),(k,g))=⟨k,3,0,True⟩ := by
  simp [degree,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

def partialSum (h g : Tape ℂ) (k j : ℕ) : ℂ :=
  ∑ i∈Finset.range j,h.look (i+1) 0*g.look (k-1-i) 0

theorem sumSteps_run (n k j : ℕ) (h g : Tape ℂ) (a : ℂ) :
    Bill.steps (0 : ℂ) (fun i z=>run term ((((n,h),a),(k,g)),(i,z))) j=
      ⟨partialSum h g k j,50*j+1,if j=0 then 0 else max j (k-1),True⟩ := by
  induction j with
  | zero => simp [Bill.steps,Bill.one,partialSum]
  | succ j ih =>
    rw [Bill.steps,ih]
    dsimp only [Bill.pass]
    rw [term_run]
    simp only [Bill.pay,partialSum,Finset.sum_range_succ]
    congr 1
    · by_cases hj:j=0 <;> simp [hj]
    · simp

theorem sum_run (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    run sum (((n,h),a),(k,g))=⟨partialSum h g k k,50*k+6,k,True⟩ := by
  change ((run degree (((n,h),a),(k,g))).pass (fun l=>(Bill.one (0:ℂ)).pass (fun z=>
    Bill.steps z (fun i v=>run term ((((n,h),a),(k,g)),(i,v))) l))).pay 1 0=_
  rw [degree_run]
  simp only [Bill.pass,Bill.one]
  rw [sumSteps_run]
  simp only [Bill.pay]
  congr 1 <;> first | omega | simp
  intro hk
  omega

attribute [local irreducible] sum

def nextValue (h g : Tape ℂ) (a : ℂ) (k : ℕ) : ℂ :=
  if k=0 then a else -a*partialSum h g k k

theorem coefficient_run (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    run coefficient (((n,h),a),(k,g))=
      ⟨nextValue h g a k,if k=0 then 7 else 50*k+20,k,True⟩ := by
  by_cases hk:k=0
  · subst k
    simp [coefficient,degree,inverse,nextValue,run,Code.run,Atom.run,
      Bill.pass,Bill.pay,Bill.one]
  · change ((run degree (((n,h),a),(k,g))).pass (fun z=>
      if z=0 then run inverse (((n,h),a),(k,g)) else
        run (binary (.sub .scalar) (.atom (.cz .scalar))
          (binary (.scale .scalar) inverse sum)) (((n,h),a),(k,g)))).pay 1 0=_
    simp only [degree,inverse,binary,run,Code.run,Atom.run,Bill.one,Bill.pass]
    rw [show sum.run () (((n,h),a),(k,g))=run sum (((n,h),a),(k,g)) from rfl,
      sum_run]
    simp [Bill.pay,hk,nextValue]
    ring

attribute [local irreducible] coefficient

theorem step_run (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    run step (((n,h),a),(k,g))=
      (run (ModelEquivalenceInterpreter.update sc) ((g,k),nextValue h g a k)).pay
        ((if k=0 then 7 else 50*k+20)+9) k := by
  change ((((run old (((n,h),a),(k,g))).pass (fun v=>
    (run degree (((n,h),a),(k,g))).pass (fun i=>Bill.one (v,i)))).pass (fun vi=>
      (run coefficient (((n,h),a),(k,g))).pass (fun z=>Bill.one (vi,z)))).pass
        (run (ModelEquivalenceInterpreter.update sc))).pay 1 0 = _
  rw [coefficient_run]
  simp only [old,degree,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  congr 1 <;> first | omega | simp

theorem step_value (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    (run step (((n,h),a),(k,g))).val=g.set k (nextValue h g a k) := by
  rw [step_run]
  exact ModelEquivalenceInterpreter.update_value sc g k _

theorem step_valid (n k : ℕ) (h g : Tape ℂ) (a : ℂ) :
    (run step (((n,h),a),(k,g))).valid := by
  rw [step_run]
  exact ModelEquivalenceInterpreter.update_valid sc g k _

theorem step_work (n k : ℕ) (h g : Tape ℂ) (a : ℂ)
    (len:g.len=n) (hk:k<n) :
    (run step (((n,h),a),(k,g))).work≤85*n+40 := by
  rw [step_run]
  have hb:=(ModelEquivalenceInterpreter.update_work_bounds sc g k (nextValue h g a k)).2
  dsimp only [Bill.pay]
  split_ifs <;> omega

theorem step_peak (n k : ℕ) (h g : Tape ℂ) (a : ℂ)
    (len:g.len=n) (hk:k<n) :
    (run step (((n,h),a),(k,g))).peak≤n := by
  rw [step_run]
  change max (run (ModelEquivalenceInterpreter.update sc) ((g,k),_)).peak k≤n
  rw [ModelEquivalenceInterpreter.update_peak]
  split_ifs <;> omega

theorem initial_value (n : ℕ) (h : Tape ℂ) (a : ℂ) :
    (run initial ((n,h),a)).val=Tape.tab n (fun _=>0) := by
  change (Bill.tab n sc.blank (fun _=>Bill.one (0:ℂ))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem initial_work (n : ℕ) (h : Tape ℂ) (a : ℂ) :
    (run initial ((n,h),a)).work=5*n+6 := by
  change 3+(Bill.tab n sc.blank (fun _=>Bill.one (0:ℂ))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  simp [Bill.one]
  omega

theorem initial_peak (n : ℕ) (h : Tape ℂ) (a : ℂ) :
    (run initial ((n,h),a)).peak=n := by
  change max (max 0 (Bill.tab n sc.blank (fun _=>Bill.one (0:ℂ))).peak) 0=_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp [Bill.one]

theorem initial_valid (n : ℕ) (h : Tape ℂ) (a : ℂ) :
    (run initial ((n,h),a)).valid := by
  change (True ∧ True) ∧ (Bill.tab n sc.blank (fun _=>Bill.one (0:ℂ))).valid
  exact ⟨⟨trivial,trivial⟩,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 (by simp [Bill.one])⟩

def steps (n : ℕ) (h : Tape ℂ) (a : ℂ) : ℕ → Bill (Tape ℂ) :=
  Bill.steps (Tape.tab n (fun _=>0)) (fun k g=>run step (((n,h),a),(k,g)))

theorem steps_bounds (n j : ℕ) (h : Tape ℂ) (a : ℂ) (hj:j≤n) :
    (steps n h a j).val.len=n ∧ (steps n h a j).valid ∧
    (steps n h a j).work≤1+j*(85*n+41) ∧ (steps n h a j).peak≤n := by
  induction j with
  | zero => simp [steps,Bill.steps,Bill.one,Tape.tab]
  | succ j ih =>
    obtain ⟨len,hv,hw,hp⟩:=ih (by omega)
    change ((steps n h a j).pass (fun g=>run step (((n,h),a),(j,g)))).pay 1 (j+1) |>
      (fun b=>b.val.len=n ∧ b.valid ∧ b.work≤1+(j+1)*(85*n+41) ∧ b.peak≤n)
    have sk:j<n:=by omega
    have sv:=step_value n j h (steps n h a j).val a
    have sw:=step_work n j h (steps n h a j).val a len sk
    have sp:=step_peak n j h (steps n h a j).val a len sk
    dsimp only [Bill.pass,Bill.pay]
    refine ⟨?_,⟨hv,step_valid _ _ _ _ _⟩,?_,?_⟩
    · rw [sv]
      exact len
    · nlinarith
    · omega

theorem loop_run (n : ℕ) (h : Tape ℂ) (a : ℂ) :
    run loop ((n,h),a)=(steps n h a n).pay (5*n+10) n := by
  change ((run count ((n,h),a)).pass (fun l=>(run initial ((n,h),a)).pass
    (fun g=>Bill.steps g (fun i v=>run step (((n,h),a),(i,v))) l))).pay 1 0=_
  have iv:=initial_value n h a
  have iw:=initial_work n h a
  have ip:=initial_peak n h a
  have ia:=initial_valid n h a
  simp only [count,run,Code.run,Atom.run,Bill.one,Bill.pass]
  rw [iv,iw,ip]
  simp only [Bill.pay,steps,run]
  congr 1
  · change 3+(5*n+6+(steps n h a n).work)+1=(steps n h a n).work+(5*n+10)
    omega
  · simp only [max_self,zero_max,max_zero]
    change max n (steps n h a n).peak=max (steps n h a n).peak n
    exact max_comm _ _
  · simp [ia]

theorem program_run (n : ℕ) (h : Tape ℂ) :
    run program (n,h)=
      ⟨(steps n h (h.look 0 0)⁻¹ n).val,
        (steps n h (h.look 0 0)⁻¹ n).work+5*n+20,
        max (steps n h (h.look 0 0)⁻¹ n).peak n,
        h.look 0 0≠0 ∧ (steps n h (h.look 0 0)⁻¹ n).valid⟩ := by
  change ((run prepare (n,h)).pass (run loop)).pay 1 0=_
  rw [prepare_run]
  dsimp only [Bill.pass]
  rw [loop_run]
  simp only [Bill.pay]
  congr 1 <;> omega

theorem program_work (n : ℕ) (h : Tape ℂ) :
    (run program (n,h)).work≤110*(n+1)^2 := by
  rw [program_run]
  have hb:=(steps_bounds n n h (h.look 0 0)⁻¹ le_rfl).2.2.1
  dsimp only [Bill.work]
  nlinarith

theorem program_peak (n : ℕ) (h : Tape ℂ) : (run program (n,h)).peak≤n := by
  rw [program_run]
  exact max_le (steps_bounds n n h (h.look 0 0)⁻¹ le_rfl).2.2.2 le_rfl

theorem program_valid (n : ℕ) (h : Tape ℂ) (h0:h.look 0 0≠0) :
    (run program (n,h)).valid := by
  rw [program_run]
  exact ⟨h0,(steps_bounds n n h (h.look 0 0)⁻¹ le_rfl).2.1⟩

end
end ExactFourierCircuits.DFTModelCacheKernelReciprocal
