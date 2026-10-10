import DFTModelScalarPower

set_option autoImplicit false

/-! A charged prepared geometric dot product. Both phase and accumulator are
ordinary prepared scalars; the input tape is retained and read by index. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumSum
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Input := p w (p sc (Ty.a sc))
abbrev State := p sc sc
abbrev StepInput := p Input (p w State)

def scalar {s : Ty} (op : Atom false (p sc sc) sc)
    (f g : Prog false s sc) : Prog false s sc := .comp (.fork f g) (.atom op)
def initial : Prog false Input State := .fork (.atom .cone) (.atom (.cz .scalar))
def ratio : Prog false StepInput sc :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def phase : Prog false StepInput sc :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def total : Prog false StepInput sc :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def tape : Prog false StepInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def index : Prog false StepInput w := .comp (.atom .snd) (.atom .fst)
def cell : Prog false StepInput sc := .comp (.fork tape index) (.atom .look)
def step : Prog false StepInput State :=
  .fork (scalar (.scale .scalar) phase ratio)
    (scalar (.add .scalar) total (scalar (.scale .scalar) phase cell))
def program : Prog false Input sc :=
  .comp (.loop (.atom .fst) initial step) (.atom .snd)

def value (t : Tape ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑i∈Finset.range n,z^i*t.look i 0

theorem step_run (N i : ℕ) (z a b : ℂ) (t : Tape ℂ) :
    run step ((N,(z,t)),(i,(a,b)))=
      ⟨(a*z,b+a*t.look i 0),41,0,True⟩ := by
  simp [step,scalar,phase,ratio,total,cell,tape,index,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

attribute [local irreducible] step

theorem steps_run (N k : ℕ) (z : ℂ) (t : Tape ℂ) :
    Bill.steps (1,(0:ℂ)) (fun i s=>run step ((N,(z,t)),(i,s))) k=
      ⟨(z^k,value t z k),42*k+1,k,True⟩ := by
  induction k with
  | zero => simp [Bill.steps,Bill.one,value]
  | succ k ih =>
    rw [Bill.steps,ih]
    dsimp only [Bill.pass]
    rw [step_run]
    simp only [Bill.pay,value,Finset.sum_range_succ,pow_succ]
    congr 1 <;> first | omega | simp

theorem program_run (N : ℕ) (z : ℂ) (t : Tape ℂ) :
    run program (N,(z,t))=⟨value t z N,42*N+8,N,True⟩ := by
  have hi:run initial (N,(z,t))=⟨(1,(0:ℂ)),3,0,True⟩ := by
    simp [initial,run,Code.run,Atom.run,Bill.pass,Bill.one]
  change ((((Bill.one N).pass (fun n=>(run initial (N,(z,t))).pass
    (fun s=>Bill.steps s (fun i v=>run step ((N,(z,t)),(i,v))) n))).pay 1 0).pass
      (fun s=>Bill.one s.2)).pay 1 0 = _
  rw [hi]
  dsimp only [Bill.pass,Bill.one]
  rw [steps_run]
  simp only [Bill.pay]
  congr 1 <;> first | omega | simp

end
end ExactFourierCircuits.DFTModelCacheSpectrumSum
