import ModelEquivalenceInterpreter
import UniformNewton

set_option autoImplicit false

/-! Charged prepared Newton products from a raw index and the supplied root.
The loop has three scalar registers; it never receives a product table. -/
namespace ExactFourierCircuits.DFTModelCacheForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier
noncomputable section

abbrev Input := p w sc
abbrev Product := p sc (p sc sc)
abbrev StepInput := p Input (p w Product)

def scalar {s : Ty} (op : Atom false (p sc sc) sc)
    (f g : Prog false s sc) : Prog false s sc := .comp (.fork f g) (.atom op)

def initial : Prog false Input Product :=
  .fork (.atom .cone) (.fork (.atom .cone) (.atom .cone))
def root : Prog false StepInput sc := .comp (.atom .fst) (.atom .snd)
def old : Prog false StepInput Product := .comp (.atom .snd) (.atom .snd)
def power : Prog false StepInput sc := .comp old (.atom .fst)
def H : Prog false StepInput sc := .comp old (.comp (.atom .snd) (.atom .fst))
def scale : Prog false StepInput sc := .comp old (.comp (.atom .snd) (.atom .snd))
def nextPower : Prog false StepInput sc := scalar (.scale .scalar) power root
def nextH : Prog false StepInput sc :=
  scalar (.scale .scalar) H (scalar (.sub .scalar) (.atom .cone) nextPower)
def nextScale : Prog false StepInput sc :=
  scalar (.scale .scalar) scale (scalar (.sub .scalar) (.atom (.cz .scalar)) power)
def step : Prog false StepInput Product := .fork nextPower (.fork nextH nextScale)

/-- One concrete loop, with all projections and arithmetic charged. -/
def product : Prog false Input Product := .loop (.atom .fst) initial step

theorem step_run (n i : ℕ) (omega p h s : ℂ) :
    run step ((n,omega),(i,(p,(h,s))))=
      ⟨(p*omega,(h*(1-p*omega),s*(-p))),57,0,True⟩ := by
  simp [step,nextPower,nextH,nextScale,scalar,root,old,power,H,scale,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem initial_run (n : ℕ) (omega : ℂ) :
    run initial (n,omega)=⟨(1,(1,1)),5,0,True⟩ := by
  simp [initial,run,Code.run,Atom.run,Bill.pass,Bill.one]

def productSteps (n : ℕ) (omega : ℂ) : ℕ → Bill Product.T :=
  Bill.steps (1,(1,1)) (fun i p => run step ((n,omega),(i,p)))

theorem productSteps_run (n j : ℕ) (omega : ℂ) :
    productSteps n omega j=
      ⟨(omega^j,(NewtonFourier.H omega j,NewtonFourier.scale omega j)),58*j+1,j,True⟩ := by
  induction j with
  | zero => simp [productSteps,Bill.steps,Bill.one]
  | succ j ih =>
    change ((productSteps n omega j).pass
      (fun p => run step ((n,omega),(j,p)))).pay 1 (j+1)=_
    rw [ih]
    dsimp only [Bill.pass]
    rw [step_run]
    simp [Bill.pay,pow_succ,H_succ,scale_succ]
    omega

theorem product_run (j : ℕ) (omega : ℂ) :
    run product (j,omega)=
      ⟨(omega^j,(NewtonFourier.H omega j,NewtonFourier.scale omega j)),58*j+8,j,True⟩ := by
  change ((Bill.one j).pass (fun l =>
    (run initial (j,omega)).pass (fun p =>
      Bill.steps p (fun i v => run step ((j,omega),(i,v))) l))).pay 1 0=_
  rw [initial_run]
  dsimp only [Bill.one,Bill.pass]
  have h := productSteps_run j j omega
  dsimp only [productSteps] at h
  rw [h]
  simp [Bill.pay]
  omega

end
end ExactFourierCircuits.DFTModelCacheForest
