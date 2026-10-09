import UniformMachine
import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

/-!
# Affine scalar primitives in the upstream typed RAM

A source scalar is represented by a prepared offset and a homogeneous left
datum. The types prohibit injecting a nonzero prepared scalar into the data
channel. These actual `Prog false` terms require no extra machine atom.
-/
namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Affine := p sc (c .left)
abbrev Tagged := p w Affine

def flag (b : Bool) : ℕ := if b then 1 else 0

def tagged (b : Bool) (offset homogeneous : ℂ) : Tagged.T :=
  (flag b,(offset,homogeneous))

/-- Prepared values have zero homogeneous component; data may have an offset. -/
def Represents (z : Tagged.T) (a : Scalar) : Prop :=
  z.1 = flag a.dependent ∧ a.value = z.2.1 + z.2.2 ∧
    (a.dependent = false → z.2.2 = 0)

def prepared : Prog false sc Affine := .fork (.atom .id) (.atom (.cz .left))
def input : Prog false (c .left) Affine := .fork (.atom (.cz .scalar)) (.atom .id)

def leftOffset : Prog false (p Affine Affine) sc :=
  .comp (.atom .fst) (.atom .fst)
def rightOffset : Prog false (p Affine Affine) sc :=
  .comp (.atom .snd) (.atom .fst)
def leftHomogeneous : Prog false (p Affine Affine) (c .left) :=
  .comp (.atom .fst) (.atom .snd)
def rightHomogeneous : Prog false (p Affine Affine) (c .left) :=
  .comp (.atom .snd) (.atom .snd)

def add : Prog false (p Affine Affine) Affine :=
  .fork (.comp (.fork leftOffset rightOffset) (.atom (.add .scalar)))
    (.comp (.fork leftHomogeneous rightHomogeneous) (.atom (.add .left)))

def sub : Prog false (p Affine Affine) Affine :=
  .fork (.comp (.fork leftOffset rightOffset) (.atom (.sub .scalar)))
    (.comp (.fork leftHomogeneous rightHomogeneous) (.atom (.sub .left)))

/-- Scaling both components uses only the statically prepared scalar input. -/
def scale : Prog false (p sc Affine) Affine :=
  .fork
    (.comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
      (.atom (.scale .scalar)))
    (.comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
      (.atom (.scale .left)))

/-- This is used only when both operands are prepared. `inv` checks nonzero. -/
def quotient : Prog false (p Affine Affine) Affine :=
  .fork (.comp (.fork (.comp rightOffset (.atom .inv)) leftOffset)
    (.atom (.scale .scalar))) (.atom (.cz .left))

theorem prepared_run (a : ℂ) : run prepared a = ⟨(a,0),3,0,True⟩ := by
  simp [prepared,run,Code.run,Atom.run,Bill.pass,Bill.one]

theorem input_run (a : ℂ) : run input a = ⟨(0,a),3,0,True⟩ := by
  simp [input,run,Code.run,Atom.run,Bill.pass,Bill.one]

theorem add_run (a b : Affine.T) :
    run add (a,b) = ⟨(a.1+b.1,a.2+b.2),19,0,True⟩ := by
  simp [add,leftOffset,rightOffset,leftHomogeneous,rightHomogeneous,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem sub_run (a b : Affine.T) :
    run sub (a,b) = ⟨(a.1-b.1,a.2-b.2),19,0,True⟩ := by
  simp [sub,leftOffset,rightOffset,leftHomogeneous,rightHomogeneous,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem scale_run (a : ℂ) (b : Affine.T) :
    run scale (a,b) = ⟨(a*b.1,a*b.2),15,0,True⟩ := by
  simp [scale,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem quotient_run (a b : Affine.T) :
    run quotient (a,b) = ⟨(a.1/b.1,0),13,0,b.1 ≠ 0⟩ := by
  simp [quotient,leftOffset,rightOffset,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one,div_eq_mul_inv,mul_comm]

theorem prepared_represents (a : ℂ) : Represents (0,(run prepared a).val) ⟨a,false⟩ := by
  simp [prepared_run,Represents,flag]

theorem input_represents (a : ℂ) : Represents (1,(run input a).val) ⟨a,true⟩ := by
  simp [input_run,Represents,flag]

end
end ExactFourierCircuits.DFTModelAffine
