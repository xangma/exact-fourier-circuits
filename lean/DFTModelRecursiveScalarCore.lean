import DFTModelAffinePacket
import UniformNativeScalarRecordMachine

set_option autoImplicit false

/-! Concrete scalar-macro primitives for the actual recursive saving body.
The finite coefficient is decoded using upstream prepared arithmetic. One
upstream execution carries the exact actual and zero-source result together. -/
namespace ExactFourierCircuits.DFTModelRecursiveScalarCore
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
noncomputable section

def two {s : Ty} : Prog false s sc :=
  .comp (.fork (.atom .cone) (.atom .cone)) (.atom (.add .scalar))
def half {s : Ty} : Prog false s sc := .comp two (.atom .inv)
def negative {s : Ty} (x : Prog false s sc) : Prog false s sc :=
  .comp (.fork (.atom (.cz .scalar)) x) (.atom (.sub .scalar))

def coefficient {s : Ty} (c : Fin 5) : Prog false s sc :=
  if c.val=0 then negative (.atom .cone) else
  if c.val=1 then negative half else
  if c.val=2 then .atom (.cz .scalar) else
  if c.val=3 then half else .atom .cone

def coefficientWork (c : Fin 5) : ℕ :=
  if c.val=0 then 5 else if c.val=1 then 11 else
  if c.val=2 then 1 else if c.val=3 then 7 else 1

theorem coefficient_run {s : Ty} (c : Fin 5) (x : s.T) :
    run (coefficient c) x =
      ⟨UniformFixedCoefficientCodec.decode c,coefficientWork c,0,True⟩ := by
  fin_cases c <;>
    norm_num [coefficient,coefficientWork,two,half,negative,
      UniformFixedCoefficientCodec.decode,run,Code.run,Atom.run,
      Bill.pass,Bill.pay,Bill.one]

theorem coefficient_work_bound (c : Fin 5) : coefficientWork c≤11 := by
  fin_cases c <;> norm_num [coefficientWork]

/-- Multiplication by an explicitly prepared scalar, retaining the actual tag. -/
def scaleTagged : Prog false (p sc Tagged) Tagged :=
  .fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .snd))) scale)

def scaled (c : ℂ) (z : Tagged.T) : Tagged.T := (z.1,(c*z.2.1,c*z.2.2))
def added (z y : Tagged.T) : Tagged.T :=
  (if z.1=0 then y.1 else 1,(z.2.1+y.2.1,z.2.2+y.2.2))
def updated (c : ℂ) (z y : Tagged.T) : Tagged.T := added z (scaled c y)

theorem scaleTagged_run (c : ℂ) (z : Tagged.T) :
    run scaleTagged (c,z) = ⟨scaled c z,25,0,True⟩ := by
  simp [scaleTagged,scaled,scale,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem addTagged_run (z y : Tagged.T) :
    run taggedAdd (z,y) =
      ⟨added z y,if z.1=0 then 35 else 33,if z.1=0 then 0 else 1,True⟩ := by
  by_cases h:z.1=0 <;>
    simp [taggedAdd,tagUnion,tagLeft,tagRight,affineLeft,affineRight,
      add,leftOffset,rightOffset,leftHomogeneous,rightHomogeneous,added,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h]

abbrev OperationInput := p sc (p Tagged Tagged)
def operation : Prog false OperationInput Tagged :=
  .comp (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .snd))) scaleTagged)) taggedAdd

theorem comp_run {s t u : Ty} (f : Prog false s t) (g : Prog false t u) (x : s.T) :
    run (.comp f g) x = ((run f x).pass (run g)).pay 1 0 := rfl

theorem fork_run {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    run (.fork f g) x = (run f x).pass (fun y => (run g x).pass (fun z => Bill.one (y,z))) := rfl

theorem atom_run {s t : Ty} (f : Atom false s t) (x : s.T) :
    run (.atom f) x = f.run x := rfl

theorem ifz_run {s t : Ty} (q : Prog false s w) (f g : Prog false s t) (x : s.T) :
    run (.ifz q f g) x = ((run q x).pass (fun a =>
      if a=0 then run f x else run g x)).pay 1 0 := rfl

theorem operation_run (c : ℂ) (z y : Tagged.T) :
    run operation (c,(z,y)) =
      ⟨updated c z y,if z.1=0 then 71 else 69,if z.1=0 then 0 else 1,True⟩ := by
  simp only [operation,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [scaleTagged_run]
  rw [addTagged_run]
  by_cases h:z.1=0 <;> simp [updated,h]

/-- Exact zero-source offsets, not merely a weak numerical representation. -/
theorem updated_paired (c : ℂ) (a b a0 b0 : Scalar) :
    updated c (encodePaired a a0) (encodePaired b b0) =
      encodePaired (UniformFixedNetworkShearChildMachine.value c a b)
        (UniformFixedNetworkShearChildMachine.value c a0 b0) := by
  cases a with
  | mk av ad =>
    cases b with
    | mk bv bd =>
      cases ad <;> cases bd <;>
        simp [updated,added,scaled,encodePaired,tagged,flag,
          UniformFixedNetworkShearChildMachine.value,UniformInPlaceMachine.result,
          UniformInPlaceMachine.prepared]
      all_goals ring

theorem operation_paired (c : ℂ) (a b a0 b0 : Scalar) :
    (run operation (c,(encodePaired a a0,encodePaired b b0))).val =
      encodePaired (UniformFixedNetworkShearChildMachine.value c a b)
        (UniformFixedNetworkShearChildMachine.value c a0 b0) := by
  rw [operation_run]
  exact updated_paired c a b a0 b0

end
end ExactFourierCircuits.DFTModelRecursiveScalarCore
