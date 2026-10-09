import DFTModelAffineCore

set_option autoImplicit false

/-! Runtime taint dispatch for the affine primitive packet. All branches are
ordinary upstream typed `Code false`; invalid operations use `inv 0` to
produce an invalid Bill, without a complex-valued branch. -/
namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev BinaryInput := p Tagged Tagged
def tagLeft : Prog false BinaryInput w := .comp (.atom .fst) (.atom .fst)
def tagRight : Prog false BinaryInput w := .comp (.atom .snd) (.atom .fst)
def affineLeft : Prog false BinaryInput Affine := .comp (.atom .fst) (.atom .snd)
def affineRight : Prog false BinaryInput Affine := .comp (.atom .snd) (.atom .snd)
def offsetLeft : Prog false BinaryInput sc := .comp affineLeft (.atom .fst)
def offsetRight : Prog false BinaryInput sc := .comp affineRight (.atom .fst)

def tagUnion : Prog false BinaryInput w :=
  .ifz tagLeft tagRight (.atom (.lit 1))

def invalid (s : Ty) : Prog false s Tagged :=
  .fork (.atom (.lit 0))
    (.fork (.comp (.atom (.cz .scalar)) (.atom .inv)) (.atom (.cz .left)))

def taggedAdd : Prog false BinaryInput Tagged :=
  .fork tagUnion (.comp (.fork affineLeft affineRight) add)
def taggedSub : Prog false BinaryInput Tagged :=
  .fork tagUnion (.comp (.fork affineLeft affineRight) sub)
def multiplyLeft : Prog false BinaryInput Tagged :=
  .fork tagUnion (.comp (.fork offsetLeft affineRight) scale)
def multiplyRight : Prog false BinaryInput Tagged :=
  .fork tagUnion (.comp (.fork offsetRight affineLeft) scale)
def taggedMul : Prog false BinaryInput Tagged :=
  .ifz tagLeft multiplyLeft (.ifz tagRight multiplyRight (invalid BinaryInput))
def dividePrepared : Prog false BinaryInput Tagged :=
  .fork (.atom (.lit 0)) (.comp (.fork affineLeft affineRight) quotient)
def taggedDiv : Prog false BinaryInput Tagged :=
  .ifz tagLeft (.ifz tagRight dividePrepared (invalid BinaryInput)) (invalid BinaryInput)

def field : FieldOp → Prog false BinaryInput Tagged
  | .add => taggedAdd | .sub => taggedSub | .mul => taggedMul | .div => taggedDiv

theorem invalid_run (s : Ty) (x : s.T) :
    run (invalid s) x = ⟨tagged false 0 0,7,0,False⟩ := by
  simp [invalid,tagged,flag,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem tagUnion_run (da db : Bool) (oa ha ob hb : ℂ) :
    run tagUnion (tagged da oa ha,tagged db ob hb) =
      ⟨flag (da || db),if da then 5 else 7,if da then 1 else 0,True⟩ := by
  cases da <;> cases db <;>
    simp [tagUnion,tagLeft,tagRight,tagged,flag,run,Code.run,Atom.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedAdd_run (da db : Bool) (oa ha ob hb : ℂ) :
    run taggedAdd (tagged da oa ha,tagged db ob hb) =
      ⟨tagged (da || db) (oa+ob) (ha+hb),
        if da then 33 else 35,if da then 1 else 0,True⟩ := by
  cases da <;> cases db <;>
    simp [taggedAdd,tagUnion,tagLeft,tagRight,affineLeft,affineRight,add,
      leftOffset,rightOffset,leftHomogeneous,rightHomogeneous,tagged,flag,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedSub_run (da db : Bool) (oa ha ob hb : ℂ) :
    run taggedSub (tagged da oa ha,tagged db ob hb) =
      ⟨tagged (da || db) (oa-ob) (ha-hb),
        if da then 33 else 35,if da then 1 else 0,True⟩ := by
  cases da <;> cases db <;>
    simp [taggedSub,tagUnion,tagLeft,tagRight,affineLeft,affineRight,sub,
      leftOffset,rightOffset,leftHomogeneous,rightHomogeneous,tagged,flag,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedMul_left_run (db : Bool) (oa ha ob hb : ℂ) :
    run taggedMul (tagged false oa ha,tagged db ob hb) =
      ⟨tagged db (oa*ob) (oa*hb),37,0,True⟩ := by
  cases db <;>
    simp [taggedMul,multiplyLeft,tagUnion,tagLeft,tagRight,affineLeft,
      affineRight,offsetLeft,scale,tagged,flag,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem taggedMul_right_run (oa ha ob hb : ℂ) :
    run taggedMul (tagged true oa ha,tagged false ob hb) =
      ⟨tagged true (ob*oa) (ob*ha),39,1,True⟩ := by
  simp [taggedMul,multiplyRight,tagUnion,tagLeft,tagRight,affineLeft,
    affineRight,offsetRight,scale,tagged,flag,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedMul_invalid_run (oa ha ob hb : ℂ) :
    run taggedMul (tagged true oa ha,tagged true ob hb) =
      ⟨tagged false 0 0,15,0,False⟩ := by
  simp [taggedMul,invalid,tagLeft,tagRight,tagged,flag,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedDiv_run (oa ha ob hb : ℂ) :
    run taggedDiv (tagged false oa ha,tagged false ob hb) =
      ⟨tagged false (oa/ob) 0,31,0,ob ≠ 0⟩ := by
  simp [taggedDiv,dividePrepared,tagLeft,tagRight,affineLeft,affineRight,
    quotient,leftOffset,rightOffset,tagged,flag,div_eq_mul_inv,mul_comm,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedDiv_left_invalid_run (db : Bool) (oa ha ob hb : ℂ) :
    run taggedDiv (tagged true oa ha,tagged db ob hb) =
      ⟨tagged false 0 0,11,0,False⟩ := by
  simp [taggedDiv,invalid,tagLeft,tagged,flag,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem taggedDiv_right_invalid_run (oa ha ob hb : ℂ) :
    run taggedDiv (tagged false oa ha,tagged true ob hb) =
      ⟨tagged false 0 0,15,0,False⟩ := by
  simp [taggedDiv,invalid,tagLeft,tagRight,tagged,flag,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

/-- Uniform constant cost, including the natural taint tests. -/
theorem field_budget (op : FieldOp) (da db : Bool) (oa ha ob hb : ℂ) :
    (run (field op) (tagged da oa ha,tagged db ob hb)).work ≤ 39 ∧
    (run (field op) (tagged da oa ha,tagged db ob hb)).peak ≤ 1 := by
  cases op <;> cases da <;> cases db <;> simp only [field]
  all_goals first
    | rw [taggedAdd_run]
    | rw [taggedSub_run]
    | rw [taggedMul_left_run]
    | rw [taggedMul_right_run]
    | rw [taggedMul_invalid_run]
    | rw [taggedDiv_run]
    | rw [taggedDiv_left_invalid_run]
    | rw [taggedDiv_right_invalid_run]
  all_goals norm_num

end
end ExactFourierCircuits.DFTModelAffine
