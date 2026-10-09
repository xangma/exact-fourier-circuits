import DFTModelAffineCore
import DFTModelBinaryPair

set_option autoImplicit false

/-!
# Affine pair translation for mixed prepared and data banks

Unlike a direct injection of arbitrary complex values into a data paint, this
representation retains a prepared offset and a homogeneous left component.
The actual pair block acts on both components using only prepared scalings.
Its result represents the source scalar including its conservative tag.
-/
namespace ExactFourierCircuits.DFTModelBinaryAffinePair
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Pair := p DFTModelAffine.Tagged DFTModelAffine.Tagged
abbrev Input := p DFTModelBinaryPair.Coefficients Pair

def coefficient (second : Bool) : Prog false Input sc :=
  .comp (.atom .fst) (if second then .atom .snd else .atom .fst)

def datum (second : Bool) : Prog false Input DFTModelAffine.Tagged :=
  .comp (.atom .snd) (if second then .atom .snd else .atom .fst)

def tag (second : Bool) : Prog false Input w := .comp (datum second) (.atom .fst)
def affine (second : Bool) : Prog false Input DFTModelAffine.Affine :=
  .comp (datum second) (.atom .snd)

def tagSum : Prog false Input w :=
  .comp (.fork (tag false) (tag true)) (.atom (.int .add))
def combinedTag : Prog false Input w :=
  .ifz tagSum (.atom (.lit 0)) (.atom (.lit 1))

def term (secondCoefficient secondDatum : Bool) : Prog false Input DFTModelAffine.Affine :=
  .comp (.fork (coefficient secondCoefficient) (affine secondDatum)) DFTModelAffine.scale

def combination (swapped : Bool) : Prog false Input DFTModelAffine.Tagged :=
  .fork combinedTag
    (.comp (.fork (term swapped false) (term (!swapped) true)) DFTModelAffine.add)

def program : Prog false Input Pair := .fork (combination false) (combination true)

def flags (u v : DFTModelAffine.Tagged.T) : ℕ := if u.1+v.1 = 0 then 0 else 1

def combine (a b : ℂ) (u v : DFTModelAffine.Tagged.T) : DFTModelAffine.Tagged.T :=
  (flags u v,(a*u.2.1+b*v.2.1,a*u.2.2+b*v.2.2))

def result (a b : ℂ) (u v : DFTModelAffine.Tagged.T) : Pair.T :=
  (combine a b u v,combine b a u v)

theorem combination_run (swapped : Bool) (a b : ℂ) (u v : DFTModelAffine.Tagged.T) :
    run (combination swapped) ((a,b),(u,v)) =
      ⟨if swapped then combine b a u v else combine a b u v,87,u.1+v.1,True⟩ := by
  cases swapped <;> by_cases h : u.1=0 ∧ v.1=0 <;>
    simp [combination,combinedTag,tagSum,term,coefficient,affine,tag,datum,
      flags,combine,DFTModelAffine.scale,DFTModelAffine.add,
      DFTModelAffine.leftOffset,DFTModelAffine.rightOffset,
      DFTModelAffine.leftHomogeneous,DFTModelAffine.rightHomogeneous,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h]
  all_goals exact Nat.one_le_iff_ne_zero.mpr (fun hz => h (Nat.add_eq_zero_iff.mp hz))

theorem program_run (a b : ℂ) (u v : DFTModelAffine.Tagged.T) :
    run program ((a,b),(u,v)) = ⟨result a b u v,175,u.1+v.1,True⟩ := by
  change ((run (combination false) ((a,b),(u,v))).pass (fun y =>
    (run (combination true) ((a,b),(u,v))).pass (fun z => Bill.one (y,z)))) = _
  rw [combination_run,combination_run]
  simp [result,Bill.pass,Bill.one]

theorem combine_represents (a b : ℂ) (u v : DFTModelAffine.Tagged.T) (x y : Scalar)
    (hx : DFTModelAffine.Represents u x) (hy : DFTModelAffine.Represents v y) :
    DFTModelAffine.Represents (combine a b u v) (UniformPairMachine.combine a b x y) := by
  rcases hx with ⟨hx,hxv,hxz⟩
  rcases hy with ⟨hy,hyv,hyz⟩
  refine ⟨?_,?_,?_⟩
  · change flags u v = DFTModelAffine.flag (x.dependent || y.dependent)
    simp only [flags,hx,hy]
    cases x.dependent <;> cases y.dependent <;> simp [DFTModelAffine.flag]
  · change a*x.value+b*y.value = (a*u.2.1+b*v.2.1)+(a*u.2.2+b*v.2.2)
    rw [hxv,hyv]
    ring
  · intro h
    have hx0 : x.dependent=false := by
      change (x.dependent || y.dependent)=false at h
      cases hxd : x.dependent <;> cases hyd : y.dependent <;> simp_all
    have hy0 : y.dependent=false := by
      change (x.dependent || y.dependent)=false at h
      cases hxd : x.dependent <;> cases hyd : y.dependent <;> simp_all
    change a*u.2.2+b*v.2.2=0
    rw [hxz hx0,hyz hy0]
    simp

theorem represented_peak (u v : DFTModelAffine.Tagged.T) (x y : Scalar)
    (hx : DFTModelAffine.Represents u x) (hy : DFTModelAffine.Represents v y) :
    u.1+v.1 ≤ 2 := by
  rw [hx.1,hy.1]
  cases x.dependent <;> cases y.dependent <;> simp [DFTModelAffine.flag]

/-- Prepared offsets are never inserted into the homogeneous channel. -/
theorem actual_execution {n B : ℕ} (input : Fin n → ℂ) (s : State)
    (a b : ℂ) (x y : Scalar) (u v : DFTModelAffine.Tagged.T)
    (hx : DFTModelAffine.Represents u x) (hy : DFTModelAffine.Represents v y)
    (ready : UniformPairMachine.Ready a b x y s)
    (distinct : s.natReg 0 ≠ s.natReg 1) (code : 11 ≤ B) (wb : WordBound B s) :
    ∃ t, BoundedExecution UniformPairMachine.program n input B s 11 t ∧
      t.scalarHeap (s.natReg 0)=some (UniformPairMachine.combine a b x y) ∧
      t.scalarHeap (s.natReg 1)=some (UniformPairMachine.combine b a x y) ∧
      DFTModelAffine.Represents (run program ((a,b),(u,v))).val.1
        (UniformPairMachine.combine a b x y) ∧
      DFTModelAffine.Represents (run program ((a,b),(u,v))).val.2
        (UniformPairMachine.combine b a x y) ∧
      (run program ((a,b),(u,v))).valid ∧
      (run program ((a,b),(u,v))).work ≤ 16*11 ∧
      (run program ((a,b),(u,v))).peak ≤ B := by
  have execution := UniformPairMachine.bounded_execution n input B s a b x y ready code wb
  have values := UniformPairMachine.final_values s a b x y distinct
  refine ⟨UniformPairMachine.finalState s a b x y,execution,values.1,values.2,?_,?_,?_,?_,?_⟩
  · rw [program_run]
    exact combine_represents a b u v x y hx hy
  · rw [program_run]
    exact combine_represents b a u v x y hx hy
  · rw [program_run]
    trivial
  · rw [program_run]
    change 175 ≤ 16*11
    omega
  · rw [program_run]
    exact Nat.le_trans (represented_peak u v x y hx hy)
      (Nat.le_trans (by decide : 2 ≤ 11) code)

end
end ExactFourierCircuits.DFTModelBinaryAffinePair
