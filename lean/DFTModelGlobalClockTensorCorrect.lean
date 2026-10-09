import DFTModelGlobalClockTensor

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelGlobalClockTensor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTensorMonomialMachine
noncomputable section

attribute [local irreducible] expand base body program

def axisData (a : Axis) : AxisRecord.T := (a.radix,⟨a.radix,a.coefficient⟩)
def axisTape (axes : List Axis) : Tape AxisRecord.T :=
  ⟨axes.length,fun i => axisData (axes.get i)⟩
def coefficientTape (axes : List Axis) : Tape ℂ :=
  ⟨(radices axes).prod,tensorCoefficient axes⟩
def Stored (axes : List Axis) (i : ℕ) (t : Tape AxisRecord.T) : Prop :=
  ∀k : Fin axes.length,t.look (i+k.val) AxisRecord.blank=axisData (axes.get k)

theorem axisTape_stored (axes : List Axis) : Stored axes 0 (axisTape axes) := by
  intro k
  simp [axisTape,Tape.look,k.isLt]

theorem stored_head {a : Axis} {axes : List Axis} {i : ℕ} {t : Tape AxisRecord.T}
    (h : Stored (a::axes) i t) : t.look i AxisRecord.blank=axisData a := by
  simpa using h (0:Fin (a::axes).length)

theorem stored_tail {a : Axis} {axes : List Axis} {i : ℕ} {t : Tape AxisRecord.T}
    (h : Stored (a::axes) i t) : Stored axes (i+1) t := by
  intro k
  simpa [Nat.add_assoc,Nat.add_comm 1] using h k.succ

theorem expand_coefficients {r : Port} (h : Handler r) (a : Axis) (axes : List Axis) :
    ((expand (r:=r)).run h (axisData a,coefficientTape axes)).val =
      coefficientTape (a::axes) := by
  rw [expand_value]
  change Tape.mk (a.radix*(radices axes).prod) _ = Tape.mk (a.radix*(radices axes).prod) _
  congr 1
  funext j
  have vp := volume_positive axes
  have hd : j.val/(radices axes).prod<a.radix :=
    (Nat.div_lt_iff_lt_mul vp).2 j.isLt
  have hm := Nat.mod_lt j.val vp
  simp only [axisData,coefficientTape,Tape.look,hd,hm,↓reduceDIte,
    tensorCoefficient]
  rfl

def coefficientCost : List Axis → ℕ
  | [] => 10
  | a::axes => coefficientCost axes+39*(radices (a::axes)).prod+29

/-- The closed suffix descent computes the same MSB physical tensor product
as the actual tensor traversal, including the empty-axis identity. -/
theorem result_spec (axes : List Axis) (i : ℕ) (t : Tape AxisRecord.T)
    (stored : Stored axes i t) :
    (result axes.length i t).val=coefficientTape axes ∧
      (result axes.length i t).valid ∧
      (result axes.length i t).work=coefficientCost axes ∧
      (result axes.length i t).peak ≤ max (i+axes.length) (radices axes).prod := by
  induction axes generalizing i with
  | nil =>
    simp only [List.length_nil]
    rw [result_zero]
    refine ⟨?_,trivial,rfl,?_⟩
    · rfl
    · simp [radices]
  | cons a axes ih =>
    have tail := ih (i+1) (stored_tail stored)
    rw [List.length_cons,result_succ,stored_head stored]
    let h : Handler RecPort := fun x => result axes.length x.1 x.2
    refine ⟨?_,?_,?_,?_⟩
    · change ((expand (r:=RecPort)).run h
        (axisData a,(result axes.length (i+1) t).val)).val=_
      rw [tail.1,expand_coefficients]
    · change (result axes.length (i+1) t).valid ∧
        ((expand (r:=RecPort)).run h
          (axisData a,(result axes.length (i+1) t).val)).valid
      exact ⟨tail.2.1,expand_valid h _ _ _⟩
    · change (result axes.length (i+1) t).work+
        ((expand (r:=RecPort)).run h
          (axisData a,(result axes.length (i+1) t).val)).work+16+1=_
      rw [tail.2.2.1,tail.1]
      rw [show axisData a=(a.radix,(axisData a).2) from rfl,expand_work]
      simp [coefficientTape,coefficientCost,radices]
      omega
    · change max (max (max (result axes.length (i+1) t).peak
        ((expand (r:=RecPort)).run h
          (axisData a,(result axes.length (i+1) t).val)).peak) (i+1))
            (axes.length+1)≤_
      have vp := volume_positive axes
      have ar := a.positive
      have prodle : (radices axes).prod≤a.radix*(radices axes).prod := by nlinarith
      have ep : ((expand (r:=RecPort)).run h
          (axisData a,(result axes.length (i+1) t).val)).peak=
            a.radix*(radices axes).prod := by
        rw [tail.1]
        exact expand_peak h a.radix (axisData a).2 (coefficientTape axes) ar vp
      rw [ep]
      have tp := tail.2.2.2
      change _ ≤ max (i+(axes.length+1)) (a.radix*(radices axes).prod)
      omega

theorem coefficientCost_linear (axes : List Axis) (two : ∀a∈axes,2≤a.radix) :
    coefficientCost axes≤110*(radices axes).prod := by
  induction axes with
  | nil => simp [coefficientCost,radices]
  | cons a axes ih =>
    have ar := two a (by simp)
    have tail := ih (fun b hb => two b (by simp [hb]))
    have vp := volume_positive axes
    change coefficientCost axes+39*(a.radix*(radices axes).prod)+29≤_
    change _≤110*(a.radix*(radices axes).prod)
    nlinarith

theorem program_run (t : Tape AxisRecord.T) :
    run program t=(result t.len 0 t).pay 7 t.len := by
  unfold program
  simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Bill.word,result]
  simp only [max_zero,true_and,and_true]
  congr 1 <;> omega

/-- Genuine fixed `Code false`, prepared factor input records, exact physical
tensor coefficients, linear work, and a word bound including recursion fuel. -/
theorem program_contract (axes : List Axis) (two : ∀a∈axes,2≤a.radix) :
    (run program (axisTape axes)).val=coefficientTape axes ∧
      (run program (axisTape axes)).valid ∧
      (run program (axisTape axes)).work≤110*(radices axes).prod+7 ∧
      (run program (axisTape axes)).peak ≤ max axes.length (radices axes).prod := by
  rw [program_run]
  have spec := result_spec axes 0 (axisTape axes) (axisTape_stored axes)
  refine ⟨spec.1,spec.2.1,?_,?_⟩
  · change (result axes.length 0 (axisTape axes)).work+7≤_
    rw [spec.2.2.1]
    have h := coefficientCost_linear axes two
    omega
  · change max (result axes.length 0 (axisTape axes)).peak axes.length≤_
    have h : (result axes.length 0 (axisTape axes)).peak≤ max axes.length (radices axes).prod :=
      by simpa only [Nat.zero_add] using spec.2.2.2
    exact max_le h (le_max_left axes.length (radices axes).prod)

end
end ExactFourierCircuits.DFTModelGlobalClockTensor
