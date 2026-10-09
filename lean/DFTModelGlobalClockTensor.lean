import DFTModelAffineCore
import ModelEquivalenceInterpreter
import UniformGlobalTensorDiagonalPreparation

set_option autoImplicit false

/-! A concrete prepared tensor-diagonal producer. The axis records occur in
the actual physical order. One suffix call returns one coefficient tape; the
parent publishes its radix times suffix volume with a fresh tabulation. -/
namespace ExactFourierCircuits.DFTModelGlobalClockTensor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTensorMonomialMachine
noncomputable section

abbrev AxisRecord := p w (Ty.a sc)
abbrev Axes := Ty.a AxisRecord
abbrev Node := p w Axes
abbrev Coefficients := Ty.a sc
abbrev RecPort : Port := some (Node,Coefficients)
abbrev Expansion := p AxisRecord Coefficients
abbrev Cell := p Expansion w

def suffixLength {r : Port} : Code false r Cell w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .len))
def axisFactors {r : Port} : Code false r Cell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def firstFactor {r : Port} : Code false r Cell sc :=
  .comp (.fork axisFactors
    (.comp (.fork (.atom .snd) suffixLength) (.atom (.int .div)))) (.atom .look)
def tailFactor {r : Port} : Code false r Cell sc :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd))
    (.comp (.fork (.atom .snd) suffixLength) (.atom (.int .mod)))) (.atom .look)
def cell {r : Port} : Code false r Cell sc :=
  .comp (.fork firstFactor tailFactor) (.atom (.scale .scalar))
def expansionLength {r : Port} : Code false r Expansion w :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst))
    (.comp (.atom .snd) (.atom .len))) (.atom (.int .mul))
def expand {r : Port} : Code false r Expansion Coefficients :=
  .tab expansionLength cell

def base {r : Port} : Code false r Node Coefficients :=
  .tab (.atom (.lit 1)) (.atom .cone)
def current {r : Port} : Code false r Node AxisRecord :=
  .comp (.fork (.atom .snd) (.atom .fst)) (.atom .look)
def next {r : Port} : Code false r Node Node :=
  .fork (.comp (.fork (.atom .fst) (.atom (.lit 1))) (.atom (.int .add)))
    (.atom .snd)
def body : Code false RecPort Node Coefficients :=
  .comp (.fork current (.comp next .call)) expand
def program : Prog false Axes Coefficients :=
  .comp (.fork (.atom .len) (.fork (.atom (.lit 0)) (.atom .id)))
    (.descend base body)

theorem cell_run {r : Port} (h : Handler r) (radix j : ℕ)
    (f v : Tape ℂ) :
    cell.run h (((radix,f),v),j) =
      ⟨f.look (j/v.len) 0*v.look (j%v.len) 0,35,
        max v.len (max (j/v.len) (j%v.len)),True⟩ := by
  simp [cell,firstFactor,tailFactor,axisFactors,suffixLength,Code.run,
    Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  omega

theorem expansionLength_run {r : Port} (h : Handler r) (radix : ℕ)
    (f v : Tape ℂ) :
    expansionLength.run h ((radix,f),v) =
      ⟨radix*v.len,9,max v.len (radix*v.len),True⟩ := by
  simp [expansionLength,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] cell expansionLength

theorem expand_run {r : Port} (h : Handler r) (radix : ℕ) (f v : Tape ℂ) :
    (expand (r:=r)).run h ((radix,f),v) =
      (Bill.tab (radix*v.len) sc.blank
        (fun j => (cell (r:=r)).run h (((radix,f),v),j))).pay 10
          (max v.len (radix*v.len)) := by
  unfold expand
  change ((expansionLength.run h ((radix,f),v)).pass
    (fun len => Bill.tab len sc.blank
      (fun j => cell.run h (((radix,f),v),j)))).pay 1 0 = _
  rw [expansionLength_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem expand_value {r : Port} (h : Handler r) (radix : ℕ) (f v : Tape ℂ) :
    (expand.run h ((radix,f),v)).val = Tape.tab (radix*v.len)
      (fun j => f.look (j/v.len) 0*v.look (j%v.len) 0) := by
  rw [expand_run]
  change (Bill.tab (radix*v.len) sc.blank
    (fun j => (cell (r:=r)).run h (((radix,f),v),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (fun j => congrArg Bill.val (cell_run h radix j f v)))

theorem expand_work {r : Port} (h : Handler r) (radix : ℕ) (f v : Tape ℂ) :
    (expand.run h ((radix,f),v)).work = 39*(radix*v.len)+12 := by
  rw [expand_run]
  change (Bill.tab (radix*v.len) sc.blank
    (fun j => (cell (r:=r)).run h (((radix,f),v),j))).work+10 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw : (fun j => (cell.run h (((radix,f),v),j)).work) = fun _ => 35 := by
    funext j; exact congrArg Bill.work (cell_run h radix j f v)
  rw [hw]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem expand_peak {r : Port} (h : Handler r) (radix : ℕ) (f v : Tape ℂ) :
    0 < radix → 0 < v.len → (expand.run h ((radix,f),v)).peak = radix*v.len := by
  intro hr hv
  rw [expand_run]
  change max (Bill.tab (radix*v.len) sc.blank
      (fun j => (cell (r:=r)).run h (((radix,f),v),j))).peak
        (max v.len (radix*v.len)) = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have vl : v.len ≤ radix*v.len := by nlinarith
  have pp : (Finset.range (radix*v.len)).sup
      (fun j => (cell.run h (((radix,f),v),j)).peak) ≤ radix*v.len := by
    apply Finset.sup_le
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [cell_run]
    have hd : j/v.len < radix := (Nat.div_lt_iff_lt_mul hv).2 (by simpa [Nat.mul_comm] using hj)
    have hm := Nat.mod_lt j hv
    have rl : radix ≤ radix*v.len := by nlinarith
    dsimp only [Bill.peak]
    omega
  omega

theorem expand_valid {r : Port} (h : Handler r) (radix : ℕ) (f v : Tape ℂ) :
    (expand.run h ((radix,f),v)).valid := by
  rw [expand_run]
  change (Bill.tab (radix*v.len) sc.blank
    (fun j => (cell (r:=r)).run h (((radix,f),v),j))).valid
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _; rw [cell_run]; trivial

theorem base_run {r : Port} (h : Handler r) (i : ℕ) (axes : Tape AxisRecord.T) :
    base.run h (i,axes) = ⟨Tape.tab 1 (fun _ => 1),9,1,True⟩ := by
  have val : (base.run h (i,axes)).val=Tape.tab 1 (fun _ => 1) := by
    change (Bill.tab 1 sc.blank (fun _ => Bill.one (1:ℂ))).val=_
    rw [ModelEquivalenceInterpreter.tab_value]
    rfl
  have work : (base.run h (i,axes)).work=9 := by
    change 1+(Bill.tab 1 sc.blank (fun _ => Bill.one (1:ℂ))).work+1=_
    rw [ModelEquivalenceInterpreter.tab_work]
    simp [Bill.one]
  have peak : (base.run h (i,axes)).peak=1 := by
    change max (max 1 (Bill.tab 1 sc.blank (fun _ => Bill.one (1:ℂ))).peak) 0=_
    rw [ModelEquivalenceInterpreter.tab_peak]
    simp [Bill.one]
  have valid : (base.run h (i,axes)).valid := by
    change True ∧ (Bill.tab 1 sc.blank (fun _ => Bill.one (1:ℂ))).valid
    exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 (by simp [Bill.one])⟩
  cases hb : base.run h (i,axes)
  simp_all

attribute [local irreducible] expand base

theorem body_run (h : Handler RecPort) (i : ℕ) (axes : Tape AxisRecord.T) :
    body.run h (i,axes) =
      ((h (i+1,axes)).pass
        (fun v => (expand (r:=RecPort)).run h (axes.look i AxisRecord.blank,v))).pay 16 (i+1) := by
  simp only [body,current,next,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,
    Bill.one,Bill.word]
  congr 1 <;> simp <;> omega

def result (fuel i : ℕ) (axes : Tape AxisRecord.T) : Bill (Tape ℂ) :=
  depthRun ((base (r:=none)).run ()) body.run fuel (i,axes)

theorem result_zero (i : ℕ) (axes : Tape AxisRecord.T) :
    result 0 i axes = ⟨Tape.tab 1 (fun _ => 1),10,1,True⟩ := by
  change ((base (r:=none)).run () (i,axes)).pay 1 0 = _
  rw [base_run]; rfl

theorem result_succ (fuel i : ℕ) (axes : Tape AxisRecord.T) :
    result (fuel+1) i axes =
      (((result fuel (i+1) axes).pass
        (fun v => (expand (r:=RecPort)).run (fun x : Node.T => result fuel x.1 x.2)
          (axes.look i AxisRecord.blank,v))).pay 16 (i+1)).pay 1 (fuel+1) := by
  change (body.run (fun x : Node.T => result fuel x.1 x.2) (i,axes)).pay 1 (fuel+1) = _
  rw [body_run]

end
end ExactFourierCircuits.DFTModelGlobalClockTensor
