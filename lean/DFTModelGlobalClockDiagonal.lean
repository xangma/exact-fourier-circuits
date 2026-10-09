import DFTModelGlobalClockTensorCorrect
import DFTModelMemoryAffinePointwise

set_option autoImplicit false

/-! A concrete global diagonal event. The coefficient descent runs once for
all roles; one fresh role-major tabulation scales both affine channels. -/
namespace ExactFourierCircuits.DFTModelGlobalClockDiagonal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTensorMonomialMachine
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Input := p w (p DFTModelGlobalClockTensor.Axes (Ty.a Datum))
abbrev Ready := p w (p (Ty.a sc) (Ty.a Datum))
abbrev Cell := p Ready w

def coefficients : Prog false Cell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def source : Prog false Cell (Ty.a Datum) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def volume : Prog false Cell w := .comp coefficients (.atom .len)
def factor : Prog false Cell sc :=
  .comp (.fork coefficients
    (.comp (.fork (.atom .snd) volume) (.atom (.int .mod)))) (.atom .look)
def datum : Prog false Cell Datum := .comp (.fork source (.atom .snd)) (.atom .look)
def cell : Prog false Cell Datum :=
  .comp (.fork datum factor) DFTModelMemoryAffinePointwise.multiply
def outputLength : Prog false Ready w :=
  .comp (.fork (.atom .fst)
    (.comp (.comp (.atom .snd) (.atom .fst)) (.atom .len))) (.atom (.int .mul))
def publish : Prog false Ready (Ty.a Datum) := .tab outputLength cell
def ready : Prog false Input Ready :=
  .fork (.atom .fst) (.fork
    (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelGlobalClockTensor.program)
    (.comp (.atom .snd) (.atom .snd)))
def program : Prog false Input (Ty.a Datum) := .comp ready publish

theorem cell_run (W j : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    run cell ((W,(f,v)),j)=
      ⟨DFTModelMemoryAffinePointwise.scaled (v.look j Datum.blank)
          (f.look (j%f.len) 0),55,max f.len (j%f.len),True⟩ := by
  unfold cell
  change ((run (.fork datum factor) ((W,(f,v)),j)).pass
    (fun z => run DFTModelMemoryAffinePointwise.multiply z)).pay 1 0=_
  have first : run (.fork datum factor) ((W,(f,v)),j)=
      ⟨(v.look j Datum.blank,f.look (j%f.len) 0),29,max f.len (j%f.len),True⟩ := by
    simp [datum,factor,source,coefficients,volume,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  rw [first]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelMemoryAffinePointwise.multiply_run]
  simp

theorem outputLength_run (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    run outputLength (W,(f,v))=⟨W*f.len,9,max f.len (W*f.len),True⟩ := by
  simp [outputLength,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] cell outputLength

theorem publish_run (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    run publish (W,(f,v))=
      (Bill.tab (W*f.len) Datum.blank (fun j => run cell ((W,(f,v)),j))).pay
        10 (max f.len (W*f.len)) := by
  unfold publish
  change ((run outputLength (W,(f,v))).pass
    (fun L => Bill.tab L Datum.blank (fun j => run cell ((W,(f,v)),j)))).pay 1 0=_
  rw [outputLength_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem publish_value (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    (run publish (W,(f,v))).val=Tape.tab (W*f.len) (fun j =>
      DFTModelMemoryAffinePointwise.scaled (v.look j Datum.blank)
        (f.look (j%f.len) 0)) := by
  rw [publish_run]
  change (Bill.tab (W*f.len) Datum.blank (fun j => run cell ((W,(f,v)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (fun j => congrArg Bill.val (cell_run W j f v)))

theorem publish_work (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    (run publish (W,(f,v))).work=59*(W*f.len)+12 := by
  rw [publish_run]
  change (Bill.tab (W*f.len) Datum.blank (fun j => run cell ((W,(f,v)),j))).work+10=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw : (fun j => (run cell ((W,(f,v)),j)).work)=fun _ => 55 := by
    funext j; exact congrArg Bill.work (cell_run W j f v)
  rw [hw]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem publish_valid (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T) :
    (run publish (W,(f,v))).valid := by
  rw [publish_run]
  change (Bill.tab (W*f.len) Datum.blank (fun j => run cell ((W,(f,v)),j))).valid
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _; rw [cell_run]; trivial

theorem publish_peak (W : ℕ) (f : Tape ℂ) (v : Tape Datum.T)
    (roles : 0<W) (positive : 0<f.len) :
    (run publish (W,(f,v))).peak=W*f.len := by
  rw [publish_run]
  change max (Bill.tab (W*f.len) Datum.blank
    (fun j => run cell ((W,(f,v)),j))).peak (max f.len (W*f.len))=_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have fl : f.len≤W*f.len := by nlinarith
  have ps : (Finset.range (W*f.len)).sup (fun j => (run cell ((W,(f,v)),j)).peak)≤W*f.len := by
    apply Finset.sup_le
    intro j _
    rw [cell_run]
    have hm := Nat.mod_lt j positive
    dsimp only [Bill.peak]
    omega
  omega

attribute [local irreducible] publish DFTModelGlobalClockTensor.program

theorem ready_run (W : ℕ) (a : Tape DFTModelGlobalClockTensor.AxisRecord.T)
    (v : Tape Datum.T) :
    run ready (W,(a,v))=
      ⟨(W,((run DFTModelGlobalClockTensor.program a).val,v)),
        (run DFTModelGlobalClockTensor.program a).work+10,
        (run DFTModelGlobalClockTensor.program a).peak,
        (run DFTModelGlobalClockTensor.program a).valid⟩ := by
  simp [ready,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem program_run (W : ℕ) (a : Tape DFTModelGlobalClockTensor.AxisRecord.T)
    (v : Tape Datum.T) :
    run program (W,(a,v))=
      (((run DFTModelGlobalClockTensor.program a).pass
        (fun f => run publish (W,(f,v)))).pay 11 0) := by
  unfold program
  change ((run ready (W,(a,v))).pass (fun z => run publish z)).pay 1 0=_
  rw [ready_run]
  simp [Bill.pass,Bill.pay]
  omega

/-- Concrete role-major output; the same tensor coefficient is reused across
roles and multiplies offset and data without changing the dependency tag. -/
theorem program_contract (W : ℕ) (axes : List Axis) (v : Tape Datum.T)
    (roles : 0<W) (two : ∀a∈axes,2≤a.radix) :
    (run program (W,(DFTModelGlobalClockTensor.axisTape axes,v))).val=
      Tape.tab (W*(radices axes).prod) (fun j =>
        DFTModelMemoryAffinePointwise.scaled (v.look j Datum.blank)
          ((DFTModelGlobalClockTensor.coefficientTape axes).look
            (j%(radices axes).prod) 0)) ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape axes,v))).valid ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape axes,v))).work≤
        169*(W*(radices axes).prod)+30 ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape axes,v))).peak≤
        max axes.length (W*(radices axes).prod) := by
  rw [program_run]
  have coeff := DFTModelGlobalClockTensor.program_contract axes two
  have vp := volume_positive axes
  have vl : (radices axes).prod≤W*(radices axes).prod := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · change (run publish (W,((run DFTModelGlobalClockTensor.program
      (DFTModelGlobalClockTensor.axisTape axes)).val,v))).val=_
    rw [coeff.1,publish_value]
    rfl
  · exact ⟨coeff.2.1,publish_valid _ _ _⟩
  · change (run DFTModelGlobalClockTensor.program
      (DFTModelGlobalClockTensor.axisTape axes)).work+
      (run publish (W,((run DFTModelGlobalClockTensor.program
        (DFTModelGlobalClockTensor.axisTape axes)).val,v))).work+11≤_
    rw [coeff.1,publish_work]
    have cw := coeff.2.2.1
    change _+59*(W*(radices axes).prod)+12+11≤_
    omega
  · change max (max (run DFTModelGlobalClockTensor.program
      (DFTModelGlobalClockTensor.axisTape axes)).peak
      (run publish (W,((run DFTModelGlobalClockTensor.program
        (DFTModelGlobalClockTensor.axisTape axes)).val,v))).peak) 0≤_
    rw [coeff.1,publish_peak W _ v roles vp]
    have cp := coeff.2.2.2
    change max (max _ (W*(radices axes).prod)) 0≤_
    omega

end
end ExactFourierCircuits.DFTModelGlobalClockDiagonal
