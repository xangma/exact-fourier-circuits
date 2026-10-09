import DFTModelGlobalClockTensorCorrect

set_option autoImplicit false

/-! Charged extraction of one actual diagonal lane from the source's
two-word (radix,pool) records and readonly prepared scalar heap. -/
namespace ExactFourierCircuits.DFTModelGlobalClockRecords
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Record := p w w
abbrev Input := p w (p (Ty.a Record) (Ty.a sc))
abbrev AxisInput := p w (p Record (Ty.a sc))
abbrev AxisCell := p AxisInput w
abbrev DirectoryCell := p Input w

def radix : Prog false AxisInput w :=
  .comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))
def lane : Prog false AxisCell w := .comp (.atom .fst) (.atom .fst)
def cellRadix : Prog false AxisCell w := .comp (.atom .fst) radix
def pool : Prog false AxisCell w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
def heap : Prog false AxisCell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def address : Prog false AxisCell w :=
  .comp (.fork
    (.comp (.fork pool
      (.comp (.fork lane cellRadix) (.atom (.int .mul)))) (.atom (.int .add)))
    (.atom .snd)) (.atom (.int .add))
def factor : Prog false AxisCell sc := .comp (.fork heap address) (.atom .look)
def factors : Prog false AxisInput (Ty.a sc) := .tab radix factor
def axis : Prog false AxisInput DFTModelGlobalClockTensor.AxisRecord := .fork radix factors

def recordRead : Prog false DirectoryCell Record :=
  .comp (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
    (.atom .snd)) (.atom .look)
def axisInput : Prog false DirectoryCell AxisInput :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork recordRead (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))))
def entry : Prog false DirectoryCell DFTModelGlobalClockTensor.AxisRecord := .comp axisInput axis
def count : Prog false Input w := .comp (.comp (.atom .snd) (.atom .fst)) (.atom .len)
def program : Prog false Input DFTModelGlobalClockTensor.Axes := .tab count entry

theorem factor_run (l r P j : ℕ) (h : Tape ℂ) :
    run factor ((l,((r,P),h)),j)=⟨h.look (P+l*r+j) 0,35,P+l*r+j,True⟩ := by
  simp [factor,address,pool,lane,cellRadix,radix,heap,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem radix_run (l r P : ℕ) (h : Tape ℂ) :
    run radix (l,((r,P),h))=⟨r,5,0,True⟩ := by
  simp [radix,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] factor radix

theorem factors_run (l r P : ℕ) (h : Tape ℂ) :
    run factors (l,((r,P),h))=
      (Bill.tab r sc.blank (fun j => run factor ((l,((r,P),h)),j))).pay 6 0 := by
  unfold factors
  change ((run radix (l,((r,P),h))).pass
    (fun len => Bill.tab len sc.blank (fun j => run factor ((l,((r,P),h)),j)))).pay 1 0=_
  rw [radix_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem factors_value (l r P : ℕ) (h : Tape ℂ) :
    (run factors (l,((r,P),h))).val=Tape.tab r (fun j => h.look (P+l*r+j) 0) := by
  rw [factors_run]
  change (Bill.tab r sc.blank (fun j => run factor ((l,((r,P),h)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (fun j => congrArg Bill.val (factor_run l r P j h)))

theorem factors_work (l r P : ℕ) (h : Tape ℂ) :
    (run factors (l,((r,P),h))).work=39*r+8 := by
  rw [factors_run]
  change (Bill.tab r sc.blank (fun j => run factor ((l,((r,P),h)),j))).work+6=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw : (fun j => (run factor ((l,((r,P),h)),j)).work)=fun _ => 35 := by
    funext j;exact congrArg Bill.work (factor_run l r P j h)
  rw [hw]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem factors_valid (l r P : ℕ) (h : Tape ℂ) :
    (run factors (l,((r,P),h))).valid := by
  rw [factors_run]
  change (Bill.tab r sc.blank (fun j => run factor ((l,((r,P),h)),j))).valid
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _;rw [factor_run];trivial

theorem factors_peak (l r P B : ℕ) (h : Tape ℂ)
    (radixFit : r≤B) (poolFit : P+(l+1)*r≤B) :
    (run factors (l,((r,P),h))).peak≤B := by
  rw [factors_run]
  change max (Bill.tab r sc.blank
    (fun j => run factor ((l,((r,P),h)),j))).peak 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have bound : (Finset.range r).sup (fun j => (run factor ((l,((r,P),h)),j)).peak)≤B := by
    apply Finset.sup_le
    intro j hj
    rw [factor_run]
    have hj := Finset.mem_range.mp hj
    dsimp only [Bill.peak]
    nlinarith
  omega

attribute [local irreducible] factors

theorem axis_run (l r P : ℕ) (h : Tape ℂ) :
    run axis (l,((r,P),h))=
      ⟨(r,(run factors (l,((r,P),h))).val),39*r+14,
        (run factors (l,((r,P),h))).peak,True⟩ := by
  change (run radix (l,((r,P),h))).pass
    (fun x => (run factors (l,((r,P),h))).pass (fun y => Bill.one (x,y)))=_
  rw [radix_run]
  have hw := factors_work l r P h
  have hv := factors_valid l r P h
  simp [Bill.pass,Bill.one,hw,hv]
  omega

theorem axisInput_run (l j : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    run axisInput ((l,(d,h)),j)=⟨(l,(d.look j Record.blank,h)),19,0,True⟩ := by
  simp [axisInput,recordRead,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] axis axisInput

theorem entry_run (l j : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    run entry ((l,(d,h)),j)=
      ⟨((d.look j Record.blank).1,
          (run factors (l,(d.look j Record.blank,h))).val),
        39*(d.look j Record.blank).1+34,
        (run factors (l,(d.look j Record.blank,h))).peak,True⟩ := by
  unfold entry
  change ((run axisInput ((l,(d,h)),j)).pass (fun z => run axis z)).pay 1 0=_
  rw [axisInput_run]
  simp only [Bill.pass,Bill.pay]
  rw [axis_run]
  simp
  omega

def directory (as : List UniformGlobalDiagonalRowsMachine.Entry) : Tape Record.T :=
  ⟨as.length,fun i => ((as.get i).radix,(as.get i).pool)⟩

/-- Concrete readonly representation of the actual prepared factor-pool
cells; every lookup below is charged by the literal Code above. -/
def PoolValues (as : List UniformGlobalDiagonalRowsMachine.Entry) (h : Tape ℂ) : Prop :=
  ∀a∈as,∀l : Fin 9,∀j : Fin a.radix,h.look (a.pool+l.val*a.radix+j.val) 0=a.value l j

theorem actual_entry (as : List UniformGlobalDiagonalRowsMachine.Entry) (l : Fin 9)
    (h : Tape ℂ) (pools : PoolValues as h) (i : Fin as.length) :
    (run entry ((l.val,(directory as,h)),i.val)).val=
      DFTModelGlobalClockTensor.axisData
        (UniformGlobalDiagonalRowsMachine.axis l 0 0 0 (as.get i)) := by
  rw [entry_run]
  have read : (directory as).look i.val Record.blank=((as.get i).radix,(as.get i).pool) := by
    simp [directory,Tape.look,i.isLt]
  simp only [read]
  rw [factors_value]
  change ((as.get i).radix,Tape.mk (as.get i).radix _)=
    ((as.get i).radix,Tape.mk (as.get i).radix _)
  congr 2
  funext j
  exact pools (as.get i) (List.get_mem as i) l j

theorem count_run (l : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    run count (l,(d,h))=⟨d.len,5,d.len,True⟩ := by
  simp [count,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] entry count

theorem program_run (l : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    run program (l,(d,h))=
      (Bill.tab d.len DFTModelGlobalClockTensor.AxisRecord.blank
        (fun j => run entry ((l,(d,h)),j))).pay 6 d.len := by
  unfold program
  change ((run count (l,(d,h))).pass (fun n =>
    Bill.tab n DFTModelGlobalClockTensor.AxisRecord.blank
      (fun j => run entry ((l,(d,h)),j)))).pay 1 0=_
  rw [count_run]
  simp [Bill.pass,Bill.pay]
  omega

def listTape {α : Type} (xs : List α) : Tape α := ⟨xs.length,xs.get⟩

theorem tape_ext {α : Type} (z : α) (t u : Tape α) (length : t.len=u.len)
    (values : ∀j< t.len,t.look j z=u.look j z) : t=u := by
  cases t with
  | mk n f =>
    cases u with
    | mk m g =>
      dsimp only [Tape.len] at length
      subst m
      congr 1
      funext i
      have eq := values i.val i.isLt
      simpa [Tape.look,i.isLt] using eq

theorem axisTape_listTape (axes : List UniformTensorMonomialMachine.Axis) :
    DFTModelGlobalClockTensor.axisTape axes=
      listTape (axes.map DFTModelGlobalClockTensor.axisData) := by
  apply tape_ext DFTModelGlobalClockTensor.AxisRecord.blank
  · simp [DFTModelGlobalClockTensor.axisTape,listTape]
  · intro j hj
    change j<axes.length at hj
    simp [DFTModelGlobalClockTensor.axisTape,listTape,Tape.look,hj]

theorem actual_axis_data (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (l : Fin 9) (P C o : ℕ) :
    (UniformGlobalDiagonalRowsMachine.axes l P C o as).map
      DFTModelGlobalClockTensor.axisData=
      as.map (fun a => DFTModelGlobalClockTensor.axisData
        (UniformGlobalDiagonalRowsMachine.axis l 0 0 0 a)) := by
  induction as generalizing o with
  | nil => rfl
  | cons a as ih =>
    simp only [UniformGlobalDiagonalRowsMachine.axes,List.map_cons,ih]
    rfl

/-- The dynamic lane/pool reads produce precisely the actual source axis
records; no tensor-factor output tape is supplied to this program. -/
theorem program_value (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (l : Fin 9) (P C o : ℕ) (h : Tape ℂ) (pools : PoolValues as h) :
    (run program (l.val,(directory as,h))).val=
      DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes l P C o as) := by
  rw [program_run]
  change (Bill.tab (directory as).len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j => run entry ((l.val,(directory as,h)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value,axisTape_listTape,actual_axis_data]
  apply tape_ext DFTModelGlobalClockTensor.AxisRecord.blank
  · simp [Tape.tab,directory,listTape]
  · intro j hj
    change j<as.length at hj
    have e := actual_entry as l h pools ⟨j,hj⟩
    simpa [Tape.tab,Tape.look,listTape,directory,hj] using e

theorem program_work (l : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    (run program (l,(d,h))).work=
      8+38*d.len+39*(∑j∈Finset.range d.len,(d.look j Record.blank).1) := by
  rw [program_run]
  change (Bill.tab d.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j => run entry ((l,(d,h)),j))).work+6=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw : (fun j => (run entry ((l,(d,h)),j)).work)=
      fun j => 39*(d.look j Record.blank).1+34 := by
    funext j;exact congrArg Bill.work (entry_run l j d h)
  rw [hw,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (l : ℕ) (d : Tape Record.T) (h : Tape ℂ) :
    (run program (l,(d,h))).valid := by
  rw [program_run]
  change (Bill.tab d.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j => run entry ((l,(d,h)),j))).valid
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _;rw [entry_run];trivial

theorem program_peak (l B : ℕ) (d : Tape Record.T) (h : Tape ℂ)
    (countFit : d.len≤B) (radixFit : ∀j<d.len,(d.look j Record.blank).1≤B)
    (poolFit : ∀j<d.len,(d.look j Record.blank).2+(l+1)*(d.look j Record.blank).1≤B) :
    (run program (l,(d,h))).peak≤B := by
  rw [program_run]
  change max (Bill.tab d.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j => run entry ((l,(d,h)),j))).peak d.len≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have bound : (Finset.range d.len).sup (fun j => (run entry ((l,(d,h)),j)).peak)≤B := by
    apply Finset.sup_le
    intro j hj
    rw [entry_run]
    have hj := Finset.mem_range.mp hj
    exact factors_peak l _ _ B h (radixFit j hj) (poolFit j hj)
  omega

end
end ExactFourierCircuits.DFTModelGlobalClockRecords
