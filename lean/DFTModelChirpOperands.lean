import DFTModelChirpSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirpOperands
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p DFTModelChirpTables.Input (Ty.a (c .left))
abbrev Full := p DFTModelChirpTables.Output (Ty.a (c .left))
abbrev Cell := p Full w
abbrev Output := p DFTModelChirpTables.Output (Ty.a (c .left))

def coefficients : Prog false Full (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def cellCoefficients : Prog false Cell (Ty.a sc) := .comp (.atom .fst) coefficients
def length : Prog false Full w := .comp coefficients (.atom .len)
def coefficient : Prog false Cell sc :=
  .comp (.fork cellCoefficients (.atom .snd)) (.atom .look)
def datum : Prog false Cell (c .left) :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def cell : Prog false Cell (c .left) :=
  .comp (.fork coefficient datum) (.atom (.scale .left))
def publish : Prog false Full (Ty.a (c .left)) := .tab length cell
def setup : Prog false Input Full :=
  .fork (.comp (.atom .fst) DFTModelChirpTables.program) (.atom .snd)

/-- A real input operand is multiplied by internally generated chirps, using only
prepared-scalar/data scaling. Zero padding has the same numeric value as source. -/
def program : Prog false Input Output :=
  .comp setup (.fork (.atom .fst) publish)

theorem cell_run (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) (i : ℕ) :
    run cell ((o,v),i)=⟨o.2.2.1.look i 0*v.look i 0,23,0,True⟩ := by
  simp [cell,coefficient,cellCoefficients,coefficients,datum,
    Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem length_run (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    run length (o,v)=⟨o.2.2.1.len,9,o.2.2.1.len,True⟩ := by
  simp [length,coefficients,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] length publish DFTModelChirpTables.program

theorem publish_run (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    run publish (o,v)=(Bill.tab o.2.2.1.len (c .left).blank
      (fun i => run cell ((o,v),i))).pay 10 o.2.2.1.len := by
  unfold publish
  change ((run length (o,v)).pass
    (fun k => Bill.tab k (c .left).blank (fun i => run cell ((o,v),i)))).pay 1 0 = _
  rw [length_run]
  simp [Bill.pass,Bill.pay]
  constructor <;> omega

theorem publish_value (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    (run publish (o,v)).val=Tape.tab o.2.2.1.len
      (fun i => o.2.2.1.look i 0*v.look i 0) := by
  rw [publish_run]
  change (Bill.tab o.2.2.1.len (c .left).blank (fun i => run cell ((o,v),i))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab o.2.2.1.len) (funext (fun i => congrArg Bill.val (cell_run o v i)))

theorem publish_work (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    (run publish (o,v)).work=27*o.2.2.1.len+12 := by
  rw [publish_run]
  change (Bill.tab o.2.2.1.len (c .left).blank (fun i => run cell ((o,v),i))).work+10 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun i => (run cell ((o,v),i)).work)=(fun _ : ℕ => 23) := by
    funext i
    exact congrArg Bill.work (cell_run o v i)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem publish_peak (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    (run publish (o,v)).peak=o.2.2.1.len := by
  rw [publish_run]
  change max (Bill.tab o.2.2.1.len (c .left).blank (fun i => run cell ((o,v),i))).peak
    o.2.2.1.len = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (fun i => (run cell ((o,v),i)).peak)=(fun _ : ℕ => 0) := by
    funext i
    exact congrArg Bill.peak (cell_run o v i)
  rw [h]
  simp

theorem publish_valid (o : DFTModelChirpTables.Output.T) (v : Tape ℂ) :
    (run publish (o,v)).valid := by
  rw [publish_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro i _
  rw [cell_run]
  trivial

theorem program_run (n L : ℕ) (z : ℂ) (v : Tape ℂ) :
    run program (((n,L),z),v)=
      ((run DFTModelChirpTables.program ((n,L),z)).pass
        (fun o => (run publish (o,v)).pass (fun y => Bill.one (o,y)))).pay 6 0 := by
  simp only [program,setup,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true,zero_max,max_zero]
  dsimp only [run]
  congr 1
  omega

theorem coefficients_length (n L : ℕ) (z : ℂ) :
    (run DFTModelChirpTables.program ((n,L),z)).val.2.2.1.len=L := by
  rw [DFTModelChirpTables.program_run]
  change (run DFTModelChirpTables.publish ((n,L),(run DFTModelChirp.program (n,z)).val)).val.2.2.1.len = _
  rw [DFTModelChirpTables.publish_value]
  rfl

theorem program_first (n L : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run program (((n,L),z),v)).val.1=(run DFTModelChirpTables.program ((n,L),z)).val := by
  rw [program_run]
  rfl

theorem program_value (n L : ℕ) (z : ℂ) (v : Tape ℂ) (hn : 0<n) (hz : z^(2*n)=1) :
    (run program (((n,L),z),v)).val=
      (DFTModelChirpTables.values n L (DFTModelChirp.bank n z),
        Tape.tab L (fun i => (DFTModelChirpTables.values n L (DFTModelChirp.bank n z)).2.2.1.look i 0*v.look i 0)) := by
  rw [program_run]
  change ((run DFTModelChirpTables.program ((n,L),z)).val,
    (run publish ((run DFTModelChirpTables.program ((n,L),z)).val,v)).val) = _
  rw [DFTModelChirpTables.program_value n L z hn hz,publish_value]
  rfl

theorem program_valid (n L : ℕ) (z : ℂ) (v : Tape ℂ) (hL : 0<L) :
    (run program (((n,L),z),v)).valid := by
  rw [program_run]
  exact ⟨DFTModelChirpTables.program_valid n L z hL, publish_valid _ _,trivial⟩

theorem program_work (n L : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run program (((n,L),z),v)).work≤700*(n+L+1) := by
  rw [program_run]
  change (run DFTModelChirpTables.program ((n,L),z)).work+
    ((run publish ((run DFTModelChirpTables.program ((n,L),z)).val,v)).work+1)+6≤_
  rw [publish_work,coefficients_length]
  have ht := DFTModelChirpTables.program_work n L z
  omega

theorem program_peak (n L : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run program (((n,L),z),v)).peak≤(n+L+2)^2 := by
  rw [program_run]
  change max (max (run DFTModelChirpTables.program ((n,L),z)).peak
    (max (run publish ((run DFTModelChirpTables.program ((n,L),z)).val,v)).peak 0)) 0≤_
  rw [publish_peak,coefficients_length]
  have ht := DFTModelChirpTables.program_peak n L z
  have hL : L≤(n+L+2)^2 := by
    have h1 : 1≤n+L+2 := by omega
    have h2 := Nat.mul_le_mul_left (n+L+2) h1
    simp only [Nat.mul_one,←pow_two] at h2
    omega
  omega

theorem padded_value {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) (L : ℕ)
    (z : ℂ) (hz : z^(2*n)=1) :
    (run program (((n,L),z),Tape.mk n x)).val.2=
      Tape.tab L (fun i => (UniformPaddedInputMachine.paddedScalar z x i).value) := by
  rw [program_value n L z _ hn hz]
  change Tape.mk L _ = Tape.mk L _
  congr 1
  funext i
  exact DFTModelChirpTables.padded_input_value x L i.val z i.isLt

/-- Actual selected working length gives linear outer preparation and a fixed
polynomial integer cap. Length/root selection is composed by the caller. -/
theorem working_contract {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    (run program (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),Tape.mk n x)).valid ∧
    (run program (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),Tape.mk n x)).work≤3500*(n+1) ∧
    (run program (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),Tape.mk n x)).peak≤(n+2)^4 := by
  refine ⟨program_valid n _ _ _ (UniformWorkingLength.workingLength_pos hn),?_,?_⟩
  · have h := program_work n (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) (Tape.mk n x)
    have hL := UniformWorkingLength.workingLength_upper hn
    omega
  · have h := program_peak n (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) (Tape.mk n x)
    have hL := UniformWorkingLength.workingLength_upper hn
    have hbase : n+UniformWorkingLength.workingLength n+2≤(n+2)^2 := by nlinarith
    have hp := Nat.pow_le_pow_left hbase 2
    have he : ((n+2)^2)^2=(n+2)^4 := by ring
    rw [he] at hp
    exact h.trans hp

/-- Both actual initial-state source preparation and the closed typed producer
agree on chirp/output/kernel/normalization addresses and padded input values. -/
theorem source_preparation {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃t u, UniformMachine.BoundedExecution UniformNormalizationPreparation.fullProgram n x
      ((n+2)^19) UniformMachine.initial t u ∧
      DFTModelChirpTables.SourceMatch x
        (run program (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),Tape.mk n x)).val.1 u ∧
      (∀j,j<UniformWorkingLength.workingLength n →
        (u.scalarHeap (UniformPaddedInputPreparation.dataBase n+j)).map UniformMachine.Scalar.value=
          some ((run program (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),Tape.mk n x)).val.2.look j 0)) ∧
      t≤UniformNormalizationPreparation.fullPreparationBudget n := by
  obtain ⟨t,u,he,hm,hcost⟩ := DFTModelChirpTables.source_preparation hn x
  refine ⟨t,u,he,?_,?_,hcost⟩
  · rw [program_first]
    exact hm
  · intro j hj
    rw [hm.input j hj,program_value n _ _ _ hn (DFTModelChirp.specified_period n hn)]
    rw [DFTModelChirpTables.program_value n _ _ hn (DFTModelChirp.specified_period n hn)]
    simp only [Tape.look,Tape.tab,hj,↓reduceDIte]

end
end ExactFourierCircuits.DFTModelChirpOperands
