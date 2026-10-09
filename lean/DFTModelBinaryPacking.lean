import DFTModelBinaryAffine

set_option autoImplicit false

/-!
# Charged physical-bank to pair-bank translation

This is actual upstream `Code false`: one fresh tape, two readonly cell
lookups per pair, and the same quotient/remainder addresses as the actual
binary stage. Thus the pair representation used by the stage bridge need not
be granted as a free materialized permutation.
-/
namespace ExactFourierCircuits.DFTModelBinaryPacking
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w (p w (Ty.a DFTModelAffine.Tagged))
abbrev CellInput := p Input w

def stride : Prog false CellInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def oldTape : Prog false CellInput (Ty.a DFTModelAffine.Tagged) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def remainder : Prog false CellInput w :=
  .comp (.fork (.atom .snd) stride) (.atom (.int .mod))
def quotient : Prog false CellInput w :=
  .comp (.fork (.atom .snd) stride) (.atom (.int .div))
def doubled : Prog false CellInput w :=
  .comp (.fork (.atom (.lit 2)) quotient) (.atom (.int .mul))
def digit (t : ℕ) : Prog false CellInput w :=
  .comp (.fork (.atom (.lit t)) doubled) (.atom (.int .add))
def scaled (t : ℕ) : Prog false CellInput w :=
  .comp (.fork stride (digit t)) (.atom (.int .mul))
def address (t : ℕ) : Prog false CellInput w :=
  .comp (.fork remainder (scaled t)) (.atom (.int .add))
def read (t : ℕ) : Prog false CellInput DFTModelAffine.Tagged :=
  .comp (.fork oldTape (address t)) (.atom .look)
def cell : Prog false CellInput DFTModelBinaryAffinePair.Pair := .fork (read 0) (read 1)
def program : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .tab (.atom .fst) cell

def addressPeak (P j t : ℕ) : ℕ :=
  max (max (j%P) (max (max t (max 2 (max (j/P) (2*(j/P)))))
    (max (t+2*(j/P)) (P*(t+2*(j/P))))))
    (UniformTensorAddressMachine.address P 2 j t)

theorem address_run (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) (j t : ℕ) :
    run (address t) ((M,(P,v)),j) =
      ⟨UniformTensorAddressMachine.address P 2 j t,37,addressPeak P j t,True⟩ := by
  simp [address,scaled,digit,doubled,quotient,remainder,stride,addressPeak,
    UniformTensorAddressMachine.address,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,max_left_comm,max_comm]

theorem address_peak_bound (P Q j t B : ℕ) (positive : 0<P)
    (hj : j<P*Q) (ht : t<2) (extent : P*2*Q≤B) (two : 2≤B) :
    addressPeak P j t ≤ B := by
  obtain ⟨hmod,hdiv,hdoubled,hdigit,hscaled,haddr⟩ :=
    UniformTensorAddressMachine.intermediate_bounds P 2 Q j t B positive hj ht extent
  unfold addressPeak
  simp only [max_le_iff]
  exact ⟨⟨hmod,⟨⟨by omega,⟨two,⟨hdiv,hdoubled⟩⟩⟩,⟨hdigit,hscaled⟩⟩⟩,haddr⟩

theorem read_run (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) (j t : ℕ) :
    run (read t) ((M,(P,v)),j) =
      ⟨v.look (UniformTensorAddressMachine.address P 2 j t) (0,(0,0)),
        45,addressPeak P j t,True⟩ := by
  change (((run oldTape ((M,(P,v)),j)).pass (fun y =>
    (run (address t) ((M,(P,v)),j)).pass (fun z => Bill.one (y,z)))).pass
    (fun z => Atom.run .look z)).pay 1 0 = _
  have old : run oldTape ((M,(P,v)),j) = Bill.mk v 5 0 True := by
    simp [oldTape,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [old,address_run]
  simp [Bill.pass,Bill.pay,Bill.one,Atom.run,Ty.blank]

theorem cell_run (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) (j : ℕ) :
    run cell ((M,(P,v)),j) =
      ⟨(v.look (UniformTensorAddressMachine.address P 2 j 0) (0,(0,0)),
        v.look (UniformTensorAddressMachine.address P 2 j 1) (0,(0,0))),91,
        max (addressPeak P j 0) (addressPeak P j 1),True⟩ := by
  change ((run (read 0) ((M,(P,v)),j)).pass (fun y =>
    (run (read 1) ((M,(P,v)),j)).pass (fun z => Bill.one (y,z)))) = _
  rw [read_run,read_run]
  simp [Bill.pass,Bill.one]

theorem program_value (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,v))).val = Tape.tab M (fun j =>
      (v.look (UniformTensorAddressMachine.address P 2 j 0) (0,(0,0)),
        v.look (UniformTensorAddressMachine.address P 2 j 1) (0,(0,0)))) := by
  change (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,(P,v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab M) (funext (fun j => congrArg Bill.val (cell_run M P v j)))

theorem program_work (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,v))).work = 95*M+4 := by
  change 1+(Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,(P,v)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((M,(P,v)),j)).work) = (fun _ => 91) := by
    funext j
    exact congrArg Bill.work (cell_run M P v j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (M P : ℕ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,v))).valid := by
  change True ∧ (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,(P,v)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem program_peak (P Q B : ℕ) (v : Tape DFTModelAffine.Tagged.T)
    (positive : 0<P) (extent : P*2*Q≤B) (two : 2≤B) :
    (run program (P*Q,(P,v))).peak ≤ B := by
  change max (max 0 (Bill.tab (P*Q) DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((P*Q,(P,v)),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,zero_max]
  apply max_le
  · have eq : P*2*Q=2*(P*Q) := by ring
    rw [eq] at extent
    omega
  · apply Finset.sup_le
    intro j hj
    rw [cell_run]
    exact max_le (address_peak_bound P Q j 0 B positive (Finset.mem_range.mp hj)
      (by decide) extent two) (address_peak_bound P Q j 1 B positive
        (Finset.mem_range.mp hj) (by decide) extent two)

/-- Exact source address map, exposed as an actual charged fresh-tape program. -/
theorem physical_view {P Q : ℕ} (v : Tape DFTModelAffine.Tagged.T) :
    (run program (P*Q,(P,v))).val = DFTModelBinaryAffine.data (M:=P*Q)
      (fun j t => v.look (UniformTensorAddressMachine.address P 2 j.val t.val) (0,(0,0))) := by
  rw [program_value]
  rfl

end
end ExactFourierCircuits.DFTModelBinaryPacking
