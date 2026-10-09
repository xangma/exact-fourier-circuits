import UniformBinaryCStageMachine
import DFTModelBinaryAffinePair

set_option autoImplicit false

/-!
# Complete binary C stage over affine published banks

One fresh tape contains both outputs for each disjoint source pair. Its cells
retain prepared offsets separately from homogeneous left data. The entry
relation is an explicit representation of the actual source heap; no earlier
bank production, whole compiler, or data-channel injection is presumed.
-/
namespace ExactFourierCircuits.DFTModelBinaryAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier
noncomputable section

abbrev Input := p w (p DFTModelBinaryPair.Coefficients (Ty.a DFTModelBinaryAffinePair.Pair))
abbrev CellInput := p Input w

def coefficients : Prog false CellInput DFTModelBinaryPair.Coefficients :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def oldTape : Prog false CellInput (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def oldPair : Prog false CellInput DFTModelBinaryAffinePair.Pair :=
  .comp (.fork oldTape (.atom .snd)) (.atom .look)
def cell : Prog false CellInput DFTModelBinaryAffinePair.Pair :=
  .comp (.fork coefficients oldPair) DFTModelBinaryAffinePair.program

def program : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .tab (.atom .fst) cell

def data {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T) :
    Tape DFTModelBinaryAffinePair.Pair.T := ⟨M,fun j => (v j 0,v j 1)⟩
def input {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T) : Input.T :=
  (M,((a,b),data v))

def transformed {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T)
    (j : Fin M) (t : Fin 2) : DFTModelAffine.Tagged.T :=
  if t=0 then DFTModelBinaryAffinePair.combine a b (v j 0) (v j 1)
    else DFTModelBinaryAffinePair.combine b a (v j 0) (v j 1)

theorem cell_run (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T) (j : ℕ) :
    run cell ((M,((c,d),v)),j) =
      ⟨DFTModelBinaryAffinePair.result c d (v.look j ((0,(0,0)),(0,(0,0)))).1
        (v.look j ((0,(0,0)),(0,(0,0)))).2,191,
        (v.look j ((0,(0,0)),(0,(0,0)))).1.1+
          (v.look j ((0,(0,0)),(0,(0,0)))).2.1,True⟩ := by
  change ((run (.fork coefficients oldPair) ((M,((c,d),v)),j)).pass
    (fun z => run DFTModelBinaryAffinePair.program z)).pay 1 0 = _
  have h : run (.fork coefficients oldPair) ((M,((c,d),v)),j) =
      Bill.mk ((c,d),v.look j ((0,(0,0)),(0,(0,0)))) 15 0 True := by
    simp [coefficients,oldPair,oldTape,run,Code.run,Atom.run,
      Bill.pass,Bill.pay,Bill.one,Ty.blank]
  rw [h]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelBinaryAffinePair.program_run]
  simp

theorem program_value (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,((c,d),v))).val = Tape.tab M (fun j =>
      DFTModelBinaryAffinePair.result c d (v.look j ((0,(0,0)),(0,(0,0)))).1
        (v.look j ((0,(0,0)),(0,(0,0)))).2) := by
  change (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab M) (funext (fun j => congrArg Bill.val (cell_run M c d v j)))

theorem program_work (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,((c,d),v))).work = 195*M+4 := by
  change 1+(Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((M,((c,d),v)),j)).work) = (fun _ => 191) := by
    funext j
    exact congrArg Bill.work (cell_run M c d v j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,((c,d),v))).valid := by
  change True ∧ (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem input_value {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T) :
    (run program (input v)).val = data (transformed v) := by
  rw [input,program_value]
  unfold data
  dsimp only [Tape.tab,Tape.len]
  congr 1
  funext j
  simp [Tape.look,j.isLt,DFTModelBinaryAffinePair.result,transformed]

theorem input_peak {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T)
    (z : Fin M → Fin 2 → Scalar)
    (represented : ∀ j t,DFTModelAffine.Represents (v j t) (z j t)) :
    (run program (input v)).peak ≤ max M 2 := by
  change max (max 0 (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j => run cell ((M,((a,b),data v)),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,zero_max]
  apply max_le (le_max_left _ _)
  apply Finset.sup_le
  intro j hj
  have lt : j < M := Finset.mem_range.mp hj
  rw [cell_run]
  change ((data v).look j ((0,(0,0)),(0,(0,0)))).1.1+
    ((data v).look j ((0,(0,0)),(0,(0,0)))).2.1 ≤ max M 2
  simp only [data,Tape.look,lt,↓reduceDIte]
  exact Nat.le_trans (DFTModelBinaryAffinePair.represented_peak
    (v ⟨j,lt⟩ 0) (v ⟨j,lt⟩ 1) (z ⟨j,lt⟩ 0) (z ⟨j,lt⟩ 1)
    (represented ⟨j,lt⟩ 0) (represented ⟨j,lt⟩ 1)) (le_max_right _ _)

theorem transformed_represents {P Q : ℕ}
    (v : Fin (P*Q) → Fin 2 → DFTModelAffine.Tagged.T)
    (z : Fin (P*Q) → Fin 2 → Scalar)
    (represented : ∀ j t,DFTModelAffine.Represents (v j t) (z j t))
    (j : Fin (P*Q)) (t : Fin 2) :
    DFTModelAffine.Represents (transformed v j t)
      (UniformBinaryCStageMachine.transformed z j t) := by
  fin_cases t <;> simp only [transformed,UniformBinaryCStageMachine.transformed,
    ↓reduceIte,Fin.zero_eta,Fin.isValue]
  · exact DFTModelBinaryAffinePair.combine_represents a b _ _ _ _
      (represented j 0) (represented j 1)
  · exact DFTModelBinaryAffinePair.combine_represents b a _ _ _ _
      (represented j 0) (represented j 1)

theorem work_preserved {M : ℕ} (v : Fin M → Fin 2 → DFTModelAffine.Tagged.T) :
    (run program (input v)).work ≤ 8*(25*M+6) := by
  rw [input,program_work]
  omega

def Represents (P A Q : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) (s : State) : Prop :=
  v.len = P*Q ∧ ∀ j : Fin (P*Q), ∀ t : Fin 2, ∃ z,
    s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=some z ∧
      DFTModelAffine.Represents
        (if t=0 then (v.look j.val ((0,(0,0)),(0,(0,0)))).1
          else (v.look j.val ((0,(0,0)),(0,(0,0)))).2) z

/-- An actual full source stage, with no homogeneous injection of prepared data. -/
theorem actual_execution {n B P A Q : ℕ} (x : Fin n → ℂ)
    (z : Fin (P*Q) → Fin 2 → Scalar)
    (v : Fin (P*Q) → Fin 2 → DFTModelAffine.Tagged.T) (s : State)
    (represented : ∀ j t,DFTModelAffine.Represents (v j t) (z j t))
    (pc : s.pc=0) (stride : s.natReg 2800=P) (base : s.natReg 2801=A)
    (count : s.natReg 2802=Q) (positive : 0<P) (separate : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (source : ∀ j t,s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=some (z j t))
    (wb : WordBound B s) (code : 30≤B) (extent : A+P*2*Q≤B) :
    ∃ u, BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(P*Q)+6) u ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s u ∧
      UniformBinaryCStageMachine.Constants u ∧
      Represents P A Q (run program (input v)).val u ∧
      (run program (input v)).valid ∧
      (run program (input v)).work ≤ 8*(25*(P*Q)+6) ∧
      (run program (input v)).peak ≤ B := by
  obtain ⟨u,execution,values,frame⟩ := UniformBinaryCStageMachine.execution n B x P A Q z s
    pc stride base count positive separate constants source wb code extent
  refine ⟨u,execution,frame,frame.constants separate constants,?_,
    program_valid _ _ _ _,work_preserved v,?_⟩
  · rw [input_value]
    refine ⟨rfl,?_⟩
    intro j t
    refine ⟨UniformBinaryCStageMachine.transformed z j t,values j t,?_⟩
    have h := transformed_represents v z represented j t
    fin_cases t <;> simpa [data,Tape.look,j.isLt] using h
  · have h : P*Q ≤ B := by
      have eq : P*2*Q=2*(P*Q) := by ring
      rw [eq] at extent
      omega
    exact (input_peak v z represented).trans (max_le h (by omega))

end
end ExactFourierCircuits.DFTModelBinaryAffine
