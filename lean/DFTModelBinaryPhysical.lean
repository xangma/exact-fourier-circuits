import DFTModelBinaryPacking
import DFTModelBinaryCoefficients

set_option autoImplicit false

/-!
# Actual binary C stage starting from its physical readonly bank

The packing permutation and the affine butterfly are both charged upstream
programs. Their composition is linear in the bank volume and introduces no
new root, field atom, or mutable-tape primitive. Output uses the explicit
pair-major address view; restoring another layout is a separate phase.
-/
namespace ExactFourierCircuits.DFTModelBinaryPhysical
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier
noncomputable section

abbrev Input := p w (p w (p DFTModelBinaryPair.Coefficients (Ty.a DFTModelAffine.Tagged)))

def coefficients : Prog false Input DFTModelBinaryPair.Coefficients :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def packingInput : Prog false Input DFTModelBinaryPacking.Input :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
def packed : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .comp packingInput DFTModelBinaryPacking.program
def ready : Prog false Input DFTModelBinaryAffine.Input :=
  .fork (.atom .fst) (.fork coefficients packed)
def program : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .comp ready DFTModelBinaryAffine.program

def view (P Q : ℕ) (v : Tape DFTModelAffine.Tagged.T)
    (j : Fin (P*Q)) (t : Fin 2) : DFTModelAffine.Tagged.T :=
  v.look (UniformTensorAddressMachine.address P 2 j.val t.val) (0,(0,0))

theorem packingInput_run (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    run packingInput (M,(P,((c,d),v))) = ⟨(M,(P,v)),11,0,True⟩ := by
  simp [packingInput,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem ready_run (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    run ready (M,(P,((c,d),v))) =
      ⟨(M,((c,d),(run DFTModelBinaryPacking.program (M,(P,v))).val)),
        95*M+24,(run DFTModelBinaryPacking.program (M,(P,v))).peak,True⟩ := by
  have pin := packingInput_run M P c d v
  have work := DFTModelBinaryPacking.program_work M P v
  have valid := DFTModelBinaryPacking.program_valid M P v
  change ((Bill.one M).pass (fun y =>
    (run (.fork coefficients packed) (M,(P,((c,d),v)))).pass
      (fun z => Bill.one (y,z)))) = _
  have cr : run coefficients (M,(P,((c,d),v))) = Bill.mk (c,d) 5 0 True := by
    simp [coefficients,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  have pr : run packed (M,(P,((c,d),v))) =
      ((run packingInput (M,(P,((c,d),v)))).pass
        (fun z => run DFTModelBinaryPacking.program z)).pay 1 0 := rfl
  change ((Bill.one M).pass (fun y =>
    ((run coefficients (M,(P,((c,d),v)))).pass (fun q =>
      (run packed (M,(P,((c,d),v)))).pass (fun z => Bill.one (q,z)))).pass
        (fun z => Bill.one (y,z)))) = _
  rw [cr,pr,pin]
  simp [Bill.pass,Bill.pay,Bill.one,work,valid]
  omega

theorem program_value (P Q : ℕ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (P*Q,(P,((a,b),v)))).val =
      DFTModelBinaryAffine.data (DFTModelBinaryAffine.transformed (view P Q v)) := by
  change (((run ready (P*Q,(P,((a,b),v)))).pass
    (fun z => run DFTModelBinaryAffine.program z)).pay 1 0).val = _
  rw [ready_run]
  change (run DFTModelBinaryAffine.program
    (P*Q,((a,b),(run DFTModelBinaryPacking.program (P*Q,(P,v))).val))).val = _
  rw [DFTModelBinaryPacking.physical_view]
  exact DFTModelBinaryAffine.input_value (view P Q v)

theorem program_work (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,((c,d),v)))).work = 290*M+29 := by
  change (((run ready (M,(P,((c,d),v)))).pass
    (fun z => run DFTModelBinaryAffine.program z)).pay 1 0).work = _
  rw [ready_run]
  change 95*M+24+(run DFTModelBinaryAffine.program
    (M,((c,d),(run DFTModelBinaryPacking.program (M,(P,v))).val))).work+1 = _
  rw [DFTModelBinaryAffine.program_work]
  omega

theorem program_valid (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,((c,d),v)))).valid := by
  change (((run ready (M,(P,((c,d),v)))).pass
    (fun z => run DFTModelBinaryAffine.program z)).pay 1 0).valid
  rw [ready_run]
  exact ⟨trivial,DFTModelBinaryAffine.program_valid _ _ _ _⟩

theorem program_peak (P Q B : ℕ) (v : Tape DFTModelAffine.Tagged.T)
    (z : Fin (P*Q) → Fin 2 → Scalar)
    (represented : ∀ j t,DFTModelAffine.Represents (view P Q v j t) (z j t))
    (positive : 0<P) (extent : P*2*Q≤B) (two : 2≤B) :
    (run program (P*Q,(P,((a,b),v)))).peak ≤ B := by
  change (((run ready (P*Q,(P,((a,b),v)))).pass
    (fun z => run DFTModelBinaryAffine.program z)).pay 1 0).peak ≤ _
  rw [ready_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  apply max_le (DFTModelBinaryPacking.program_peak P Q B v positive extent two)
  rw [DFTModelBinaryPacking.physical_view]
  have h := DFTModelBinaryAffine.input_peak (view P Q v) z represented
  apply Nat.le_trans h
  apply max_le _ two
  have eq : P*2*Q=2*(P*Q) := by ring
  rw [eq] at extent
  omega

/-- Physical input is represented pointwise; the target itself computes the
pair permutation. Output and source execution are derived, not assumed. -/
theorem actual_execution {n B P A Q : ℕ} (x : Fin n → ℂ)
    (z : Fin (P*2*Q) → Scalar) (v : Tape DFTModelAffine.Tagged.T) (s : State)
    (represented : ∀ k : Fin (P*2*Q),DFTModelAffine.Represents
      (v.look k.val (0,(0,0))) (z k))
    (source : ∀ k : Fin (P*2*Q),s.scalarHeap (A+k.val)=some (z k))
    (pc : s.pc=0) (stride : s.natReg 2800=P) (base : s.natReg 2801=A)
    (count : s.natReg 2802=Q) (positive : 0<P) (separate : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (wb : WordBound B s) (code : 30≤B) (extent : A+P*2*Q≤B) :
    ∃ u, BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(P*Q)+6) u ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s u ∧
      UniformBinaryCStageMachine.Constants u ∧
      DFTModelBinaryAffine.Represents P A Q
        (run program (P*Q,(P,((a,b),v)))).val u ∧
      (run program (P*Q,(P,((a,b),v)))).valid ∧
      (run program (P*Q,(P,((a,b),v)))).work ≤ 12*(25*(P*Q)+6) ∧
      (run program (P*Q,(P,((a,b),v)))).peak ≤ B := by
  let old : Fin (P*Q) → Fin 2 → Scalar := fun j t =>
    z (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
  have rep : ∀ j t,DFTModelAffine.Represents (view P Q v j t) (old j t) := by
    intro j t
    exact represented (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
  have src : ∀ j t,s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=
      some (old j t) := by
    intro j t
    exact source (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
  obtain ⟨u,execution,frame,constants,result,_,_,_⟩ :=
    DFTModelBinaryAffine.actual_execution x old (view P Q v) s rep pc stride base count
      positive separate constants src wb code extent
  refine ⟨u,execution,frame,constants,?_,program_valid _ _ _ _ _,?_,?_⟩
  · rw [program_value]
    rw [DFTModelBinaryAffine.input_value] at result
    exact result
  · rw [program_work]
    omega
  · exact program_peak P Q B v old rep positive (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelBinaryPhysical
