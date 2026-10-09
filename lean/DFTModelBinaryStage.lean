import DFTModelBinaryUnpacking

set_option autoImplicit false

/-!
# Closed physical-bank translation of the complete actual binary C stage

Three linear fresh-tape phases gather disjoint pairs, apply the affine C
butterflies, and restore physical order. Every output uses readonly published
input tapes. No source store triggers a whole-bank copy. This is one actual
stage compiler primitive, not the complete uniform-program compiler.
-/
namespace ExactFourierCircuits.DFTModelBinaryStage
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier
noncomputable section

attribute [local irreducible] DFTModelBinaryPhysical.program

abbrev Input := DFTModelBinaryPhysical.Input

def package (f : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair)) :
    Prog false Input DFTModelBinaryUnpacking.Input :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst)) f)
def ready : Prog false Input DFTModelBinaryUnpacking.Input :=
  package DFTModelBinaryPhysical.program
def program : Prog false Input (Ty.a DFTModelAffine.Tagged) :=
  .comp ready DFTModelBinaryUnpacking.program

theorem package_run (f : Prog false Input (Ty.a DFTModelBinaryAffinePair.Pair))
    (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    run (package f) (M,(P,((c,d),v))) =
      ⟨(M,(P,(run f (M,(P,((c,d),v)))).val)),
        (run f (M,(P,((c,d),v)))).work+6,
        (run f (M,(P,((c,d),v)))).peak,(run f (M,(P,((c,d),v)))).valid⟩ := by
  change ((Bill.one M).pass (fun y =>
    ((run (.comp (.atom .snd) (.atom .fst) : Prog false Input w)
      (M,(P,((c,d),v)))).pass (fun q =>
        (run f (M,(P,((c,d),v)))).pass
          (fun z => Bill.one (q,z)))).pass (fun z => Bill.one (y,z)))) = _
  have hp : run (.comp (.atom .snd) (.atom .fst) : Prog false Input w)
      (M,(P,((c,d),v))) = Bill.mk P 3 0 True := by
    simp [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [hp]
  simp [Bill.pass,Bill.one]
  omega

theorem ready_run (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    run ready (M,(P,((c,d),v))) =
      ⟨(M,(P,(run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).val)),
        290*M+35,(run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).peak,True⟩ := by
  rw [ready,package_run,DFTModelBinaryPhysical.program_work]
  simp
  exact DFTModelBinaryPhysical.program_valid M P c d v

/-- Keep a compiled component abstract while evaluating its surrounding code. -/
theorem comp_run {s t u : Ty} (f : Prog false s t) (g : Prog false t u) (x : s.T) :
    run (.comp f g) x = ((run f x).pass (fun y => run g y)).pay 1 0 := rfl

theorem program_value (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,((c,d),v)))).val =
      (run DFTModelBinaryUnpacking.program
        (M,(P,(run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).val))).val := by
  rw [program,comp_run,ready_run]
  rfl

theorem program_work (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,((c,d),v)))).work = 420*M+44 := by
  rw [program,comp_run,ready_run]
  change 290*M+35+(run DFTModelBinaryUnpacking.program
    (M,(P,(run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).val))).work+1 = _
  rw [DFTModelBinaryUnpacking.program_work]
  omega

theorem program_valid (M P : ℕ) (c d : ℂ) (v : Tape DFTModelAffine.Tagged.T) :
    (run program (M,(P,((c,d),v)))).valid := by
  rw [program,comp_run,ready_run]
  exact ⟨trivial,DFTModelBinaryUnpacking.program_valid _ _ _⟩

theorem program_peak (P Q B : ℕ) (v : Tape DFTModelAffine.Tagged.T)
    (z : Fin (P*Q) → Fin 2 → Scalar)
    (represented : ∀ j t,DFTModelAffine.Represents (DFTModelBinaryPhysical.view P Q v j t) (z j t))
    (positive : 0<P) (extent : P*2*Q≤B) (two : 2≤B) :
    (run program (P*Q,(P,((a,b),v)))).peak≤B := by
  rw [program,comp_run,ready_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  apply max_le (DFTModelBinaryPhysical.program_peak P Q B v z represented positive extent two)
  apply DFTModelBinaryUnpacking.program_peak _ _ _ _ _ two
  convert extent using 1; ring

def Represents (L A : ℕ) (v : Tape DFTModelAffine.Tagged.T) (s : State) : Prop :=
  v.len=L ∧ ∀ k : Fin L, ∃ z,
    s.scalarHeap (A+k.val)=some z ∧ DFTModelAffine.Represents (v.look k.val (0,(0,0))) z

/-- Full physical input/output correspondence to the genuine thirty-instruction
source stage, with affine offsets, tags, prepared constants and charged bounds. -/
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
      Represents (P*2*Q) A (run program (P*Q,(P,((a,b),v)))).val u ∧
      (run program (P*Q,(P,((a,b),v)))).valid ∧
      (run program (P*Q,(P,((a,b),v)))).work ≤ 17*(25*(P*Q)+6) ∧
      (run program (P*Q,(P,((a,b),v)))).peak≤B := by
  obtain ⟨u,execution,frame,constants,pairs,_,_,_⟩ :=
    DFTModelBinaryPhysical.actual_execution x z v s represented source pc stride base count
      positive separate constants wb code extent
  refine ⟨u,execution,frame,constants,?_,program_valid _ _ _ _ _,?_,?_⟩
  · rw [program_value]
    refine ⟨?_,?_⟩
    · rw [DFTModelBinaryUnpacking.program_value]
      change P*Q*2=P*2*Q
      ring
    · intro k
      let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
      obtain ⟨w,hw,rep⟩ := pairs.2 jt.1 jt.2
      refine ⟨w,?_,?_⟩
      · have eq : UniformBinaryCStageMachine.coordinate P A Q jt.1 jt.2=A+k.val := by
          change A+UniformTensorAddressMachine.address P 2 jt.1.val jt.2.val=A+k.val
          rw [← UniformTensorAddressMachine.fiberEquiv_address]
          exact congrArg (fun a : Fin (P*2*Q) => A+a.val)
            ((UniformTensorAddressMachine.fiberEquiv P 2 Q).apply_symm_apply k)
        rw [eq] at hw
        exact hw
      · rw [DFTModelBinaryUnpacking.inverse_lookup]
        exact rep
  · rw [program_work]
    omega
  · let old : Fin (P*Q) → Fin 2 → Scalar := fun j t =>
      z (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
    have rep : ∀ j t,DFTModelAffine.Represents (DFTModelBinaryPhysical.view P Q v j t) (old j t) := by
      intro j t
      exact represented (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
    exact program_peak P Q B v old rep positive (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelBinaryStage
