import DFTModelBinaryStage
import DFTModelAffinePaired

set_option autoImplicit false

/-!
# The actual physical binary stage preserves its zero-input baseline

The entry invariant identifies a published Tagged tape with the exact affine
encoding of two matching source banks. The same single target stage returns
that encoding for the two source output banks. The second source run is a
proof witness, not a second execution of the typed program.
-/
namespace ExactFourierCircuits.DFTModelBinaryBaseline
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier DFTModelAdmissibilityControl
noncomputable section

attribute [local irreducible] DFTModelBinaryStage.program DFTModelBinaryPhysical.program

theorem combine_paired (c d : ℂ) (x y x0 y0 : Scalar) :
    DFTModelBinaryAffinePair.combine c d
      (DFTModelAffine.encodePaired x x0) (DFTModelAffine.encodePaired y y0) =
      DFTModelAffine.encodePaired (UniformPairMachine.combine c d x y)
        (UniformPairMachine.combine c d x0 y0) := by
  apply Prod.ext
  · change DFTModelBinaryAffinePair.flags
      (DFTModelAffine.encodePaired x x0) (DFTModelAffine.encodePaired y y0) =
        DFTModelAffine.flag (x.dependent || y.dependent)
    cases hx : x.dependent <;> cases hy : y.dependent <;>
      simp [DFTModelBinaryAffinePair.flags,DFTModelAffine.encodePaired,
        DFTModelAffine.tagged,DFTModelAffine.flag,hx,hy]
  · apply Prod.ext
    · rfl
    · change c*(x.value-x0.value)+d*(y.value-y0.value) =
        (c*x.value+d*y.value)-(c*x0.value+d*y0.value)
      ring

def fibers {P Q : ℕ} (z : Fin (P*2*Q) → Scalar) : Fin (P*Q) → Fin 2 → Scalar :=
  fun j t => z (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))

theorem transformed_paired {P Q : ℕ} (v : Tape DFTModelAffine.Tagged.T)
    (z z0 : Fin (P*2*Q) → Scalar)
    (encoded : ∀ k : Fin (P*2*Q),v.look k.val (0,(0,0))=
      DFTModelAffine.encodePaired (z k) (z0 k))
    (j : Fin (P*Q)) (t : Fin 2) :
    DFTModelBinaryAffine.transformed (DFTModelBinaryPhysical.view P Q v) j t =
      DFTModelAffine.encodePaired
        (UniformBinaryCStageMachine.transformed (fibers z) j t)
        (UniformBinaryCStageMachine.transformed (fibers z0) j t) := by
  have cell : ∀ u : Fin 2,DFTModelBinaryPhysical.view P Q v j u =
      DFTModelAffine.encodePaired (fibers z j u) (fibers z0 j u) := by
    intro u
    exact encoded (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,u))
  fin_cases t <;>
    simp only [DFTModelBinaryAffine.transformed,UniformBinaryCStageMachine.transformed,
      Fin.isValue,cell]
  · exact combine_paired a b _ _ _ _
  · exact combine_paired b a _ _ _ _

/-- Exact paired result of the already compiled full physical-bank stage. -/
theorem program_lookup {P Q : ℕ} (v : Tape DFTModelAffine.Tagged.T)
    (z z0 : Fin (P*2*Q) → Scalar)
    (encoded : ∀ k : Fin (P*2*Q),v.look k.val (0,(0,0))=
      DFTModelAffine.encodePaired (z k) (z0 k)) (k : Fin (P*2*Q)) :
    (run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).val.look k.val (0,(0,0)) =
      let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
      DFTModelAffine.encodePaired
        (UniformBinaryCStageMachine.transformed (fibers z) jt.1 jt.2)
        (UniformBinaryCStageMachine.transformed (fibers z0) jt.1 jt.2) := by
  rw [DFTModelBinaryStage.program_value,DFTModelBinaryUnpacking.inverse_lookup,
    DFTModelBinaryPhysical.program_value]
  let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
  change (if jt.2=0 then
    ((DFTModelBinaryAffine.data
      (DFTModelBinaryAffine.transformed (DFTModelBinaryPhysical.view P Q v))).look
      jt.1.val ((0,(0,0)),(0,(0,0)))).1 else
    ((DFTModelBinaryAffine.data
      (DFTModelBinaryAffine.transformed (DFTModelBinaryPhysical.view P Q v))).look
      jt.1.val ((0,(0,0)),(0,(0,0)))).2) =
    DFTModelAffine.encodePaired
      (UniformBinaryCStageMachine.transformed (fibers z) jt.1 jt.2)
      (UniformBinaryCStageMachine.transformed (fibers z0) jt.1 jt.2)
  have h := transformed_paired v z z0 encoded jt.1 jt.2
  generalize ht : jt.2=t at h ⊢
  fin_cases t <;> simpa [DFTModelBinaryAffine.data,Tape.look,jt.1.isLt] using h

theorem coordinate_inverse (P A Q : ℕ) (k : Fin (P*2*Q)) :
    let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
    UniformBinaryCStageMachine.coordinate P A Q jt.1 jt.2=A+k.val := by
  change A+UniformTensorAddressMachine.address P 2 _ _=A+k.val
  rw [← UniformTensorAddressMachine.fiberEquiv_address]
  exact congrArg (fun l : Fin (P*2*Q) => A+l.val)
    ((UniformTensorAddressMachine.fiberEquiv P 2 Q).apply_symm_apply k)

/-- Output offsets agree with a genuinely executed zero-input source stage.
All preparation, control, code/word and bank entry premises concern inputs. -/
theorem actual_execution {n B P A Q : ℕ} (x : Fin n → ℂ)
    (z z0 : Fin (P*2*Q) → Scalar) (v : Tape DFTModelAffine.Tagged.T) (s s0 : State)
    (same : StateMatch s s0)
    (encoded : ∀ k : Fin (P*2*Q),v.look k.val (0,(0,0))=
      DFTModelAffine.encodePaired (z k) (z0 k))
    (source : ∀ k : Fin (P*2*Q),s.scalarHeap (A+k.val)=some (z k))
    (baseline : ∀ k : Fin (P*2*Q),s0.scalarHeap (A+k.val)=some (z0 k))
    (pc : s.pc=0) (stride : s.natReg 2800=P) (base : s.natReg 2801=A)
    (count : s.natReg 2802=Q) (positive : 0<P) (separate : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (wb : WordBound B s) (code : 30≤B) (extent : A+P*2*Q≤B) :
    ∃ u u0,
      BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(P*Q)+6) u ∧
      BoundedExecution UniformBinaryCStageMachine.program n (fun _ => 0) B s0 (25*(P*Q)+6) u0 ∧
      StateMatch u u0 ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s u ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s0 u0 ∧
      (∀ k : Fin (P*2*Q),∃ w w0,
        u.scalarHeap (A+k.val)=some w ∧ u0.scalarHeap (A+k.val)=some w0 ∧
        (run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).val.look k.val (0,(0,0))=
          DFTModelAffine.encodePaired w w0 ∧
        ((run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).val.look k.val (0,(0,0))).2.1=
          w0.value) ∧
      (run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).valid ∧
      (run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).work≤17*(25*(P*Q)+6) ∧
      (run DFTModelBinaryStage.program (P*Q,(P,((a,b),v)))).peak≤B := by
  have matchedCells : ∀ k,ScalarMatch (z k) (z0 k) := by
    intro k
    have h := same.scalarHeap (A+k.val)
    rw [source k,baseline k] at h
    cases h with
    | some h => exact h
  have represented : ∀ k,DFTModelAffine.Represents (v.look k.val (0,(0,0))) (z k) := by
    intro k
    rw [encoded]
    exact DFTModelAffine.encodePaired_represents _ _ (matchedCells k)
  have src : ∀ j t,s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=
      some (fibers z j t) := by
    intro j t
    exact source (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
  have src0 : ∀ j t,s0.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=
      some (fibers z0 j t) := by
    intro j t
    exact baseline (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
  have constants0 : UniformBinaryCStageMachine.Constants s0 := by
    constructor
    · obtain ⟨w,hw,hm⟩ := (same.scalarHeap 1).left constants.1
      have he := hm.eq_of_prepared rfl
      rw [← he] at hw
      exact hw
    · obtain ⟨w,hw,hm⟩ := (same.scalarHeap 2).left constants.2
      have he := hm.eq_of_prepared rfl
      rw [← he] at hw
      exact hw
  obtain ⟨u,execution,values,frame⟩ := UniformBinaryCStageMachine.execution n B x P A Q
    (fibers z) s pc stride base count positive separate constants src wb code extent
  obtain ⟨u0,zeroRun,values0,frame0⟩ := UniformBinaryCStageMachine.execution n B (fun _ => 0) P A Q
    (fibers z0) s0 (same.pc.trans pc) (by rw [same.natReg];exact stride)
    (by rw [same.natReg];exact base) (by rw [same.natReg];exact count)
    positive separate constants0 src0 (same.wordBound wb) code extent
  obtain ⟨u0',zeroRun',sameResult⟩ := boundedExecution_match (y:=fun _ => 0) execution same
  have eq : u0'=u0 := (zeroRun'.executes.deterministic zeroRun.executes).2
  subst u0'
  refine ⟨u,u0,execution,zeroRun,sameResult,frame,frame0,?_,
    DFTModelBinaryStage.program_valid _ _ _ _ _,?_,?_⟩
  · intro k
    let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
    have coord : UniformBinaryCStageMachine.coordinate P A Q jt.1 jt.2=A+k.val :=
      coordinate_inverse P A Q k
    refine ⟨UniformBinaryCStageMachine.transformed (fibers z) jt.1 jt.2,
      UniformBinaryCStageMachine.transformed (fibers z0) jt.1 jt.2,?_,?_,?_,?_⟩
    · simpa only [coord] using values jt.1 jt.2
    · simpa only [coord] using values0 jt.1 jt.2
    · exact program_lookup v z z0 encoded k
    · rw [program_lookup v z z0 encoded k]
      rfl
  · rw [DFTModelBinaryStage.program_work]
    omega
  · have rep : ∀ j t,DFTModelAffine.Represents (DFTModelBinaryPhysical.view P Q v j t)
        (fibers z j t) := by
      intro j t
      exact represented (UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t))
    exact DFTModelBinaryStage.program_peak P Q B v (fibers z) rep positive (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelBinaryBaseline
