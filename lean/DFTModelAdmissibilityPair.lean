import DFTModelAdmissibility
import UniformPairMachine

set_option autoImplicit false

/-! A complete admissibility certificate for the literal two-coordinate
kernel used by the actual binary/recursive DFT program. The certificate follows
all eleven actual instructions, not only the kernel's matrix identity. -/
namespace ExactFourierCircuits.DFTModelAdmissibility
open UniformMachine UniformPairMachine
noncomputable section

 theorem product_in_mode {m : Mode} (c : ℂ) {u : Scalar} (h : InMode m u) :
    InMode m (product c u) := mode_scale (a := prepared c) rfl h

 theorem combine_in_mode {m : Mode} (c d : ℂ) {u v : Scalar}
    (hu : InMode m u) (hv : InMode m v) : InMode m (combine c d u v) :=
    mode_add (product_in_mode c hu) (product_in_mode d hv)

/-- Both genuine kernel additions combine slots in one common mode. In the
data mode untainted zero initialization is allowed; in the prepared mode both
inputs and all coefficient arithmetic may be nonzero. -/
theorem pair_admissible {n : ℕ} (x : Fin n → ℂ) (m : Mode) (s : State)
    (c d : ℂ) (u v : Scalar) (ready : Ready c d u v s)
    (hu : InMode m u) (hv : InMode m v) :
    AdmissibleExecution program n x s 11 (finalState s c d u v) := by
  obtain ⟨pc,left,right,diagonal,offDiagonal⟩ := ready
  have first : MixedZero (product c u) (product d v) :=
    mixed_of_mode (product_in_mode c hu) (product_in_mode d hv)
  have second : MixedZero (product d u) (product c v) :=
    mixed_of_mode (product_in_mode d hu) (product_in_mode c hv)
  refine .next (u:=loadedLeft s u) ?_ ?_ (.next (u:=loadedBoth s u v) ?_ ?_
    (.next (u:=productLeft s c u v) ?_ ?_ (.next (u:=productRight s c d u v) ?_ ?_
      (.next (u:=addedLeft s c d u v) ?_ ?_ (.next (u:=productOtherLeft s c d u v) ?_ ?_
        (.next (u:=productOtherRight s c d u v) ?_ ?_ (.next (u:=addedRight s c d u v) ?_ ?_
          (.next (u:=storedLeft s c d u v) ?_ ?_ (.next (u:=finalState s c d u v) ?_ ?_
            (.halt ?_))))))))))
  all_goals simp [Guard,InstructionGuard,FieldGuard,step,program,finalState,storedLeft,
    addedRight,productOtherRight,productOtherLeft,addedLeft,productRight,productLeft,
    loadedBoth,loadedLeft,writeScalar,next,pc,left,right,diagonal,offDiagonal,
    prepared_mul,product_add,first,second]

/-- This is the same concrete, charged and word-bounded run as the existing
kernel execution theorem, now also carrying its local arithmetic certificate. -/
theorem pair_bounded_admissible {n B : ℕ} (x : Fin n → ℂ) (m : Mode) (s : State)
    (c d : ℂ) (u v : Scalar) (ready : Ready c d u v s)
    (hu : InMode m u) (hv : InMode m v) (large : 11 ≤ B) (bound : WordBound B s) :
    BoundedExecution program n x B s 11 (finalState s c d u v) ∧
      AdmissibleExecution program n x s 11 (finalState s c d u v) :=
  ⟨bounded_execution n x B s c d u v ready large bound,
   pair_admissible x m s c d u v ready hu hv⟩

/-- The real kernel keeps both output slots in the same caller mode. -/
theorem pair_output_modes {m : Mode} (s : State) (c d : ℂ) (u v : Scalar)
    (hu : InMode m u) (hv : InMode m v) (distinct : s.natReg 0 ≠ s.natReg 1) :
    ∃ a b, (finalState s c d u v).scalarHeap (s.natReg 0) = some a ∧
      (finalState s c d u v).scalarHeap (s.natReg 1) = some b ∧
      InMode m a ∧ InMode m b := by
  obtain ⟨left,right⟩ := final_values s c d u v distinct
  exact ⟨_,_,left,right,combine_in_mode c d hu hv,combine_in_mode d c hu hv⟩

end
end ExactFourierCircuits.DFTModelAdmissibility
