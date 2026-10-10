import DFTModelSavingBinaryStage

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformBinaryTensorCoordinates
noncomputable section
attribute [local irreducible] DFTModelRecursiveBinary.program DFTModelRecursiveBinary.body

def partialAxes {R : ℕ} (k j : ℕ) (f : Fin R → Fin (2^k) → Scalar) : Fin R → Fin (2^k) → Scalar :=
  fun r => applyAxes k ((List.finRange k).take j) (f r)

theorem partialAxes_succ {R k j : ℕ} (hj : j<k) (f : Fin R → Fin (2^k) → Scalar) :
    partialAxes k (j+1) f=fun r => axisAction k ⟨j,hj⟩ (partialAxes k j f r) := by
  funext r
  unfold partialAxes
  rw [List.take_succ_eq_append_getElem (show j<(List.finRange k).length by simpa using hj)]
  simp [applyAxes,List.foldl_append]

theorem states_paired {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (j : ℕ) (cap : j≤k) :
    DFTModelRecursiveBinary.states Complex.I (paired f f0) j=
      (2^j,paired (partialAxes k j f) (partialAxes k j f0)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj : j<k := by omega
    change (2*(DFTModelRecursiveBinary.states Complex.I (paired f f0) j).1,
      DFTModelRecursiveBinary.next Complex.I
        (DFTModelRecursiveBinary.states Complex.I (paired f f0) j).1
        (DFTModelRecursiveBinary.states Complex.I (paired f f0) j).2)=_
    rw [ih (by omega)]
    change (2*2^j,DFTModelRecursiveBinary.next Complex.I (2^j)
      (paired (partialAxes k j f) (partialAxes k j f0)))=_
    rw [next_paired (⟨j,hj⟩ : Fin k),partialAxes_succ hj f,partialAxes_succ hj f0,Nat.pow_succ,Nat.mul_comm]

/-- Exact flags and zero-source offsets for the complete ordinary tensor loop,
including runtime k=0 and every role in the physical role-major bank. -/
theorem program_paired {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).val=
      paired (fun r => applyAxes k (List.finRange k) (f r))
        (fun r => applyAxes k (List.finRange k) (f0 r)) := by
  rw [DFTModelRecursiveBinary.program_value,states_paired f f0 k (le_refl _)]
  change paired (fun r => applyAxes k ((List.finRange k).take k) (f r))
    (fun r => applyAxes k ((List.finRange k).take k) (f0 r))=_
  rw [show (List.finRange k).take k=List.finRange k from by simp]

theorem program_lookup {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (r : Fin R) (z : Fin (2^k)) :
    (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).val.look
      (r.val*2^k+z.val) Tagged.blank=
      encodePaired (applyAxes k (List.finRange k) (f r) z)
        (applyAxes k (List.finRange k) (f0 r) z) := by
  rw [program_paired]
  exact paired_lookup _ _ r z

theorem program_tensor_values {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (r : Fin R) (z : Fin (2^k)) :
    let cell := (run DFTModelRecursiveBinary.program ((k,Complex.I),paired f f0)).val.look
      (r.val*2^k+z.val) Tagged.blank
    cell.2.1=(physicalMatrix k).mulVec (fun y => (f0 r y).value) z ∧
    cell.2.1+cell.2.2=(physicalMatrix k).mulVec (fun y => (f r y).value) z := by
  dsimp only
  rw [program_lookup]
  constructor
  · exact congrFun (applyAxes_tensor k (f0 r)) z
  · change (applyAxes k (List.finRange k) (f0 r) z).value+
      ((applyAxes k (List.finRange k) (f r) z).value-
      (applyAxes k (List.finRange k) (f0 r) z).value)=_
    calc
      _=(applyAxes k (List.finRange k) (f r) z).value := by ring
      _=_ := congrFun (applyAxes_tensor k (f r)) z

end
end ExactFourierCircuits.DFTModelSavingBinary
