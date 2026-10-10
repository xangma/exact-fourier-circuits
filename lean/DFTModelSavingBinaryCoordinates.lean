import DFTModelRecursiveBinary
import DFTModelRecursiveScalarSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformBinaryTensorCoordinates
noncomputable section

def flatten {R V : ℕ} (f : Fin R → Fin V → Scalar) (a : Fin (R*V)) : Scalar :=
  let ij := (finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm a
  f ij.1 ij.2

theorem flatten_address {R V : ℕ} (f : Fin R → Fin V → Scalar) (r : Fin R) (z : Fin V)
    (h : r.val*V+z.val<R*V) : flatten f ⟨r.val*V+z.val,h⟩=f r z := by
  have index : (⟨r.val*V+z.val,h⟩ : Fin (R*V))=finProdFinEquiv (r,z) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [index,flatten,Equiv.symm_apply_apply]

theorem paired_flatten {R V : ℕ} (f f0 : Fin R → Fin V → Scalar) (a : Fin (R*V)) :
    (paired f f0).look a.val Tagged.blank=encodePaired (flatten f a) (flatten f0 a) := by
  exact Tape.look_of_lt _ _ a.isLt

theorem address_role (P Q r j t : ℕ) (positive : 0<P) :
    UniformTensorAddressMachine.address P 2 (r*(P*Q)+j) t=
      r*(P*2*Q)+UniformTensorAddressMachine.address P 2 j t := by
  have h : r*(P*Q)+j=j+(r*Q)*P := by ring
  rw [UniformTensorAddressMachine.address,h,Nat.add_mul_mod_self_right,
    Nat.add_mul_div_right _ _ positive]
  unfold UniformTensorAddressMachine.address
  ring

theorem global_volume (R k : ℕ) (i : Fin k) :
    2^i.val*2*(R*2^(k-(i.val+1)))=R*2^k := by
  rw [show 2^i.val*2*(R*2^(k-(i.val+1)))=R*(2^i.val*2*2^(k-(i.val+1))) by ring,
    axis_volume]

theorem axis_fiber (k : ℕ) (i : Fin k) (f : Fin (2^k) → Scalar)
    (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2) :
    axisAction k i f (fiber k i (j,t))=
      UniformBinaryCStageMachine.transformed (fun a b => f (fiber k i (a,b))) j t := by
  rw [UniformBinaryCStageMachine.transformed_C]
  simp only [axisAction,axisMatrix_fiber,fiber_update]

/-- Enlarging the upper-axis count by the number of roles preserves each
physical role slice, with the same least-axis-first integer address. -/
theorem fiber_role {R k : ℕ} (i : Fin k) (r : Fin R)
    (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2)
    (h : r.val*(2^i.val*2^(k-(i.val+1)))+j.val<2^i.val*(R*2^(k-(i.val+1)))) :
    (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 (R*2^(k-(i.val+1)))
      (⟨r.val*(2^i.val*2^(k-(i.val+1)))+j.val,h⟩,t)).val=
      r.val*2^k+(fiber k i (j,t)).val := by
  rw [UniformTensorAddressMachine.fiberEquiv_address,address_role _ _ _ _ _ (by positivity),
    axis_volume,fiber_address]

theorem role_pair_bound {R k : ℕ} (i : Fin k) (r : Fin R)
    (j : Fin (2^i.val*2^(k-(i.val+1)))) :
    r.val*(2^i.val*2^(k-(i.val+1)))+j.val<2^i.val*(R*2^(k-(i.val+1))) := by
  have h := Nat.mul_le_mul_right (2^i.val*2^(k-(i.val+1))) (show r.val+1≤R by omega)
  have hj:=j.isLt
  nlinarith

end
end ExactFourierCircuits.DFTModelSavingBinary
