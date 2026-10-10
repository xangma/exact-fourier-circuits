import DFTModelSavingBinaryCoordinates

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformBinaryTensorCoordinates
noncomputable section

attribute [local irreducible] DFTModelBinaryStage.program DFTModelRecursiveBinary.body
  DFTModelRecursiveBinary.program

theorem flatten_fiber_role {R k : ℕ} (f : Fin R → Fin (2^k) → Scalar)
    (i : Fin k) (r : Fin R) (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2) :
    flatten f ((finCongr (global_volume R k i))
      (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 (R*2^(k-(i.val+1)))
        (⟨r.val*(2^i.val*2^(k-(i.val+1)))+j.val,role_pair_bound i r j⟩,t)))=
      f r (fiber k i (j,t)) := by
  have h : (finCongr (global_volume R k i))
      (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 (R*2^(k-(i.val+1)))
        (⟨r.val*(2^i.val*2^(k-(i.val+1)))+j.val,role_pair_bound i r j⟩,t))=
      finProdFinEquiv (r,fiber k i (j,t)) := by
    apply Fin.ext
    change (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 (R*2^(k-(i.val+1)))
      (⟨r.val*(2^i.val*2^(k-(i.val+1)))+j.val,role_pair_bound i r j⟩,t)).val=_
    simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using fiber_role i r j t (role_pair_bound i r j)
  rw [h,flatten,Equiv.symm_apply_apply]

theorem next_lookup {R k : ℕ} (i : Fin k)
    (f f0 : Fin R → Fin (2^k) → Scalar) (r : Fin R) (z : Fin (2^k)) :
    (DFTModelRecursiveBinary.next Complex.I (2^i.val) (paired f f0)).look
      (r.val*2^k+z.val) Tagged.blank=
      encodePaired (axisAction k i (f r) z) (axisAction k i (f0 r) z) := by
  obtain ⟨⟨j,t⟩,rfl⟩ := (fiber k i).surjective z
  let Q := R*2^(k-(i.val+1))
  let cast := finCongr (global_volume R k i)
  let g : Fin (2^i.val*2*Q) → Scalar := fun a => flatten f (cast a)
  let g0 : Fin (2^i.val*2*Q) → Scalar := fun a => flatten f0 (cast a)
  let J : Fin (2^i.val*Q) :=
    ⟨r.val*(2^i.val*2^(k-(i.val+1)))+j.val,role_pair_bound i r j⟩
  have encoded : ∀a : Fin (2^i.val*2*Q),
      (paired f f0).look a.val Tagged.blank=encodePaired (g a) (g0 a) := by
    intro a
    exact paired_flatten f f0 (cast a)
  have divide : (paired f f0).len/2=2^i.val*Q := by
    change (R*2^k)/2=_
    rw [←global_volume R k i]
    change (2^i.val*2*Q)/2=_
    rw [show 2^i.val*2*Q=(2^i.val*Q)*2 by ring,Nat.mul_div_cancel _ (by omega)]
  have h := DFTModelBinaryBaseline.program_lookup (paired f f0) g g0 encoded
    (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 Q (J,t))
  have view : ∀u : Fin 2,DFTModelBinaryBaseline.fibers g J u=f r (fiber k i (j,u)) := by
    intro u
    exact flatten_fiber_role f i r j u
  have view0 : ∀u : Fin 2,DFTModelBinaryBaseline.fibers g0 J u=f0 r (fiber k i (j,u)) := by
    intro u
    exact flatten_fiber_role f0 i r j u
  have addr : (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 Q (J,t)).val=
      r.val*2^k+(fiber k i (j,t)).val := fiber_role i r j t (role_pair_bound i r j)
  simp only [Equiv.symm_apply_apply,addr] at h
  unfold DFTModelRecursiveBinary.next
  rw [divide]
  change (run DFTModelBinaryStage.program (2^i.val*Q,(2^i.val,
    ((ExactFourierCircuits.a,ExactFourierCircuits.b),paired f f0)))).val.look _ Tagged.blank=_
  rw [show Tagged.blank=(0,(0,0)) from rfl,h,axis_fiber,axis_fiber]
  fin_cases t <;> simp [UniformBinaryCStageMachine.transformed,view,view0]

/-- A full-bank physical stage acts on one bit in every role slice. -/
theorem next_paired {R k : ℕ} (i : Fin k) (f f0 : Fin R → Fin (2^k) → Scalar) :
    DFTModelRecursiveBinary.next Complex.I (2^i.val) (paired f f0)=
      paired (fun r => axisAction k i (f r)) (fun r => axisAction k i (f0 r)) := by
  have even : 2*((R*2^k)/2)=R*2^k := by
    rw [←global_volume R k i,show 2^i.val*2*(R*2^(k-(i.val+1)))=
      (2^i.val*(R*2^(k-(i.val+1))))*2 by ring,Nat.mul_div_cancel _ (by omega)]
    omega
  have len : (DFTModelRecursiveBinary.next Complex.I (2^i.val) (paired f f0)).len=R*2^k := by
    rw [DFTModelRecursiveBinary.next_len]
    exact even
  cases he : DFTModelRecursiveBinary.next Complex.I (2^i.val) (paired f f0) with
  | mk L bank =>
    rw [he] at len
    change L=R*2^k at len
    subst L
    congr 1
    funext a
    let rz := (finProdFinEquiv : Fin R × Fin (2^k) ≃ Fin (R*2^k)).symm a
    have address : rz.1.val*2^k+rz.2.val=a.val := by
      have h := congrArg Fin.val ((finProdFinEquiv : Fin R × Fin (2^k) ≃ Fin (R*2^k)).apply_symm_apply a)
      simpa [rz,finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h
    have h := next_lookup i f f0 rz.1 rz.2
    rw [he,address,Tape.look_of_lt _ _ a.isLt] at h
    exact h

end
end ExactFourierCircuits.DFTModelSavingBinary
