import DFTModelRecursiveScalar
import UniformNativeScheduleSemantics

set_option autoImplicit false

/-! The concrete scalar emitter implements the actual saving-network shear
record. A single upstream execution returns the exact affine encoding of the
actual and zero-source native record executions. -/
namespace ExactFourierCircuits.DFTModelRecursiveScalarSource
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalar DFTModelRecursiveScalarCore
open DFTModelAdmissibilityControl
open UniformFixedNetworkScheduleMachine (Printed)
noncomputable section

namespace Child
abbrev Present := UniformFixedNetworkShearChildMachine.Present
abbrev values {R V : ℕ} (d s : Fin R) (c : ℂ)
    (f : Fin R → Fin V → Scalar) :=
  UniformFixedNetworkShearChildMachine.shearValues d s c f
end Child

def paired {R V : ℕ} (f f0 : Fin R → Fin V → Scalar) : Tape Tagged.T :=
  ⟨R*V,fun z =>
    let ij := (finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm z
    encodePaired (f ij.1 ij.2) (f0 ij.1 ij.2)⟩

theorem paired_lookup {R V : ℕ} (f f0 : Fin R → Fin V → Scalar) (i : Fin R) (j : Fin V) :
    (paired f f0).look (i.val*V+j.val) Tagged.blank = encodePaired (f i j) (f0 i j) := by
  have index : i.val*V+j.val=(finProdFinEquiv (i,j)).val := by
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [index,Tape.look_of_lt _ _ (finProdFinEquiv (i,j)).isLt]
  change encodePaired
    (f ((finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm (finProdFinEquiv (i,j))).1
      ((finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm (finProdFinEquiv (i,j))).2)
    (f0 ((finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm (finProdFinEquiv (i,j))).1
      ((finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm (finProdFinEquiv (i,j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem result_lookup {R V : ℕ} (d s : Fin R) (c : ℂ) (positive : 0<V)
    (f f0 : Fin R → Fin V → Scalar) (i : Fin R) (j : Fin V) :
    result d.val s.val V c (paired f f0) (i.val*V+j.val) =
      encodePaired (Child.values d s c f i j) (Child.values d s c f0 i j) := by
  have div : (i.val*V+j.val)/V=i.val := by
    rw [Nat.mul_comm i.val V,Nat.add_comm,Nat.add_mul_div_left _ _ positive,
      Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have rem : (i.val*V+j.val)%V=j.val := by
    rw [Nat.mul_comm i.val V,Nat.add_comm,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  simp only [result,div,rem]
  rw [paired_lookup,paired_lookup]
  by_cases h : i=d
  · subst i
    simp only [Child.values,UniformFixedNetworkShearChildMachine.shearValues]
    exact updated_paired c _ _ _ _
  · have hi : i.val≠d.val := fun he => h (Fin.ext he)
    simp only [hi,ite_false,Child.values,UniformFixedNetworkShearChildMachine.shearValues,h]

/-- One native scalar record is one whole-array upstream tab. No supplied
coefficient register, output action, or second typed run is required. -/
theorem program_lookup {R V : ℕ} (d s : Fin R) (c : Fin 5) (positive : 0<V)
    (f f0 : Fin R → Fin V → Scalar) (k : ℕ) (I : ℂ) (i : Fin R) (j : Fin V) :
    (run (program R d.val s.val c) ((k,I),paired f f0)).val.2.look
      (i.val*V+j.val) Tagged.blank =
      encodePaired (Child.values d s (UniformFixedCoefficientCodec.decode c) f i j)
        (Child.values d s (UniformFixedCoefficientCodec.decode c) f0 i j) := by
  rw [program_value]
  have rp : 0<R := by have h:=d.isLt;omega
  have div : (paired f f0).len/R=V := Nat.mul_div_cancel_left V rp
  have h : i.val*V+j.val<(paired f f0).len := by
    simpa [paired,finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  simp only [div,Tape.look,Tape.tab, h, dite_true]
  exact result_lookup d s _ positive f f0 i j

/-- Generic constructor equality avoids reducing the enormous fixed seed. -/
theorem macro_record {r R w : ℕ} (q : ℕ) (e : Fin r ↪ Fin R)
    (d s : Fin r) (ne : d≠s) (c : Fin 5)
    (nz : UniformFixedCoefficientCodec.decode c≠0) :
    UniformFixedNetworkScheduleMachine.macroRecord (n:=w) q e (.shear d s ne c nz) =
      UniformNativeScalarRecordMachine.shearRecord q w (e d) (e s) c := rfl


/-- Concrete native record simulation. The baseline is a second mathematical
source witness; the upstream program is evaluated only once and carries both
channels together. Every entry premise describes original source metadata/data. -/
theorem actual_execution {R : ℕ} (q w k A T B n : ℕ) (x : Fin n → ℂ)
    (d src : Fin R) (ne : d≠src) (c : Fin 5)
    (f f0 : Fin R → Fin (2^k) → Scalar) (s s0 : State) (I : ℂ)
    (same : StateMatch s s0)
    (pc : s.pc=0) (ptr : s.natReg 2850=T) (base : s.natReg 3300=A)
    (native : s.natReg 5300=k)
    (bank : Printed T (UniformNativeScalarRecordMachine.shearRecord q w d src c).data s)
    (data : Child.Present A R (2^k) f s)
    (baseline : Child.Present A R (2^k) f0 s0)
    (wb : WordBound B s) (code : 106≤B) (tableEnd : T+8≤B)
    (width : w+1≤B) (extent : A+R*2^k≤B) :
    ∃ u u0,
      BoundedExecution UniformNativeScalarRecordMachine.scalarProgram n x B s
        (10*2^k+4*k+c.val+62) u ∧
      BoundedExecution UniformNativeScalarRecordMachine.scalarProgram n (fun _ => 0) B s0
        (10*2^k+4*k+c.val+62) u0 ∧
      StateMatch u u0 ∧
      UniformNativeScalarRecordMachine.ScalarFrame
        (UniformFixedNetworkShearChildMachine.roleBase A (2^k) d.val) (2^k) s u ∧
      UniformNativeScalarRecordMachine.ScalarFrame
        (UniformFixedNetworkShearChildMachine.roleBase A (2^k) d.val) (2^k) s0 u0 ∧
      (∀ i : Fin R,∀ j : Fin (2^k),∃ a a0,
        u.scalarHeap (A+i.val*2^k+j.val)=some a ∧
        u0.scalarHeap (A+i.val*2^k+j.val)=some a0 ∧
        (run (program R d.val src.val c) ((k,I),paired f f0)).val.2.look
          (i.val*2^k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run (program R d.val src.val c) ((k,I),paired f f0)).valid ∧
      (run (program R d.val src.val c) ((k,I),paired f f0)).work ≤
        (15*R+1)*(10*2^k+4*k+c.val+62) ∧
      (run (program R d.val src.val c) ((k,I),paired f f0)).peak≤B := by
  obtain ⟨u,run,output,_cursor,frame⟩ :=
    UniformNativeScalarRecordMachine.scalar_execution q w k A T B n x d src ne c f s
      pc ptr base native bank data wb code tableEnd width extent
  have bank0 : Printed T (UniformNativeScalarRecordMachine.shearRecord q w d src c).data s0 := by
    intro j hj; rw [same.natHeap]; exact bank j hj
  obtain ⟨u0,run0,output0,_cursor0,frame0⟩ :=
    UniformNativeScalarRecordMachine.scalar_execution q w k A T B n (fun _ => 0) d src ne c f0 s0
      (same.pc.trans pc) (by rw [same.natReg];exact ptr)
      (by rw [same.natReg];exact base) (by rw [same.natReg];exact native)
      bank0 baseline (same.wordBound wb) code tableEnd width extent
  obtain ⟨u0',run0',matched⟩ := boundedExecution_match (y:=fun _ => 0) run same
  have eq : u0'=u0 := (run0'.executes.deterministic run0.executes).2
  subst u0'
  refine ⟨u,u0,run,run0,matched,frame,frame0,?_,program_valid _ _ _ _ _ _ _,?_,?_⟩
  · intro i j
    refine ⟨_,_,output i j,output0 i j,?_⟩
    exact program_lookup d src c (by positivity) f f0 k I i j
  · have h := program_work_bound R d.val src.val k I c (paired f f0)
    change _≤32+149*(R*2^k) at h
    calc
      _ ≤ 32+149*(R*2^k) := h
      _ ≤ (15*R+1)*(10*2^k+62) := by
        have hmul : 149*(R*2^k)≤150*(R*2^k) := Nat.mul_le_mul_right _ (by omega)
        have hconst : 62≤(15*R+1)*62 := by
          simp
        rw [show (15*R+1)*(10*2^k+62)=150*(R*2^k)+((15*R+1)*62+10*2^k) by ring]
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · apply program_peak_bound R d.val src.val k (2^k) B I c (paired f f0)
    · positivity
    · have h:=d.isLt;omega
    · rfl
    · exact d.isLt
    · exact src.isLt
    · omega

end
end ExactFourierCircuits.DFTModelRecursiveScalarSource
