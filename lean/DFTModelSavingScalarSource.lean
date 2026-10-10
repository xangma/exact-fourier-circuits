import DFTModelSavingScalarBounds

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6 proof, PDF pp.11–12: one scalar record of the fixed saving
network. Runtime field reads and coefficient decoding are charged before one
paired whole-bank shear. Only the original eight record cells are represented;
populated neighbouring cache cells impose no condition on this compact tape. -/
namespace ExactFourierCircuits.DFTModelSavingScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired)
open UniformFixedNetworkScheduleMachine (Printed Record)
noncomputable section

/-- A genuine native106/zero106 pair and a single runtime-decoded typed run.
The input conditions concern original source metadata and original data only. -/
theorem actual_execution {R : ℕ} (q w k A T B n : ℕ) (x : Fin n → ℂ)
    (d src : Fin R) (ne : d≠src) (c : Fin 5)
    (f f0 : Fin R → Fin (2^k) → Scalar) (s s0 : State) (I : ℂ) (raw : Tape ℕ)
    (same : StateMatch s s0)
    (pc : s.pc=0) (ptr : s.natReg 2850=T) (base : s.natReg 3300=A)
    (native : s.natReg 5300=k)
    (bank : Printed T (UniformNativeScalarRecordMachine.shearRecord q w d src c).data s)
    (copied : ∀j, j<8 → ∀z,s.natHeap (T+j)=some z → raw.look j 0=z)
    (data : UniformFixedNetworkShearChildMachine.Present A R (2^k) f s)
    (baseline : UniformFixedNetworkShearChildMachine.Present A R (2^k) f0 s0)
    (wb : WordBound B s) (code : 106≤B) (tableEnd : T+8≤B)
    (width : w+1≤B) (extent : A+R*2^k≤B) :
    ∃u u0,
      BoundedExecution UniformNativeScalarRecordMachine.scalarProgram n x B s
        (10*2^k+4*k+c.val+62) u ∧
      BoundedExecution UniformNativeScalarRecordMachine.scalarProgram n (fun _ => 0) B s0
        (10*2^k+4*k+c.val+62) u0 ∧
      StateMatch u u0 ∧
      UniformNativeScalarRecordMachine.ScalarFrame
        (UniformFixedNetworkShearChildMachine.roleBase A (2^k) d.val) (2^k) s u ∧
      UniformNativeScalarRecordMachine.ScalarFrame
        (UniformFixedNetworkShearChildMachine.roleBase A (2^k) d.val) (2^k) s0 u0 ∧
      u.natReg 2850=T+8 ∧ u0.natReg 2850=T+8 ∧
      (∀i : Fin R,∀j : Fin (2^k),∃a a0,
        u.scalarHeap (A+i.val*2^k+j.val)=some a ∧
        u0.scalarHeap (A+i.val*2^k+j.val)=some a0 ∧
        (run (program R) (raw,((k,I),paired f f0))).val.2.look
          (i.val*2^k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run (program R) (raw,((k,I),paired f f0))).valid ∧
      (run (program R) (raw,((k,I),paired f f0))).work≤
        (20*R+2)*(10*2^k+4*k+c.val+62) ∧
      (run (program R) (raw,((k,I),paired f f0))).peak≤B := by
  have rawWord (j : ℕ) (hj : j<8) : raw.look j 0=
      (UniformNativeScalarRecordMachine.shearRecord q w d src c).data[j]'(by
        simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using hj) := by
    exact copied j hj _ (bank j (by
      simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using hj))
  have dest : raw.look 3 0=d.val := by
    simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using rawWord 3 (by decide)
  have sourceField : raw.look 4 0=src.val := by
    simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using rawWord 4 (by decide)
  have coeff : raw.look 7 0=c.val := by
    simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using rawWord 7 (by decide)
  obtain ⟨u,u0,run,run0,matched,frame,frame0,output,_,_,_⟩ :=
    DFTModelRecursiveScalarSource.actual_execution q w k A T B n x d src ne c
      f f0 s s0 I same pc ptr base native bank data baseline wb code tableEnd width extent
  obtain ⟨z,rz,_,cursor,_⟩ := UniformNativeScalarRecordMachine.scalar_execution
    q w k A T B n x d src ne c f s pc ptr base native bank data wb code tableEnd width extent
  have sameOutput : z=u := (rz.executes.deterministic run.executes).2
  subst z
  have value := program_specialize R k d.val src.val I raw (paired f f0) c dest sourceField coeff
  refine ⟨u,u0,run,run0,matched,frame,frame0,cursor,?_,?_,program_valid _ _ _ _ _,?_,?_⟩
  · rw [matched.natReg];exact cursor
  · intro i j
    obtain ⟨a,a0,ha,ha0,encoded⟩ := output i j
    exact ⟨a,a0,ha,ha0,by rw [value];exact encoded⟩
  · have h := program_work R k I raw (paired f f0)
    change _≤92+179*(R*2^k) at h
    calc
      _≤92+179*(R*2^k) := h
      _≤(20*R+2)*(10*2^k+62) := by
        rw [show (20*R+2)*(10*2^k+62)=200*(R*2^k)+(1240*R+20*2^k+124) by ring]
        omega
      _≤_ := Nat.mul_le_mul_left _ (by omega)
  · apply program_peak R (2^k) d.val src.val k B I raw (paired f f0)
    · positivity
    · have h := d.isLt;omega
    · rfl
    · exact d.isLt
    · exact src.isLt
    · omega
    · omega
    · exact dest
    · exact sourceField
    · rw [coeff];have h := c.isLt;omega

end
end ExactFourierCircuits.DFTModelSavingScalar
