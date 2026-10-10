import DFTModelSavingBinaryCost

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open UniformBinaryTensorCoordinates
noncomputable section

/-- Ordinary binary base: the immutable runtime header and a fresh full bank. -/
def base : Prog false DFTModelClockControl.Node DFTModelClockControl.Node :=
  .fork (.atom .fst) DFTModelRecursiveBinary.program

attribute [local irreducible] DFTModelRecursiveBinary.program

theorem base_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run base ((k,I),v) =
      {run DFTModelRecursiveBinary.program ((k,I),v) with
        val:=((k,I),(run DFTModelRecursiveBinary.program ((k,I),v)).val),
        work:=(run DFTModelRecursiveBinary.program ((k,I),v)).work+2} := by
  rw [base,fork_run,atom_run]
  simp only [Atom.run,Bill.pass,Bill.one,zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem base_paired {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar) :
    (run base ((k,Complex.I),paired f f0)).val =
      ((k,Complex.I),paired (fun r=>applyAxes k (List.finRange k) (f r))
        (fun r=>applyAxes k (List.finRange k) (f0 r))) := by
  rw [base_run,program_paired]

theorem actual_execution {R : ℕ} (n B k A : ℕ) (x : Fin n → ℂ)
    (f f0 : Fin R → Fin (2^k) → Scalar) (s s0 : State)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 4900=k)
    (arrays : s.natReg 4901=R) (addr : s.natReg 4902=A) (size : s.natReg 4903=2^k)
    (data : ∀r j,s.scalarHeap (A+r.val*2^k+j.val)=some (f r j))
    (baseline : ∀r j,s0.scalarHeap (A+r.val*2^k+j.val)=some (f0 r j))
    (roles : 0<R) (ha : 3≤A) (con : UniformBinaryCStageMachine.Constants s)
    (code : 54≤B) (extent : A+R*2^k≤B) (wb : WordBound B s) :
    ∃ u u0,
      BoundedExecution UniformBinaryBatchCMachine.program n x B s
        (R*UniformBinaryBatchCMachine.arrayCost k+5) u ∧
      BoundedExecution UniformBinaryBatchCMachine.program n (fun _=>0) B s0
        (R*UniformBinaryBatchCMachine.arrayCost k+5) u0 ∧
      StateMatch u u0 ∧
      UniformBinaryBatchCMachine.Frame A (R*2^k) s u ∧
      UniformBinaryBatchCMachine.Frame A (R*2^k) s0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧ UniformBinaryCStageMachine.Constants u0 ∧
      u.pc=53 ∧ u0.pc=53 ∧
      (∀r : Fin R,∀j : Fin (2^k),∃a a0,
        u.scalarHeap (A+r.val*2^k+j.val)=some a ∧
        u0.scalarHeap (A+r.val*2^k+j.val)=some a0 ∧
        (run base ((k,Complex.I),paired f f0)).val.2.look
          (r.val*2^k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run base ((k,Complex.I),paired f f0)).valid ∧
      (run base ((k,Complex.I),paired f f0)).work≤
        33*(R*UniformBinaryBatchCMachine.arrayCost k+5) ∧
      (run base ((k,Complex.I),paired f f0)).peak≤B := by
  have con0 : UniformBinaryCStageMachine.Constants s0 := by
    constructor
    · obtain ⟨v,hv,hm⟩ := (same.scalarHeap 1).left con.1
      have eq:=hm.eq_of_prepared rfl
      rw [←eq] at hv
      exact hv
    · obtain ⟨v,hv,hm⟩ := (same.scalarHeap 2).left con.2
      have eq:=hm.eq_of_prepared rfl
      rw [←eq] at hv
      exact hv
  obtain ⟨u,actual,output,_,frame,cu,pu⟩ :=
    UniformBinaryBatchCMachine.execution n B k R A x s f pc bits arrays addr size
      data ha con code extent wb
  obtain ⟨u0,actual0,output0,_,frame0,cu0,pu0⟩ :=
    UniformBinaryBatchCMachine.execution n B k R A (fun _=>0) s0 f0
      (same.pc.trans pc) (by rw [same.natReg];exact bits)
      (by rw [same.natReg];exact arrays) (by rw [same.natReg];exact addr)
      (by rw [same.natReg];exact size) baseline ha con0 code extent (same.wordBound wb)
  obtain ⟨u0',actual0',matched⟩ := boundedExecution_match (y:=fun _=>0) actual same
  have eq : u0'=u0 := (actual0'.executes.deterministic actual0.executes).2
  subst u0'
  refine ⟨u,u0,actual,actual0,matched,frame,frame0,cu,cu0,pu,pu0,?_,?_,?_,?_⟩
  · intro r j
    refine ⟨_,_,output r j,output0 r j,?_⟩
    rw [base_run]
    exact program_lookup f f0 r j
  · rw [base_run]
    exact DFTModelRecursiveBinary.program_valid _ _ _
  · rw [base_run]
    have h:=program_native_work f f0 roles
    have hcost : 2≤R*UniformBinaryBatchCMachine.arrayCost k+5 := by omega
    dsimp only
    omega
  · rw [base_run]
    exact program_peak f f0 B roles (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelSavingBinary
