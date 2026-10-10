import DFTModelSavingBinarySuffixBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinarySuffix
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] program

/-- Charged suffix code simulates the actual69 native program on the same
original banks, including its independently obtained zero-input execution. -/
theorem actual_execution {R : ℕ} (n B k b A : ℕ) (x : Fin n → ℂ)
    (f f0 : Fin R → Fin (2^k) → Scalar) (s s0 : State)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 5200=k)
    (arrays : s.natReg 5201=R) (addr : s.natReg 5202=A) (size : s.natReg 5203=2^k) (start : s.natReg 5204=b)
    (data : ∀r j,s.scalarHeap (A+r.val*2^k+j.val)=some (f r j))
    (baseline : ∀r j,s0.scalarHeap (A+r.val*2^k+j.val)=some (f0 r j))
    (roles : 0<R) (ha : 3≤A) (con : UniformBinaryCStageMachine.Constants s)
    (cap : b≤k) (code : 69≤B) (stride : 2^b*2≤B) (extent : A+R*2^k≤B) (wb : WordBound B s) :
    ∃ u u0,
      BoundedExecution UniformBinarySpectatorCMachine.program n x B s
        (4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+9) u ∧
      BoundedExecution UniformBinarySpectatorCMachine.program n (fun _=>0) B s0
        (4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+9) u0 ∧
      StateMatch u u0 ∧
      UniformBinarySpectatorCMachine.Frame A (R*2^k) s u ∧
      UniformBinarySpectatorCMachine.Frame A (R*2^k) s0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧ UniformBinaryCStageMachine.Constants u0 ∧
      u.pc=68 ∧ u0.pc=68 ∧
      (∀r : Fin R,∀j : Fin (2^k),∃a a0,
        u.scalarHeap (A+r.val*2^k+j.val)=some a ∧
        u0.scalarHeap (A+r.val*2^k+j.val)=some a0 ∧
        (run program (b,((k,Complex.I),paired f f0))).val.2.look
          (r.val*2^k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run program (b,((k,Complex.I),paired f f0))).valid ∧
      (run program (b,((k,Complex.I),paired f f0))).work≤
        32*(4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+9) ∧
      (run program (b,((k,Complex.I),paired f f0))).peak≤B := by
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
  obtain ⟨u,actual,output,frame,cu,pu⟩ :=
    UniformBinarySpectatorCMachine.execution n B k b R A x s f pc bits arrays addr size start
      data cap ha con code extent stride wb
  obtain ⟨u0,actual0,output0,frame0,cu0,pu0⟩ :=
    UniformBinarySpectatorCMachine.execution n B k b R A (fun _=>0) s0 f0
      (same.pc.trans pc) (by rw [same.natReg];exact bits)
      (by rw [same.natReg];exact arrays) (by rw [same.natReg];exact addr)
      (by rw [same.natReg];exact size) (by rw [same.natReg];exact start)
      baseline cap ha con0 code extent stride (same.wordBound wb)
  obtain ⟨u0',actual0',matched⟩ := boundedExecution_match (y:=fun _=>0) actual same
  have eq : u0'=u0 := (actual0'.executes.deterministic actual0.executes).2
  subst u0'
  refine ⟨u,u0,actual,actual0,matched,frame,frame0,cu,cu0,pu,pu0,?_,?_,?_,?_⟩
  · intro r j
    refine ⟨_,_,output r j,output0 r j,?_⟩
    exact program_lookup f f0 b cap r j
  · exact program_valid _ _ _ _
  · exact program_native_work f f0 b cap roles
  · exact program_peak f f0 b B cap roles (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelSavingBinarySuffix
