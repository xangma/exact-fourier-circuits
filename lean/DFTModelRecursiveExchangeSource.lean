import DFTModelRecursiveExchangeProgram

set_option autoImplicit false
/-! A concrete opcode-4 translation. The upstream program reads the actual
record count and pair coordinates and performs successive readonly tabs.
Its single evaluation carries both the actual and zero-source native runs. -/
namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open UniformFixedNetworkScheduleMachine (Printed)
noncomputable section

attribute [local irreducible] pairProgram body pairsProgram decode program

/-- Concrete native98 simulation, including the independently obtained zero
source run, real output presence, exact affine channels, and charged work/peak.
No output bank or exchange action is supplied as an entry premise. -/
theorem actual_execution {R : ℕ} (q w k A T B n : ℕ) (x : Fin n → ℂ)
    (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (f f0 : Fin R → Fin (2^k) → Scalar) (s s0 : State) (I : ℂ)
    (same : StateMatch s s0) (pc : s.pc=0) (ptr : s.natReg 2850=T)
    (base : s.natReg 3300=A) (native : s.natReg 5300=k)
    (bank : Printed T (UniformNativeExchangeRecordMachine.record q w ps).data s)
    (data : UniformFixedNetworkShearChildMachine.Present A R (2^k) f s)
    (baseline : UniformFixedNetworkShearChildMachine.Present A R (2^k) f0 s0)
    (roles : 0<R) (wb : WordBound B s) (code : 98≤B)
    (extent : A+R*2^k≤B) (tableEnd : T+8+4*ps.length≤B) (width : w+1≤B) :
    ∃ u u0,
      BoundedExecution UniformNativeExchangeRecordMachine.program n x B s
        ((10*2^k+21)*ps.length+4*k+50) u ∧
      BoundedExecution UniformNativeExchangeRecordMachine.program n (fun _ => 0) B s0
        ((10*2^k+21)*ps.length+4*k+50) u0 ∧
      StateMatch u u0 ∧
      UniformNativeExchangeRecordMachine.FullFrame A (R*2^k) s u ∧
      UniformNativeExchangeRecordMachine.FullFrame A (R*2^k) s0 u0 ∧
      u.natReg 2850=T+8+4*ps.length ∧
      u0.natReg 2850=T+8+4*ps.length ∧
      (∀ i : Fin R,∀ j : Fin (2^k),∃ a a0,
        u.scalarHeap (A+i.val*2^k+j.val)=some a ∧
        u0.scalarHeap (A+i.val*2^k+j.val)=some a0 ∧
        (run (program R) (recordTape q w ps,((k,I),paired f f0))).val.2.look
          (i.val*2^k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run (program R) (recordTape q w ps,((k,I),paired f f0))).valid ∧
      (run (program R) (recordTape q w ps,((k,I),paired f f0))).work≤
        (20*R+10)*((10*2^k+21)*ps.length+4*k+50) ∧
      (run (program R) (recordTape q w ps,((k,I),paired f f0))).peak≤B := by
  obtain ⟨u,actual,output,cursor,frame⟩ :=
    UniformNativeExchangeRecordMachine.execution q w k A T B n x ps f s
      pc ptr base native bank data roles wb code extent tableEnd width
  have bank0 : Printed T (UniformNativeExchangeRecordMachine.record q w ps).data s0 := by
    intro j hj;rw [same.natHeap];exact bank j hj
  obtain ⟨u0,actual0,output0,cursor0,frame0⟩ :=
    UniformNativeExchangeRecordMachine.execution q w k A T B n (fun _ => 0) ps f0 s0
      (same.pc.trans pc) (by rw [same.natReg];exact ptr)
      (by rw [same.natReg];exact base) (by rw [same.natReg];exact native)
      bank0 baseline roles (same.wordBound wb) code extent tableEnd width
  obtain ⟨u0',actual0',matched⟩ := boundedExecution_match (y:=fun _ => 0) actual same
  have eq : u0'=u0 := (actual0'.executes.deterministic actual0.executes).2
  subst u0'
  refine ⟨u,u0,actual,actual0,matched,frame,frame0,cursor,cursor0,?_,
    program_valid _ _ _,program_native_work q w k ps f f0 I,?_⟩
  · intro i j
    refine ⟨_,_,output i j,output0 i j,?_⟩
    exact program_lookup q w ps (by positivity) f f0 k I i j
  · exact program_peak_bound q w ps (by positivity) roles f f0 k B I (by omega) (by omega)

end
end ExactFourierCircuits.DFTModelRecursiveExchange
