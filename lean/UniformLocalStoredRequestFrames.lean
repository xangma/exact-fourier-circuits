import UniformLocalStoredRequestBootstrap
import UniformLocalRectangleCacheBindings
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestBootstrap
open UniformMachine UniformNewtonTableMachine UniformAllAxisSeedPreparation
def savedInstruction:Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>decide (d<100 ∨ 106<d)
 | _=>true
lemma saved_program:program.all savedInstruction=true:=by decide
lemma program_keeps_saved(q:ℕ)(lo:100 ≤ q)(hi:q ≤ 106):∀ins∈program,KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp saved_program ins member
 cases ins <;>simp only [savedInstruction,KeepsNat] at *
 all_goals simp only [decide_eq_true_eq] at h
 all_goals omega
lemma execution_saved {n B ticks:ℕ}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)(q:ℕ)(lo:100 ≤ q)(hi:q ≤ 106):
 u.natReg q=s.natReg q:=Executes.keeps_nat run.executes (program_keeps_saved q lo hi)

lemma prefix_frame {n B ticks:ℕ}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)
 (old:UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n ≤ UniformJointCacheWorkspace.lowRow n)
 (nat:UniformNatCopyMachine.Outside (UniformJointCacheWorkspace.lowRow n) 7 s.natHeap u)
 (scalar:u.scalarHeap=s.scalarHeap)(out:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):
 UniformSeedRankCrossPreparation.PreservedFrame n s u:=by
 refine ⟨?_,fun i _=>congrFun scalar i,execution_saved run,out,roots⟩
 intro i hi
 exact nat i (Or.inl (lt_of_lt_of_le hi old))

lemma driver_retained {n:ℕ}{j:Fin (axisCount n)}{c:UniformLocalCacheSlotHeaderMachine.Parameters}
 {I H:ℕ}{s u:State}(h:UniformLocalRectangleCacheBindings.Driver j c I H s)
 (endLow:UniformJointCacheWorkspace.lowRow n+7 ≤ H)
 (nat:∀r,4236 ≤ r → r ≠ 6190 → u.natReg r=s.natReg r)
 (heap:UniformNatCopyMachine.Outside (UniformJointCacheWorkspace.lowRow n) 7 s.natHeap u):
 UniformLocalRectangleCacheBindings.Driver j c I H u:=by
 have timeReg:=nat 6161 (by omega) (by omega)
 refine ⟨?_,(nat _ (by omega) (by omega)).trans h.originalDirectory,h.radix,?_,?_,h.kind⟩
 · intro p hp lo
   have tested:(UniformLocalCacheContextMachine.copies.all fun p=>p.2!=6190)=true:=by decide
   have nz:p.2 ≠ 6190:=by simpa using List.all_eq_true.mp tested p hp
   exact (nat p.2 (by omega) nz).trans (h.copies p hp lo)
 · rw [timeReg];exact h.timeHigh
 · rw [timeReg,heap _ (Or.inr (endLow.trans h.timeHigh))];exact h.time

end ExactFourierCircuits.UniformLocalStoredRequestBootstrap
