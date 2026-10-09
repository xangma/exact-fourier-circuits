import UniformActualClockSeedFrame
import UniformActualTickCallerFrame
import UniformFinalClockOuterFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockOuterSyntaxFrame
open UniformMachine UniformAssembly UniformSyntacticNatFrame
open UniformFinalClockOuterRetention (RequiredNat)
noncomputable section
attribute [local irreducible] UniformRecursiveSavingProgram.program

def Safe (i:Instruction):Prop:=match natDst i with
 | none=>True
 | some d=>¬RequiredNat d
instance (i:Instruction):Decidable (Safe i):=by
 unfold Safe
 split
 · infer_instance
 · unfold RequiredNat
   infer_instance
def SafeProgram (p:Program):Prop:=∀i∈p,Safe i
lemma checked (p:Program)(h:p.all (fun i=>decide (Safe i))=true):SafeProgram p:=
 fun i hi=>of_decide_eq_true ((List.all_eq_true.mp h) i hi)
lemma append_safe {p q:Program}(hp:SafeProgram p)(hq:SafeProgram q):SafeProgram (p++q):=by
 intro i hi;rcases List.mem_append.mp hi with h|h
 · exact hp i h
 · exact hq i h
lemma relocated_safe {p:Program}(hp:SafeProgram p)(base ret:ℕ):SafeProgram (p.map (relocate base ret)):=by
 intro i hi;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
 simpa only[Safe,relocate_dst] using hp a ha

lemma kernel_safe (W:ℕ):SafeProgram
 (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W):=by
 intro i hi
 have high:=UniformActualTickCallerFrame.high_program W i hi
 have clock:=UniformActualTickCallerFrame.clock_program W i hi
 have seed:=UniformActualClockSeedFrame.kernel_safe W i hi
 unfold Safe
 cases h:natDst i with
 | none=>trivial
 | some d=>
  simp only[UniformKernelCallerPrinterSafety.Safe,h] at high
  simp only[UniformClockCallerPrinterSafety.Safe,h] at clock
  simp only[UniformSeedCallerPrinterSafety.Safe,h] at seed
  unfold RequiredNat
  omega

lemma conductor_safe (prepare child:Program)(W:ℕ)(hp:SafeProgram prepare)
 (hk:SafeProgram (UniformGlobalKernelDiagonalAssembly.programFor child W)):
 SafeProgram (UniformGlobalClockConductor.programFor prepare child W):=by
 unfold UniformGlobalClockConductor.programFor
 repeat' apply append_safe
 · exact checked _ (by decide +kernel)
 · exact checked _ (by rfl)
 · exact checked _ (by decide +kernel)
 · exact checked _ (by rfl)
 · exact relocated_safe hp _ _
 · apply relocated_safe
   exact checked _ (by decide +kernel)
 · apply relocated_safe
   exact checked _ (by decide +kernel)
 · exact checked _ (by decide +kernel)
 · exact checked _ (by decide +kernel)
 · exact relocated_safe hk _ _
 · exact checked _ (by decide +kernel)
 · exact checked _ (by decide +kernel)
lemma program_safe:SafeProgram UniformActualGlobalClockProgram.program:=by
 apply conductor_safe
 · exact checked _ (by decide +kernel)
 · exact kernel_safe _
lemma avoids (q:ℕ)(hq:RequiredNat q):Avoids UniformActualGlobalClockProgram.program q:=by
 intro i hi bad
 have h:=program_safe i hi
 have h':¬RequiredNat q:=by simpa only[Safe,bad] using h
 exact h' hq

theorem bounded_runs {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks u)
 (q:ℕ)(hq:RequiredNat q):u.natReg q=s.natReg q:=
 boundedRuns_preserves (avoids q hq) run

theorem bounded_execution {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x B s ticks u)
 (q:ℕ)(hq:RequiredNat q):u.natReg q=s.natReg q:=
 boundedExecution_preserves (avoids q hq) run
end
end ExactFourierCircuits.UniformActualClockOuterSyntaxFrame
