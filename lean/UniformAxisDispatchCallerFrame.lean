import UniformGlobalClockConductor
import UniformSyntacticNatFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisDispatchCallerFrame
open UniformMachine UniformSyntacticNatFrame
noncomputable section

def Safe (i:Instruction):Prop:=match natDst i with
 | none=>True
 | some d=>d < 5920 ∨(5926 ≤ d ∧d < 5934) ∨(6200 ≤ d ∧d < 6790)
instance (i:Instruction):Decidable (Safe i):=by unfold Safe;split <;>infer_instance
def SafeProgram (p:Program):Prop:=∀i∈p,Safe i
lemma checked (p:Program) (all:p.all (fun i=>decide (Safe i))=true):SafeProgram p:=
 fun i hi=>of_decide_eq_true ((List.all_eq_true.mp all) i hi)
lemma dispatch_safe:SafeProgram UniformGlobalCalendarDispatch.program:=checked _ (by decide +kernel)
lemma adapter_safe:SafeProgram UniformGlobalAxisUnionAdapter.program:=checked _ (by decide +kernel)

def Kept (j:ℕ):Prop:=(5920 ≤ j ∧j < 5926) ∨(5934 ≤ j ∧j < 5940) ∨(6000 ≤ j ∧j < 6200) ∨6790 ≤ j
lemma avoids {p:Program} (safe:SafeProgram p) (j:ℕ) (kept:Kept j):Avoids p j:=by
 intro i hi bad
 have good:=safe i hi
 rw[Safe,bad] at good
 unfold Kept at kept
 omega

theorem dispatch {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformGlobalCalendarDispatch.program n x B s ticks t)
 (j:ℕ) (kept:Kept j):t.natReg j=s.natReg j:=
 boundedExecution_preserves (avoids dispatch_safe j kept) run

theorem adapter {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformGlobalAxisUnionAdapter.program n x B s ticks t)
 (j:ℕ) (kept:Kept j):t.natReg j=s.natReg j:=
 boundedExecution_preserves (avoids adapter_safe j kept) run
end
end ExactFourierCircuits.UniformAxisDispatchCallerFrame
