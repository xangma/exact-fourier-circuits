import UniformAxisDispatchCallerFrame
import UniformGlobalAxisUnionAdapter
import UniformFourierAxisPrepareMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisStartupFrame
open UniformMachine UniformSyntacticNatFrame
noncomputable section

def Safe (i:Instruction):Prop:=match natDst i with
 | none=>True
 | some d=>(d<100∨107≤d)∧(d<200∨210≤d)
instance (i:Instruction):Decidable (Safe i):=by unfold Safe;split <;>infer_instance
lemma checked (p:Program) (h:p.all (fun i=>decide (Safe i))=true):∀i∈p,Safe i:=
 fun i hi=>of_decide_eq_true ((List.all_eq_true.mp h) i hi)
lemma dispatch_safe:∀i∈UniformGlobalCalendarDispatch.program,Safe i:=checked _ (by decide +kernel)
lemma adapter_safe:∀i∈UniformGlobalAxisUnionAdapter.program,Safe i:=checked _ (by decide +kernel)
lemma prepare_safe:∀i∈UniformFourierAxisPrepareMachine.program,Safe i:=checked _ (by decide +kernel)
lemma avoids {p:Program} (safe:∀i∈p,Safe i) (j:ℕ) (saved:100≤j∧j<107∨200≤j∧j<210):Avoids p j:=by
 intro i mem bad
 have h:=safe i mem
 rw[Safe,bad] at h
 omega

def Kept (j:ℕ):Prop:=UniformAxisDispatchCallerFrame.Kept j∨(100≤j∧j<107∨200≤j∧j<210)
lemma dispatch {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformGlobalCalendarDispatch.program n x B s ticks t)
 (j:ℕ)(kept:Kept j):t.natReg j=s.natReg j:=by
 rcases kept with h|saved
 · exact UniformAxisDispatchCallerFrame.dispatch run j h
 · exact boundedExecution_preserves (avoids dispatch_safe j saved) run
lemma adapter {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformGlobalAxisUnionAdapter.program n x B s ticks t)
 (j:ℕ)(kept:Kept j):t.natReg j=s.natReg j:=by
 rcases kept with h|saved
 · exact UniformAxisDispatchCallerFrame.adapter run j h
 · exact boundedExecution_preserves (avoids adapter_safe j saved) run
lemma prepare {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformFourierAxisPrepareMachine.program n x B s ticks t)
 (j:ℕ)(saved:100≤j∧j<107∨200≤j∧j<210):t.natReg j=s.natReg j:=
 boundedExecution_preserves (avoids prepare_safe j saved) run
end
end ExactFourierCircuits.UniformFinalAxisStartupFrame
