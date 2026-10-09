import UniformCacheRangeSelectorData
import UniformReciprocalMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformNewtonTableMachine

def selectorInstruction:Instruction → Bool
 | .natLiteral d _|.length d|.natBinary _ d _ _|.loadNat d _=>decide (d=6705 ∨ 6710 ≤ d ∧ d ≤ 6723)
 | _=>true
lemma selectorFootprint:Selector.program.all selectorInstruction=true:=by decide
lemma selector_keeps(q:ℕ)(a:q≠6705)(b:q<6710 ∨ 6723<q):∀ins∈Selector.program,KeepsNat q ins:=by
 intro ins mem
 have h:selectorInstruction ins=true:=List.all_eq_true.mp selectorFootprint ins mem
 cases ins <;>simp only[selectorInstruction,KeepsNat,decide_eq_true_eq] at * <;>try trivial
 all_goals omega
lemma selector_control {r tasks N tick O used i n B ticks s u D stride count finalUsed}
 {x:Fin n → ℂ}(run:BoundedExecution Selector.program n x B s ticks u)
 (h:Control r tasks N tick O used i s)
 (done:UniformGlobalCalendarSelector.Header D stride count tick O finalUsed count u):
 Control r tasks N tick O finalUsed i u:=by
 have keep(q:ℕ)(a:q≠6705)(b:q<6710 ∨ 6723<q):u.natReg q=s.natReg q:=
  Executes.keeps_nat run.executes (selector_keeps q a b)
 exact ⟨(keep 7100 (by decide) (by omega)).trans h.zero,
  (keep 7101 (by decide) (by omega)).trans h.one,
  (keep 7102 (by decide) (by omega)).trans h.two,
  (keep 7110 (by decide) (by omega)).trans h.spacing,
  (keep 7107 (by decide) (by omega)).trans h.nodeCount,
  (keep 7106 (by decide) (by omega)).trans h.index,
  (keep 7108 (by decide) (by omega)).trans h.pointer,done.tick,done.output,by simpa using done.used⟩
end ExactFourierCircuits.UniformCacheRangeSelector
