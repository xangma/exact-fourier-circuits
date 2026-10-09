import UniformLocalRequestCursorMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestFrames
open UniformMachine UniformNewtonTableMachine

def Within (writes:List ℕ) (ins:Instruction):Bool:=match ins with
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>decide (d∈writes)
 | _=>true
lemma outside_keeps {p:Program}{writes:List ℕ}(h:p.all (Within writes)=true)
 (q:ℕ)(hq:q∉writes):∀ins∈p,KeepsNat q ins:=by
 intro ins hi
 have checked:=List.all_eq_true.mp h ins hi
 cases ins <;>simp only [Within,KeepsNat] at *
 all_goals simp only [decide_eq_true_eq] at checked
 all_goals intro eq;subst q;exact hq checked

def cursorWrites:List ℕ:=[6160,6161,6162,6163,6164,6165,6166,6168,6169,6170,6171,6172,
 6173,6174,6179,6190,6191,6193,6194]
lemma cursor_checked:UniformLocalRequestCursorMachine.program.all (Within cursorWrites)=true:=by decide
lemma cursor_nat {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformLocalRequestCursorMachine.program n x B s ticks u)
 (q:ℕ)(hq:q∉cursorWrites):u.natReg q=s.natReg q:=
 Executes.keeps_nat run.executes (outside_keeps cursor_checked q hq)

def advanceWrites:List ℕ:=[6160,6161,6162,6163,6164,6165,6166,6173,6174,6190,6191,6193]
lemma advance_checked:UniformLocalRequestAdvanceMachine.program.all (Within advanceWrites)=true:=by decide
lemma advance_nat {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformLocalRequestAdvanceMachine.program n x B s ticks u)
 (q:ℕ)(hq:q∉advanceWrites):u.natReg q=s.natReg q:=
 Executes.keeps_nat run.executes (outside_keeps advance_checked q hq)

lemma cursor_high {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformLocalRequestCursorMachine.program n x B s ticks u)
 (q:ℕ)(hq:6400≤q):u.natReg q=s.natReg q:=by
 apply cursor_nat run q
 simp only [cursorWrites,List.mem_cons,List.not_mem_nil,or_false]
 omega
lemma advance_high {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformLocalRequestAdvanceMachine.program n x B s ticks u)
 (q:ℕ)(hq:6400≤q):u.natReg q=s.natReg q:=by
 apply advance_nat run q
 simp only [advanceWrites,List.mem_cons,List.not_mem_nil,or_false]
 omega
end ExactFourierCircuits.UniformLocalRequestFrames
