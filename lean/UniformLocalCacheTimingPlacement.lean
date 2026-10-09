import UniformAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingPlacement
open UniformMachine UniformAssembly
noncomputable section
/-- Relocation for a terminal segment: its genuine halt remains a halt. -/
def terminalRelocate (base:ℕ)(ins:Instruction):Instruction:=match ins with
 | .halt=>.halt
 | ins=>relocate base 0 ins

def TerminalCodeAt(p q:Program)(base:ℕ):Prop:=
 ∀i,i<p.length→q[base+i]?=(p[i]?).map (terminalRelocate base)

def terminalResult(base:ℕ):StepResult→StepResult
 | .running s=>.running (placed base s)
 | .halted s=>.halted (placed base s)
 | .failed=>.failed

lemma terminal_step(p q:Program)(base n:ℕ)(x:Fin n→ℂ)
 (code:TerminalCodeAt p q base)(s:State)(hp:s.pc<p.length):
 step q n x (placed base s)=terminalResult base (step p n x s):=by
 have hc:=code s.pc hp
 cases hg:p[s.pc]? with
 | none=>simp [step,placed,hc,hg,terminalResult]
 | some ins=>
  cases ins with
  | branchLT left right yes no=>
   by_cases h:s.natReg left<s.natReg right
   all_goals simp [step,placed,hc,hg,terminalRelocate,relocate,terminalResult,h]
  | _=>
   simp [step,placed,hc,hg,terminalRelocate,relocate,terminalResult,next,writeNat,writeScalar,Nat.add_assoc]
   all_goals split <;>simp_all

/-- Same word bound is retained using the actual finite segment extent,
rather than adding its base to all unrelated data words. -/
lemma terminal_execution {p q:Program}{base n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (code:TerminalCodeAt p q base)(extent:base+p.length≤B)
 (run:BoundedExecution p n x B s t u):
 BoundedExecution q n x B (placed base s) t (placed base u):=by
 induction run with
 | halt hb hs=>
  have pc:=halted_pc hs
  refine .halt ⟨by dsimp [placed];omega,hb.2⟩ ?_
  rw [terminal_step p q base n x code _ pc,hs]
  rfl
 | next hb hs rest ih=>
  have pc:=running_pc hs
  refine .next ⟨by dsimp [placed];omega,hb.2⟩ ?_ ih
  rw [terminal_step p q base n x code _ pc,hs]
  rfl
end
end ExactFourierCircuits.UniformLocalCacheTimingPlacement
