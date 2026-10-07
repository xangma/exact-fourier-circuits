import UniformAssembly
import UniformDirectBounds

set_option autoImplicit false

/-! A complete DFT execution through literal helper placement and continuation.
This tests assembly on all positive lengths; the fallback remains quadratic. -/
namespace ExactFourierCircuits.UniformAssembledDirect
open UniformMachine
noncomputable section

def program : Program :=
  UniformAssembly.embed [.jump 1] UniformDirectMachine.program [.halt] 22

theorem program_length : program.length = 23 := rfl

theorem bounded_DFT {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ s : State,
    BoundedExecution program n x (n+22) initial (7*n^2+9*n+9) s ∧
      ComputesDFT n x s ∧ s.rootOrders = [n] := by
  obtain ⟨s,hex,hdft,hroot⟩ := UniformDirectBounds.direct_bounded hn x
  have code : UniformAssembly.CodeAt UniformDirectMachine.program program 1 22 :=
    UniformAssembly.embed_code [.jump 1] UniformDirectMachine.program [.halt] 22
  have run := UniformAssembly.BoundedExecution.placed code
    (by omega : 1+(n+21) ≤ n+22) (by omega : 22 ≤ n+22) hex
  let u : State := {s with pc := 22}
  have entry : BoundedRuns program n x (n+22) initial 1 (UniformAssembly.placed 1 initial) := by
    refine .next (initial_wordBound _) ?_ (.refl ?_)
    · simp [step,program,UniformAssembly.embed,UniformAssembly.placed,initial]
    · convert UniformAssembly.placed_bound 1 (n+21) initial (initial_wordBound _) using 1; omega
  have halt : BoundedExecution program n x (n+22) u 1 u := by
    refine .halt run.final_bound ?_
    simp [step,u,program,UniformAssembly.embed,UniformDirectMachine.program]
  refine ⟨u,?_,hdft,hroot⟩
  convert entry.executes (run.executes halt) using 1; omega

end
end ExactFourierCircuits.UniformAssembledDirect
