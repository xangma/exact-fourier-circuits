import UniformAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundedAssembly
open UniformMachine UniformAssembly
noncomputable section

/-- Relocation only changes the PC; it need not enlarge the data/address budget. -/
theorem placed_bound (base B : ℕ) (s : State) (hs : WordBound B s)
    (hpc : base+s.pc≤B) : WordBound B (placed base s) := ⟨hpc,hs.2⟩

/-- Halting helper executions can be relocated in the same word budget. Each
executed local PC is inside the literal helper, so a constant code-size bound
suffices even when it is called repeatedly by a loop. All instructions remain charged. -/
theorem boundedExecution_placed {p q : Program} {base returnPC n B t : ℕ}
    {x : Fin n → ℂ} (code : CodeAt p q base returnPC)
    (hcode : base+p.length≤B) (hret : returnPC≤B) {s u : State}
    (h : BoundedExecution p n x B s t u) :
    BoundedRuns q n x B (placed base s) t {u with pc:=returnPC} := by
  induction h with
  | halt hb hh =>
    have hp:=UniformAssembly.halted_pc hh
    refine .next (placed_bound base B _ hb (by omega))
      (UniformAssembly.halted_placed code hh) (.refl ?_)
    exact changePC_bound B _ returnPC hb hret
  | next hb hn _ ih =>
    have hp:=UniformAssembly.running_pc hn
    exact .next (placed_bound base B _ hb (by omega))
      (UniformAssembly.running_placed code hn) ih

end
end ExactFourierCircuits.UniformBoundedAssembly
