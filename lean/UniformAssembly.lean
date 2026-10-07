import UniformMachineRuns

set_option autoImplicit false

/-! Literal relocation joins finite RAM helpers. Control targets are shifted;
the helper's halt becomes one charged jump to its continuation. No call or
array primitive is added to the instruction set. -/
namespace ExactFourierCircuits.UniformAssembly
open UniformMachine
noncomputable section

def relocate (base returnPC : ℕ) : Instruction → Instruction
  | .branchLT a b yes no => .branchLT a b (base+yes) (base+no)
  | .jump target => .jump (base+target)
  | .halt => .jump returnPC
  | ins => ins

def placed (base : ℕ) (s : State) : State := { s with pc := base+s.pc }

def placedResult (base returnPC : ℕ) : StepResult → StepResult
  | .running s => .running (placed base s)
  | .halted s => .running { s with pc := returnPC }
  | .failed => .failed

def CodeAt (p q : Program) (base returnPC : ℕ) : Prop :=
  ∀ i, i < p.length → q[base+i]? = (p[i]?).map (relocate base returnPC)

theorem step_placed (p q : Program) (base returnPC n : ℕ) (x : Fin n → ℂ)
    (code : CodeAt p q base returnPC) (s : State) (hp : s.pc < p.length) :
    step q n x (placed base s) = placedResult base returnPC (step p n x s) := by
  have hc := code s.pc hp
  cases hg : p[s.pc]? with
  | none => simp [step,placed,hc,hg,placedResult]
  | some ins =>
    cases ins with
    | branchLT left right yes no =>
      by_cases h : s.natReg left < s.natReg right
      all_goals simp [step,placed,hc,hg,relocate,placedResult,h]
    | _ =>
      simp [step,placed,hc,hg,relocate,placedResult,next,writeNat,
        writeScalar,Nat.add_assoc]
      all_goals split <;> simp_all

theorem running_pc {p : Program} {n : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : step p n x s = .running u) : s.pc < p.length := by
  cases hg : p[s.pc]? with
  | none => simp [step,hg] at h
  | some ins => exact (List.getElem?_eq_some_iff.1 hg).choose

theorem halted_pc {p : Program} {n : ℕ} {x : Fin n → ℂ} {s : State}
    (h : step p n x s = .halted s) : s.pc < p.length := by
  cases hg : p[s.pc]? with
  | none => simp [step,hg] at h
  | some ins => exact (List.getElem?_eq_some_iff.1 hg).choose

theorem running_placed {p q : Program} {base returnPC n : ℕ} {x : Fin n → ℂ}
    (code : CodeAt p q base returnPC) {s u : State}
    (h : step p n x s = .running u) :
    step q n x (placed base s) = .running (placed base u) := by
  rw [step_placed p q base returnPC n x code s (running_pc h),h]
  rfl

theorem halted_placed {p q : Program} {base returnPC n : ℕ} {x : Fin n → ℂ}
    (code : CodeAt p q base returnPC) {s : State}
    (h : step p n x s = .halted s) :
    step q n x (placed base s) = .running { s with pc := returnPC } := by
  rw [step_placed p q base returnPC n x code s (halted_pc h),h]
  rfl

theorem Runs.placed {p q : Program} {base returnPC n t : ℕ} {x : Fin n → ℂ}
    (code : CodeAt p q base returnPC) {s u : State} (h : UniformMachine.Runs p n x s t u) :
    UniformMachine.Runs q n x (placed base s) t (placed base u) := by
  induction h with
  | refl s => exact .refl _
  | next hs _ ih => exact .next (running_placed code hs) ih

/-- The charged halt is replaced by a charged continuation jump, so the
instruction count is unchanged. -/
theorem Executes.placed {p q : Program} {base returnPC n t : ℕ} {x : Fin n → ℂ}
    (code : CodeAt p q base returnPC) {s u : State} (h : UniformMachine.Executes p n x s t u) :
    UniformMachine.Runs q n x (placed base s) t { u with pc := returnPC } := by
  induction h with
  | halt hs => exact .next (halted_placed code hs) (.refl _)
  | next hs _ ih => exact .next (running_placed code hs) ih

theorem wordBound_mono {B C : ℕ} (hBC : B ≤ C) {s : State} (h : WordBound B s) :
    WordBound C s := by
  rcases h with ⟨hp,hr,hn,hs,ho,hd⟩
  refine ⟨hp.trans hBC,fun r => (hr r).trans hBC,?_,?_,?_,?_⟩
  · intro a v h; exact ⟨(hn a v h).1.trans hBC,(hn a v h).2.trans hBC⟩
  · intro a v h; exact (hs a v h).trans hBC
  · intro a v h; exact (ho a v h).trans hBC
  · intro d h; exact (hd d h).trans hBC

theorem placed_bound (base B : ℕ) (s : State) (h : WordBound B s) :
    WordBound (base+B) (placed base s) := by
  have hb : B ≤ base+B := by omega
  have hm := wordBound_mono hb h
  exact ⟨by simpa [placed] using Nat.add_le_add_left h.1 base,hm.2⟩

theorem BoundedRuns.placed {p q : Program} {base returnPC n B C t : ℕ} {x : Fin n → ℂ}
    (code : CodeAt p q base returnPC) (hBC : base+B ≤ C) {s u : State}
    (h : UniformMachine.BoundedRuns p n x B s t u) :
    UniformMachine.BoundedRuns q n x C (placed base s) t (placed base u) := by
  induction h with
  | refl hb => exact .refl (wordBound_mono hBC (placed_bound base B _ hb))
  | next hb hs _ ih =>
    exact .next (wordBound_mono hBC (placed_bound base B _ hb)) (running_placed code hs) ih

theorem BoundedExecution.placed {p q : Program} {base returnPC n B C t : ℕ}
    {x : Fin n → ℂ} (code : CodeAt p q base returnPC) (hBC : base+B ≤ C)
    (hret : returnPC ≤ C) {s u : State} (h : UniformMachine.BoundedExecution p n x B s t u) :
    UniformMachine.BoundedRuns q n x C (placed base s) t { u with pc := returnPC } := by
  induction h with
  | halt hb hs =>
    refine .next (wordBound_mono hBC (placed_bound base B _ hb))
      (halted_placed code hs) (.refl ?_)
    exact changePC_bound C _ _ (wordBound_mono (by omega) hb) hret
  | next hb hs _ ih =>
    exact .next (wordBound_mono hBC (placed_bound base B _ hb)) (running_placed code hs) ih

def embed (head p suffix : Program) (returnPC : ℕ) : Program :=
  head ++ p.map (relocate head.length returnPC) ++ suffix

theorem embed_code (head p suffix : Program) (returnPC : ℕ) :
    CodeAt p (embed head p suffix returnPC) head.length returnPC := by
  intro i hi
  simp [embed,List.getElem?_append_right,hi,List.getElem?_append_left]

theorem embed_length (head p suffix : Program) (returnPC : ℕ) :
    (embed head p suffix returnPC).length = head.length+p.length+suffix.length := by
  simp [embed,Nat.add_assoc]

end
end ExactFourierCircuits.UniformAssembly
