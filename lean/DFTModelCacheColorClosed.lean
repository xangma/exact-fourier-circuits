import DFTModelCacheColorReadback

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open UniformMatchingAxisTableMachine (InRange)
noncomputable section

attribute [local irreducible] Code.run

theorem compiled_lengths (r : ℕ) (z : Tape Row.T) :
    (run compiled (r,z)).val.2.1.len=824 ∧
      (run compiled (r,z)).val.2.2.len=H r z.len := by
  have same := congrArg (fun b : Bill LocalValue=>b.val) (compiled_run r z)
  dsimp only [Bill.pass,Bill.pay] at same
  have fuel:=DFTModelCacheNatDispatch.fuel_value instructions
    (UniformGreedyColorMachine.runtimeBudget z.len) (run initializeProgram (r,z)).val
  have h:=DFTModelCacheNatDispatch.trajectory_lengths instructions
    (run initializeProgram (r,z)).val (UniformGreedyColorMachine.runtimeBudget z.len)
  have regs : (run initializeProgram (r,z)).val.2.1.len=824 := by rw [initialize_value];rfl
  have heap : (run initializeProgram (r,z)).val.2.2.len=H r z.len := by rw [initialize_value];rfl
  exact ⟨(congrArg (fun v : LocalValue=>v.2.1.len) (same.trans fuel)).trans (h.1.trans regs),
    (congrArg (fun v : LocalValue=>v.2.2.len) (same.trans fuel)).trans (h.2.trans heap)⟩

private theorem read_colors {M : ℕ} (r : ℕ) (z : Tape Row.T) (v : LocalValue)
    (u : UniformMachine.State) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (length : v.2.2.len=H r z.len) (rep : Represents v u)
    (colors : UniformGreedyColorMachine.Colors E (C z.len) M u) :
    (run extract ((r,z),v)).val.len=M ∧
    ∀i : Fin M,(run extract ((r,z),v)).val.look i.val 0=UniformColoring.greedy E 11 M i.val := by
  rw [extract_value]
  refine ⟨rows.length,?_⟩
  intro i
  have index:i.val<z.len := rows.length.symm ▸ i.isLt
  rw [Tape.look_of_lt (Tape.tab z.len (fun j=>(v.2.2.look (C z.len+j) (0,0)).2)) 0 index]
  change (v.2.2.look (C z.len+i.val) (0,0)).2=_
  have inside:C z.len+i.val<v.2.2.len := by
    rw [length];unfold C H B U;omega
  have represented:=rep.heap (C z.len+i.val) inside
  rw [colors i i.isLt] at represented
  unfold cell ModelEquivalenceInterpreter.decodeNatCell at represented
  split at represented
  · cases represented
  · exact Option.some.inj represented

def workBound (r M : ℕ) := compiledWork r M+31*M+15
def peakBound (r M : ℕ) := max (compiledPeak r M) (max M (max 3 (C M+M)))

/-- A closed typed producer computes every color with the actual native51
program, then reads the produced color bank. Degree is unnecessary for
execution and exhausted palettes retain sentinel 11. Original Row3 labels,
including duplicates and zero coefficients, remain byte-for-byte in the input. -/
theorem execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hr : InRange r E) : ∃t u,
    t≤UniformGreedyColorMachine.runtimeBudget z.len ∧
    UniformMachine.BoundedExecution UniformGreedyColorMachine.program n x
      (B r z.len) (sourceState r z) t u ∧ u.pc=50 ∧
    (run program (r,z)).valid ∧ (run program (r,z)).val.1=(r,z) ∧
    Represents (run program (r,z)).val.2.1 u ∧
    (run program (r,z)).val.2.2.len=M ∧
    (∀i : Fin M,(run program (r,z)).val.2.2.look i.val 0=UniformColoring.greedy E 11 M i.val) ∧
    (∀i : Fin M,(run program (r,z)).val.2.2.look i.val 0≤11) ∧
    (run program (r,z)).work≤workBound r z.len ∧
    (run program (r,z)).peak≤peakBound r z.len := by
  obtain ⟨t,u,time,actual,pc,colors,valid,rep,work,peak⟩:=compiled_execution r n x z E rows hr
  have read:=read_colors r z (run compiled (r,z)).val u E rows (compiled_lengths r z).2 rep colors
  have readBounds:=extract_bounds r z (run compiled (r,z)).val
  rw [program_run,colored_run]
  refine ⟨t,u,time,actual,pc,⟨valid,readBounds.1⟩,rfl,rep,read.1,read.2,?_,?_,?_⟩
  · intro i
    change (run extract ((r,z),(run compiled (r,z)).val)).val.look i.val 0≤11
    rw [read.2]
    exact UniformGreedyColorMachine.greedy_le E M i.val
  · change (run compiled (r,z)).work+(run extract ((r,z),(run compiled (r,z)).val)).work+5+2≤_
    rw [readBounds.2.1]
    unfold workBound
    omega
  · change max (run compiled (r,z)).peak (run extract ((r,z),(run compiled (r,z)).val)).peak≤_
    exact max_le_max peak readBounds.2.2

/-- The paper's degree-six cache condition gives eleven proper matching layers.
It is a theorem about the SAME computed native colors, not supplied colors. -/
theorem degree_six {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hr : InRange r E) (degree : UniformColoring.DegreeBound E 6) :
    (run program (r,z)).valid ∧ (run program (r,z)).val.2.2.len=M ∧
    (∀i : Fin M,(run program (r,z)).val.2.2.look i.val 0=UniformColoring.coloring E 6 i) ∧
    (∀i : Fin M,(run program (r,z)).val.2.2.look i.val 0<11) ∧
    (∀i j : Fin M,i≠j→(run program (r,z)).val.2.2.look i.val 0=
      (run program (r,z)).val.2.2.look j.val 0→¬UniformColoring.Conflict (E i) (E j)) := by
  obtain ⟨_,_,_,_,_,valid,_,_,length,values,_,_,_⟩:=execution r n x z E rows hr
  refine ⟨valid,length,?_,?_,?_⟩
  · intro i
    simpa only [UniformColoring.coloring] using values i
  · intro i
    rw [values i]
    exact UniformColoring.coloring_bound E degree (by decide) i
  · intro i j different same
    rw [values i,values j] at same
    exact UniformColoring.same_color_disjoint E degree (by decide) i j different same

end
end ExactFourierCircuits.DFTModelCacheColor
