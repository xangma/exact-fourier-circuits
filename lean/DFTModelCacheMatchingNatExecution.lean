import DFTModelCacheMatchingNatSource
import DFTModelCacheMatchingNatBounds
import DFTModelCacheNatDispatchBounded

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open UniformMatchingAxisTableMachine
noncomputable section

def runtimeProgram : Prog false Input w :=
  nat .add (nat .add (nat .mul (.atom (.lit 17)) radix)
    (nat .mul (.atom (.lit 8)) count)) (.atom (.lit 21))

def compiled : Prog false Input Local :=
  .comp (.fork runtimeProgram initializeProgram)
    (DFTModelCacheNatDispatch.fuelProgram instructions)

private theorem runtime_arithmetic (r M : ℕ) :
    max (max (max (max 17 (17*r)) (max (max 8 M) (8*M))) (17*r+8*M))
      (max 21 (17*r+8*M+21))=17*r+8*M+21 := by omega

theorem runtimeProgram_run (r : ℕ) (z : Tape Row.T) :
    run runtimeProgram (r,z)=⟨runtime r z.len,19,runtime r z.len,True⟩ := by
  simp [runtimeProgram,radix,count,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,runtime]
  omega

attribute [local irreducible] Code.run

theorem compiled_run (r : ℕ) (z : Tape Row.T) :
    run compiled (r,z)=((run initializeProgram (r,z)).pass
      (fun v=>run (DFTModelCacheNatDispatch.fuelProgram instructions) (runtime r z.len,v))).pay
        21 (runtime r z.len) := by
  rw [compiled,comp_run,fork_run,runtimeProgram_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,true_and,and_true]
  congr 1 <;> omega

theorem running_safety (r n : ℕ) (x : Fin n→ℂ) (M : ℕ) :
    DFTModelCacheNatDispatch.RunningSafety instructions n x (wordBound r M)
      (wordBound r M+1) 862 (heapSize r M) := by
  intro v s u i rep regs heap before after selected step
  have member: i∈instructions := List.mem_of_getElem? selected
  have foot:=instructions_footprint i member
  have large:862≤wordBound r M := by unfold wordBound;omega
  refine ⟨fits foot regs heap rep before,?_⟩
  apply peak (DFTModelCacheNatDispatch.native instructions) foot large regs heap rep before after
    (DFTModelCacheNatDispatch.native_at instructions v s rep i selected) step

theorem halt_safety (r M : ℕ) :
    DFTModelCacheNatDispatch.HaltSafety (wordBound r M) (wordBound r M+1)
      862 (heapSize r M) := by
  intro v s rep regs heap bound
  refine ⟨by omega,?_,?_,by rw [heap];exact le_rfl,trivial⟩
  · rw [rep.pc];have :=bound.1;omega
  · rw [regs];unfold wordBound;omega

/-- Actual typed execution from raw rows, with no supplied permutation, fuel,
initialized bank, Fits trajectory, or intended final state. -/
theorem compiled_execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hm : Matching E) (hr : InRange r E) : ∃u,
    UniformMachine.BoundedExecution UniformMatchingAxisTableMachine.program n x
      (wordBound r z.len) (sourceState r z) (runtime r M) u ∧
    (run compiled (r,z)).valid ∧ Represents (run compiled (r,z)).val u ∧
    Bank (P z.len) (ordered r E) u ∧ Bank (W r z.len) (widths r M) u ∧
    AxisRow (A r z.len) r M (W r z.len) (P z.len) u ∧
    (run compiled (r,z)).work≤200025+204*heapSize r z.len+
      runtime r M*(35*(862+heapSize r z.len)+435) ∧
    (run compiled (r,z)).peak≤ max (2*heapSize r z.len+2000) (runtime r M) := by
  obtain ⟨u,actual,_,perm,widths,axis⟩:=native_execution r n x z E rows hm hr
  have mapped:DFTModelCacheNatDispatch.native instructions=
      UniformMatchingAxisTableMachine.program := instructions_native
  have nativeRun:UniformMachine.BoundedExecution (DFTModelCacheNatDispatch.native instructions)
      n x (wordBound r z.len) (sourceState r z) (runtime r z.len) u := by
    simpa only [mapped,rows.length] using actual
  have init:=initialize_bounds r z
  have typed:=DFTModelCacheNatDispatch.bounded_source instructions n x
    (wordBound r z.len) (wordBound r z.len+1) 862 (heapSize r z.len)
    (sourceState r z) u (runtime r z.len) nativeRun
    (run initializeProgram (r,z)).val (initialized_represents r z)
    (by rw [initialize_value];rfl) (by rw [initialize_value];rfl)
    (by omega) (running_safety r n x z.len) (halt_safety r z.len)
  rw [compiled_run]
  refine ⟨u,actual,?_,?_,perm,widths,axis,?_,?_⟩
  · exact ⟨init.1,typed.1⟩
  · exact typed.2.1
  · have work:=typed.2.2.1
    rw [instructions_length] at work
    have coeff : 35*(862+heapSize r z.len)+105+6*55=
        35*(862+heapSize r z.len)+435 := by omega
    rw [coeff] at work
    rw [←rows.length]
    change (run initializeProgram (r,z)).work+_+21≤_
    dsimp only at work ⊢
    omega
  · have pk:=typed.2.2.2
    change max (max (run initializeProgram (r,z)).peak _) (runtime r z.len)≤_
    rw [←rows.length]
    dsimp only at pk ⊢
    have room : wordBound r z.len+1≤2*heapSize r z.len+2000 := by
      unfold heapSize;omega
    exact max_le (max_le (init.2.2.trans (le_max_left _ _))
      (pk.trans (max_le (le_max_right _ _) (room.trans (le_max_left _ _)))))
      (le_max_right _ _)

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
