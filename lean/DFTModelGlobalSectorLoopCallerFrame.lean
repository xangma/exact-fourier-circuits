import DFTModelGlobalSectorLoopPatches
set_option autoImplicit false
/-! Original loop control and the unchanged recursive child preserve the real
sector-count register and later caller headers. This adds no source operation. -/
namespace ExactFourierCircuits.DFTModelGlobalSectorLoopCallerFrame
open UniformMachine UniformAssembly UniformSyntacticNatFrame UniformTensorMonomialMachine
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program UniformRecursiveSavingProgram.program

def Safe (i : Instruction) : Prop := match natDst i with
 | none=>True
 | some d=>d≠464 ∧(d<5900∨5910<d)
instance (i : Instruction) : Decidable (Safe i) := by unfold Safe;split <;>infer_instance
lemma checked (p : Program) (h : p.all (fun i=>decide (Safe i))=true) :
 ∀i∈p,Safe i := fun i hi=>of_decide_eq_true ((List.all_eq_true.mp h) i hi)
lemma safe_avoids {p : Program} (h : ∀i∈p,Safe i) (j : ℕ)
 (kept : j=464∨5900≤j∧j≤5910) : Avoids p j := by
 intro i hi bad
 have hs:=h i hi
 rw[Safe,bad] at hs
 omega
lemma boot_safe : ∀i∈UniformSameProgramSectorLoop.boot.map Op.code,Safe i :=
 checked _ (by decide +kernel)
lemma setup_safe : ∀i∈UniformSameProgramSectorLoop.setup.map Op.code,Safe i :=
 checked _ (by decide +kernel)
lemma finish_safe : ∀i∈UniformSameProgramSectorLoop.finish.map Op.code,Safe i :=
 checked _ (by decide +kernel)
lemma branch_safe (L : ℕ) : ∀i∈[Instruction.branchLT 5892 5890 8 (L+19)],Safe i :=
 by
 intro i hi
 have eq:=List.mem_singleton.mp hi
 subst i
 trivial
lemma tail_safe : ∀i∈[Instruction.jump 7,.halt],Safe i :=checked _ (by decide)

/-- Static destinations of the actual astronomical child are used symbolically;
neither fixed seed/unit payload is expanded. -/
theorem program_avoids (j : ℕ) (kept : j=464∨5900≤j∧j≤5910) :
 Avoids UniformSameProgramSectorLoop.program j := by
 have child:=UniformRecursiveStaticNatFrame.program_avoids j (by omega)
 have moved:=avoids_map_relocate _ 17 (17+UniformRecursiveSavingProgram.program.length) j child
 rw[UniformSameProgramSectorLoop.program,UniformSameProgramSectorLoop.assembly]
 exact avoids_append _ _ j
  (avoids_append _ _ j
   (avoids_append _ _ j
    (avoids_append _ _ j
     (avoids_append _ _ j (safe_avoids boot_safe j kept)
      (safe_avoids (branch_safe _) j kept)) (safe_avoids setup_safe j kept)) moved)
   (safe_avoids finish_safe j kept)) (safe_avoids tail_safe j kept)

/-- Holds for the SAME original complete loop witness returned by SectorLoop4. -/
theorem execution_nat {n B ticks : ℕ} {x : Fin n→ℂ} {s u : State}
 (run : BoundedExecution UniformSameProgramSectorLoop.program n x B s ticks u)
 (j : ℕ) (kept : j=464∨5900≤j∧j≤5910) : u.natReg j=s.natReg j :=
 boundedExecution_preserves (program_avoids j kept) run

open DFTModelGlobalSectorLoop

theorem Result.count {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace)
 (count : s.natReg 464=xs.length) : u.natReg 464=xs.length :=
 (execution_nat h.actual 464 (Or.inl rfl)).trans count

theorem Result.high {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace)
 (j : ℕ) (lo : 5900≤j) (hi : j≤5910) :
 u.natReg j=s.natReg j ∧u0.natReg j=s0.natReg j :=
 ⟨execution_nat h.actual j (Or.inr ⟨lo,hi⟩),execution_nat h.baseline j (Or.inr ⟨lo,hi⟩)⟩

end
end ExactFourierCircuits.DFTModelGlobalSectorLoopCallerFrame
