import UniformDiagonalReturnCore
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDiagonalDependencyTags
open UniformMachine
open UniformGlobalDiagonalChildPrefix (Context phaseValues)
noncomputable section

/-- The actual diagonal is multiplication by prepared coefficients; it carries
the source tag exactly, including when a numerical value happens to be zero. -/
lemma phase {W:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (r:ℕ) (j:Fin c.packing.volume):
 (phaseValues c v r j).dependent=(v r j.val).dependent:=rfl

/-- A supplement for any actual147 execution, derived from its exact tagged
output theorem and determinism of the literal machine. -/
theorem execution {W n ticks:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s u:State)
 (ready:UniformDiagonalReturnCore.Ready c v s) (code:147≤c.metadata.B)
 (pc:s.pc=0) (wb:WordBound c.metadata.B s)
 (run:BoundedExecution (UniformGlobalDiagonalReturn.programFor W) n x c.metadata.B s ticks u):
 ∀r,r<W→∀j:Fin c.packing.volume,
 (u.scalarHeap (c.tensor.source+r*c.tensor.volume+j.val)).map Scalar.dependent=some ((v r j.val).dependent):=by
 obtain ⟨z,actual,_zp,cells,_outputs,_roots,_scalar,_nat⟩:=
  UniformDiagonalReturnCore.execution c v x s ready code pc wb
 have same: u=z:=(run.executes.deterministic actual.executes).2
 subst u
 intro r hr j
 rw[cells r hr j]
 exact congrArg some (phase c v r j)

lemma all_prepared {W n ticks:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s u:State)
 (ready:UniformDiagonalReturnCore.Ready c v s) (code:147≤c.metadata.B)
 (pc:s.pc=0) (wb:WordBound c.metadata.B s)
 (run:BoundedExecution (UniformGlobalDiagonalReturn.programFor W) n x c.metadata.B s ticks u)
 (input:∀r,r<W→∀j,j<c.tensor.volume→(v r j).dependent=false):
 ∀r,r<W→∀j:Fin c.packing.volume,
 (u.scalarHeap (c.tensor.source+r*c.tensor.volume+j.val)).map Scalar.dependent=some false:=by
 intro r hr j
 rw[execution c v x s u ready code pc wb run r hr j]
 rw[input r hr j.val (by rw[←c.volume];exact j.isLt)]
end
end ExactFourierCircuits.UniformDiagonalDependencyTags
