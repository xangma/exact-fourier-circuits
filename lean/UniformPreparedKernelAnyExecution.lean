import UniformInitializedPreparedKernel
import UniformExecutedTaggedBank
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedKernelAnyExecution
open UniformMachine
open UniformConditionalKernelLayout (Context)
noncomputable section

/-- The additive tag theorem applies to any actual execution of the same
literal initialized kernel, by deterministic machine execution. -/
theorem execution {W F R n ticks:ℕ} (child:Program) (g:Context W F R) (cost:ℕ→ℕ)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s t:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (root:UniformPreparedSectorLoop.RootBody child W n g.inverse.layout.B F R cost x)
 (prepared:∀r,r<W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0<W) (code:child.length+647≤g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s)
 (run:BoundedExecution (UniformInitializedKernelExecution.programFor child W) n x g.metadata.B s ticks t):
 ∀r,r<W→∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
 (t.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.dependent=some false:=by
 obtain ⟨z,time,actual,_cheap,_zp,tags,_outputs,_roots⟩:=
  UniformInitializedPreparedKernel.execution child g cost v x s input banks source constants root prepared positive code pc wb
 have sameProgram:BoundedExecution (UniformInitializedKernelExecution.programFor child W) n x g.metadata.B s time z:=by
  simpa only[UniformInitializedPreparedKernel.program_same] using actual
 have same:t=z:=(run.executes.deterministic sameProgram.executes).2
 subst t
 exact tags

lemma projected_false {A V r j:ℕ} {s:State}
 (h:(s.scalarHeap (A+r*V+j)).map Scalar.dependent=some false):
 (UniformExecutedTaggedBank.values A V s r j).dependent=false:=by
 unfold UniformExecutedTaggedBank.values
 cases q:s.scalarHeap (A+r*V+j) with
 | none=>simp[q] at h
 | some z=>simpa only[q,Option.map_some,Option.getD_some,Option.some.injEq] using h
end
end ExactFourierCircuits.UniformPreparedKernelAnyExecution
