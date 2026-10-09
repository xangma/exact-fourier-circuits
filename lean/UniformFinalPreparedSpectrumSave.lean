import UniformFinalMovementFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPreparedSpectrumSave
open UniformMachine UniformFinalNumericJoin UniformFinalMovementFrame
noncomputable section

/-- Save the actual prepared first-transform role, including its false tag.
The only spectrum premise is the real first-clock numeric and tag output. -/
theorem execution {n L S B:ℕ}(x:Fin n→ℂ)(f:Fin L→ℂ)(s:State)
 (input:NumericValues (S+L) f s)
 (tags:∀j,(scalars L (S+L) s j).dependent=false)
 (width:s.natReg 103=L)(base:s.natReg 6026=S)(storage:s.natReg 7300=Q n)
 (separate:Q n+L≤S+L)(sourceFit:S+L+L≤B)(storageFit:Q n+L≤B)
 (code:15≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution UniformKernelSpectrumCopy.program n x B s (7*L+9) u∧
 (∀j,u.scalarHeap (Q n+j.val)=some (UniformPairMachine.prepared (f j)))∧
 Frame n s u∧UniformKernelSpectrumCopy.Frame (Q n) L s u∧u.pc=14:=by
 obtain ⟨u,run,copied,frame,upc⟩:=UniformKernelSpectrumCopy.execution x
  (scalars L (S+L) s) s (numeric_present input) width base storage
  separate sourceFit storageFit code pc wb
 have same:∀j:Fin L,u.scalarHeap (Q n+j.val)=s.scalarHeap (S+L+j.val):=by
  intro j;exact (copied j).trans (numeric_present input j).symm
 exact ⟨u,run,prepared_copy f s u input tags same,
  UniformFinalMovementFrame.Frame.copy frame,frame,upc⟩

end
end ExactFourierCircuits.UniformFinalPreparedSpectrumSave
