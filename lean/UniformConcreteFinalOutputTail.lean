import UniformFinalOutputTail
import UniformFinalMovementGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformConcreteFinalOutputTail
open UniformMachine UniformFinalNumericJoin UniformSequentialAssembly UniformSequentialExecution
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants
abbrev volume (n:ℕ):ℕ:=UniformInitialPreparation.len n
def target (n:ℕ):ℕ:=3*UniformJointAllocation.slab c n
abbrev budget (n:ℕ):ℕ:=UniformJointAllocation.envelope c n

/-- All output-header and chirp-loop word premises follow from the actual
retained metadata and the canonical final movement allocation. -/
lemma fits {n:ℕ}(hn:0<n)(s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s):
 64≤budget n ∧ s.natReg 102+2*s.natReg 101+2*s.natReg 103+7≤budget n ∧
 UniformInitialPreparation.ell n+7+2*n≤budget n ∧ target n+volume n≤budget n:=by
 dsimp only[budget,target,volume]
 have low:=UniformFinalRoleGeometry.header_low hn s metadata
 have geometry:=UniformFinalMovementGeometry.fits hn
 have chirp:=low
 rw[metadata.saved.count,metadata.saved.inputLength,metadata.saved.workingLength] at chirp
 exact ⟨geometry.code,by omega,by omega,geometry.target⟩

/-- Execute the real output-header11 and output18 stages at the canonical
budget. No small-word, chirp-placement or spectrum-placement premise remains. -/
theorem execution {n:ℕ}[NeZero (volume n)](hn:0<n)(x:Fin n→ℂ)(s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (operands:UniformInitialPreparation.Operands n x s)
 (transform:s.natReg 6025=target n)
 (values:UniformChirpOutputMachine.Values (volume n) (target n) (scalars (volume n) (target n) s) s)
 (spectrum:UniformChirpOutputMachine.FinalSpectrum x (scalars (volume n) (target n) s))
 (wb:WordBound (budget n) s):∃u,
 LocalStages n (budget n) x [natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]
 s (13*n+18) u ∧ ComputesDFT n x u ∧ u.rootOrders=s.rootOrders ∧ u.pc=17:=by
 have safe:=fits hn s metadata
 exact UniformFinalOutputTail.execution hn rfl x s metadata operands transform values spectrum
  safe.1 safe.2.1 safe.2.2.1 safe.2.2.2 wb

/-- The three genuine transform heap postconditions and actual copies produce
both the final spectrum and the continuous charged output stages. -/
theorem of_three_transform_heaps {n:ℕ}[NeZero (volume n)](hn:0<n)
 (AP BP:Fin (volume n)≃Fin (volume n))(x:Fin n→ℂ)(AK A DK Q:ℕ)
 (kernelIn kernelOut dataIn dataOut productOut thirdIn thirdOut finalOut:State)
 (kernelInput:NumericValues AK (fun i=>kernel (n:=n) (AP i)) kernelIn)
 (kernelRun:HeapTransform AP BP AK DK kernelIn kernelOut)
 (kernelTags:∀i,(scalars (volume n) DK kernelOut i).dependent=false)
 (kernelSaved:∀i:Fin (volume n),dataOut.scalarHeap (Q+i.val)=kernelOut.scalarHeap (DK+i.val))
 (dataInput:NumericValues A (fun i=>data x (AP i)) dataIn)
 (dataRun:HeapTransform AP BP A A dataIn dataOut)
 (pointwise:NumericValues A (fun i=>(scalars (volume n) A dataOut i).value*
  (scalars (volume n) Q dataOut i).value) productOut)
 (thirdReindex:∀i:Fin (volume n),thirdIn.scalarHeap (A+i.val)=
  productOut.scalarHeap (A+(BP.symm (AP i)).val))
 (thirdRun:HeapTransform AP BP A A thirdIn thirdOut)
 (finalReindex:∀i:Fin (volume n),finalOut.scalarHeap (target n+i.val)=
  thirdOut.scalarHeap (A+(BP.symm i).val))
 (metadata:UniformPermutationInversePreparation.Metadata n finalOut)
 (operands:UniformInitialPreparation.Operands n x finalOut)
 (transform:finalOut.natReg 6025=target n)(wb:WordBound (budget n) finalOut):
 (∀i:Fin (volume n),dataOut.scalarHeap (Q+i.val)=
  some (UniformPairMachine.prepared (kernelSpectrum (n:=n) (BP i)))) ∧ ∃u,
 LocalStages n (budget n) x [natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]
 finalOut (13*n+18) u ∧ ComputesDFT n x u ∧ u.rootOrders=finalOut.rootOrders ∧ u.pc=17:=by
 have joined:=three_transform_heaps AP BP x AK A DK Q (target n)
  kernelIn kernelOut dataIn dataOut productOut thirdIn thirdOut finalOut
  kernelInput kernelRun kernelTags kernelSaved dataInput dataRun pointwise thirdReindex thirdRun finalReindex
 exact ⟨joined.1,execution hn x finalOut metadata operands transform joined.2.1 joined.2.2 wb⟩

end
end ExactFourierCircuits.UniformConcreteFinalOutputTail
