import UniformSequentialExecution
import UniformFinalOuterHeaders
import UniformFinalNumericJoin

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOutputTail
open UniformMachine UniformSequentialAssembly UniformSequentialExecution
noncomputable section

/-- The real two-stage output tail restores its arguments from saved metadata,
then emits the DFT. Its normalization and chirp values come from the retained
startup operands, and its spectrum comes from the three actual transforms. -/
theorem execution {n L B T:ℕ}[NeZero L](hn:0<n)
 (selected:L=UniformInitialPreparation.len n)(x:Fin n→ℂ)(s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (operands:UniformInitialPreparation.Operands n x s)
 (transform:s.natReg 6025=T)
 (values:UniformChirpOutputMachine.Values L T (UniformFinalNumericJoin.scalars L T s) s)
 (spectrum:UniformChirpOutputMachine.FinalSpectrum x (UniformFinalNumericJoin.scalars L T s))
 (small:64≤B)(low:s.natReg 102+2*s.natReg 101+2*s.natReg 103+7≤B)
 (chirp:UniformInitialPreparation.ell n+7+2*n≤B)(data:T+L≤B)
 (wb:WordBound B s):∃u,
 LocalStages n B x [natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]
 s (13*n+18) u∧ComputesDFT n x u∧u.rootOrders=s.rootOrders∧u.pc=17:=by
 let s0:State:={s with pc:=0}
 have wb0:WordBound B s0:=UniformMachine.changePC_bound B s 0 wb (by omega)
 have safe:=UniformFinalOuterHeaders.output_safe s0 B (by exact (wb.2.1 6025)) low
 have header:=UniformSequentialAssembly.nat_execution UniformFinalOuterHeaders.output x s0 rfl wb0
  (by rw[UniformFinalOuterHeaders.output_length];omega) safe.1 safe.2
 let h:=UniformNatBlockMachine.applyBlock UniformFinalOuterHeaders.output s0
 let h0:State:={h with pc:=0}
 have fields:=UniformFinalOuterHeaders.output_values s metadata
 have heap:h0.scalarHeap=s.scalarHeap:=rfl
 have normalization:h0.scalarHeap (UniformNormalizationPreparation.normBase n)=
  some (UniformPairMachine.prepared (L:ℂ)⁻¹):=by
  rw[heap,selected]
  exact operands.normalization
 have hL:0<L:=by simpa only[selected] using UniformWorkingLength.workingLength_pos hn
 have hnL:2*n≤L:=by simpa only[selected] using UniformWorkingLength.workingLength_lower n
 have coefficients:UniformChirpOutputMachine.Coefficients n (UniformInitialPreparation.ell n+7)
  (OAI.ExactFourier.zeta (2*n)) h0:=by
  intro j hj
  exact (operands.chirps j hj).1
 obtain ⟨u,run,dft,frame,pc⟩:=UniformChirpOutputMachine.output_execution_dft hn hL hnL x B
  (UniformInitialPreparation.ell n+7) T (UniformNormalizationPreparation.normBase n)
  (UniformFinalNumericJoin.scalars L T s) h0 rfl fields.1
  (fields.2.1.trans selected.symm) fields.2.2.1 (fields.2.2.2.1.trans transform)
  fields.2.2.2.2 normalization coefficients
  values spectrum small chirp data (UniformMachine.changePC_bound B h 0 header.final_bound (by omega))
 refine ⟨u,?_,dft,frame.2.2.1,pc⟩
 have localRun:LocalStages n B x [natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]
  s (UniformFinalOuterHeaders.output.length+1+(13*n+6+0)) u:=
  .cons header (.cons run (.nil u run.final_bound))
 convert localRun using 1
 rw[UniformFinalOuterHeaders.output_length]
 omega

end
end ExactFourierCircuits.UniformFinalOutputTail
