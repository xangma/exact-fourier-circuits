import UniformCacheLowWholeExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheLowRetention
open UniformMachine UniformAllAxisSeedPreparation
noncomputable section
lemma saved_same {n:ℕ} {s u:State}
 (old:UniformPermutationInversePreparation.Metadata n s)
 (new:UniformPermutationInversePreparation.Metadata n u):
 ∀r,100 ≤ r → r ≤ 106→u.natReg r=s.natReg r:=by
 intro r lo hi
 interval_cases r
 all_goals first
 | exact new.saved.nextPrime.trans old.saved.nextPrime.symm
 | exact new.saved.inputLength.trans old.saved.inputLength.symm
 | exact new.saved.count.trans old.saved.count.symm
 | exact new.saved.workingLength.trans old.saved.workingLength.symm
 | exact new.saved.masterRoot.trans old.saved.masterRoot.symm
 | exact new.saved.copyAddress.trans old.saved.copyAddress.symm
 | exact new.saved.copyLength.trans old.saved.copyLength.symm
lemma Frame.preserved {n:ℕ} {s u:State} (hn:0<n) (frame:Frame n s u)
 (saved:∀r,100 ≤ r → r ≤ 106→u.natReg r=s.natReg r)
 (outputs:u.outputs=s.outputs) (roots:u.rootOrders=s.rootOrders):
 UniformSeedRankCrossPreparation.PreservedFrame n s u:=by
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2
 change axisBase n (axisCount n)≤z n∧directoryBase n+2*axisCount n≤z n at word
 exact ⟨fun a ha=>frame.nat a (ha.trans_le word.2),
  fun a ha=>frame.scalar a (ha.trans_le word.1),saved,outputs,roots⟩
lemma Frame.alpha_copied {n:ℕ} {s u:State} (hn:0<n) (frame:Frame n s u)
 (j:Fin (UniformInitialPreparation.len n)):
 u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=
 s.scalarHeap (UniformInputPermutationPreparation.destination n+j.val):=by
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2.1
 have global:UniformGlobalLocalPreparation.globalEnd n≤axisBase n (axisCount n):=by
  unfold axisBase UniformLocalSeedTableMachine.poolBase;omega
 apply frame.scalar
 apply lt_of_lt_of_le _ (global.trans word)
 unfold UniformGlobalLocalPreparation.globalEnd
 have:=j.isLt
 omega
lemma Frame.beta_inverse {n:ℕ} {s u:State} (hn:0<n) (frame:Frame n s u)
 (old:UniformGlobalNatPreparation.PermutationBank (UniformInitialPreparation.len n)
  (UniformPermutationInversePreparation.inverseBase n) s.natHeap
  (UniformCRTTraversalCycle.betaPermutation n).symm):
 UniformGlobalNatPreparation.PermutationBank (UniformInitialPreparation.len n)
  (UniformPermutationInversePreparation.inverseBase n) u.natHeap
  (UniformCRTTraversalCycle.betaPermutation n).symm:=by
 intro j
 apply Eq.trans _ (old j)
 apply frame.nat
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2.2
 apply lt_of_lt_of_le _ word
 unfold directoryBase
 have:=j.isLt
 omega
lemma Frame.permutation {n L base:ℕ} {s u:State} (frame:Frame n s u)
 (bound:base+L≤z n) (p:Equiv.Perm (Fin L))
 (old:UniformGlobalNatPreparation.PermutationBank L base s.natHeap p):
 UniformGlobalNatPreparation.PermutationBank L base u.natHeap p:=by
 intro j
 exact (frame.nat _ (by have:=j.isLt;omega)).trans (old j)

lemma Frame.normal_alpha {n:ℕ} {s u:State} (hn:0<n) (frame:Frame n s u)
 (j:Fin (UniformInitialPreparation.len n)):
 u.natHeap (UniformInitialPreparation.alphaBase n+j.val)=
 s.natHeap (UniformInitialPreparation.alphaBase n+j.val):=by
 have fit:=(UniformInitialPreparation.word_setup hn).2.1
 change 128+10*UniformInitialPreparation.ell n+4*UniformInitialPreparation.len n≤z n at fit
 apply frame.nat
 unfold UniformInitialPreparation.alphaBase UniformCRTTraversalMachine.alphaBase
  UniformCRTTraversalMachine.digitBase
 have:=j.isLt
 omega
lemma Frame.normal_beta {n:ℕ} {s u:State} (hn:0<n) (frame:Frame n s u)
 (j:Fin (UniformInitialPreparation.len n)):
 u.natHeap (UniformInitialPreparation.betaBase n+j.val)=
 s.natHeap (UniformInitialPreparation.betaBase n+j.val):=by
 have fit:=(UniformInitialPreparation.word_setup hn).2.1
 change 128+10*UniformInitialPreparation.ell n+4*UniformInitialPreparation.len n≤z n at fit
 apply frame.nat
 unfold UniformInitialPreparation.betaBase UniformCRTTraversalMachine.betaBase
  UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase
 have:=j.isLt
 omega
lemma Frame.operands {n:ℕ} {x:Fin n→ℂ} {s u:State}
 (hn:0<n) (frame:Frame n s u) (old:UniformInitialPreparation.Operands n x s):
 UniformInitialPreparation.Operands n x u:=by
 apply UniformGlobalLocalPreparation.operands_transport_below old
 intro a ha
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2.1
 have global:UniformGlobalLocalPreparation.globalEnd n≤axisBase n (axisCount n):=by
  unfold axisBase UniformLocalSeedTableMachine.poolBase;omega
 exact frame.scalar a (ha.trans_le (global.trans word))

/-- The added frame applies to any actual run of the unchanged4654 program.
Determinism identifies it with the fully constructed charged execution. -/
theorem execution_frame (c:UniformJointAllocation.Constants) (n:ℕ) (hn:0<n)
 (x:Fin n→ℂ) (s u:State) (ticks:ℕ)
 (core:UniformAxisCachePreparationRetention.Core n x s)
 (slab:s.natReg 6020=UniformJointAllocation.slab c n)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=0) (wb:WordBound (UniformJointAllocation.envelope c n) s)
 (run:BoundedExecution UniformAxisCacheWholeProgram.program n x
  (UniformJointAllocation.envelope c n) s ticks u):
 Frame n s u ∧ UniformAllAxisSeedPreparation.ProtectedFrame n s u:=by
 obtain ⟨v,t,actual,_,_,out,frame⟩:=UniformAxisCacheWholeExecution.execution_low c n hn x s core slab bank pc wb
 have same:=(actual.executes.deterministic run.executes).2
 subst u
 exact ⟨frame,(frame.preserved hn (saved_same core.metadata out.input.metadata) out.outputs out.roots).protected⟩
end
end ExactFourierCircuits.UniformCacheLowRetention
