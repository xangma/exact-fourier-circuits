import UniformFinalPhysicalTableInputs
import UniformFastPhysicalCRTCycle

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT permutations after (5.5), PDF p.22
(`eq:crt-fourier`), and §5.4 integer/address bounds, PDF p.24.

The produced physical CRT table and its protected-bank geometry refine the
paper's costed index permutations. Allocation addresses, headers and frames are
implementation bookkeeping rather than a separate paper argument.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPhysicalTableExecution
open UniformMachine UniformFastPhysicalCRTMachine UniformSelectedPhysicalCRT UniformCRTTraversalCycle
open UniformGlobalNatPreparation UniformFinalPhysicalTableGeometry UniformAxisCachePreparationRetention
open scoped BigOperators
noncomputable section

/-- The actual selected fast converter derives every digit and prefix weight
from the retained seed directory. Its two output banks use physical MSB order. -/
/- Paper stage: §5.2, linear CRT permutations after (5.5), PDF p.22: use actual retained radix/source tables and the proved <2L carry-visit bound. -/
theorem execution(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(args:Args (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s)
 (core:Core n x s)(wb:WordBound (UniformJointAllocation.envelope c n) s):∃ticks u,
 BoundedExecution UniformFastPhysicalCRTMachine.program n x (UniformJointAllocation.envelope c n) s ticks u∧
 ticks≤60*(len n+UniformAllAxisSeedPreparation.axisCount n+1)∧u.pc=52∧
 Args (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) u∧Constants u∧Frame s u∧
 UniformFastPhysicalCRTProgress.Outside (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s.natHeap u∧
 PermutationBank (len n) (addresses c n).physicalAlpha u.natHeap (physicalAlpha n)∧
 PermutationBank (len n) (addresses c n).inverseBeta u.natHeap (physicalBeta n).symm:=by
 let cast:Fin (∏i,radices n i)≃Fin (len n):=finCongr (UniformSelectedCRT.radices_product n)
 let A:Fin (∏i,radices n i)≃Fin (∏i,radices n i):=cast.trans (alphaPermutation n)|>.trans cast.symm
 let Q:Fin (∏i,radices n i)≃Fin (∏i,radices n i):=cast.trans (betaPermutation n)|>.trans cast.symm
 let R:=UniformPhysicalCRTCoordinates.rho (radices n) (UniformSelectedCRT.radix_pos n)
 have f:=fits c hn
 have ac:PermutationBank (∏i,radices n i) (addresses c n).alpha s.natHeap A:=by
  intro j
  simpa only[addresses,A,Equiv.trans_apply,Equiv.symm_apply_apply,cast,finCongr_apply,finCongr_symm,Fin.val_cast] using core.metadata.alpha (cast j)
 have bc:PermutationBank (∏i,radices n i) (addresses c n).beta s.natHeap Q:=by
  intro j
  simpa only[addresses,Q,Equiv.trans_apply,Equiv.symm_apply_apply,cast,finCongr_apply,finCongr_symm,Fin.val_cast] using core.metadata.beta (cast j)
 obtain ⟨ticks,u,run,cost,up,ua,uc,uf,uh,ap,bi⟩:=UniformFastPhysicalCRTCycle.execution (radices n)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn) (addresses c n) R A Q
  (fun j=>UniformFastPhysicalCRTArithmetic.rho_value _ _ j) x s pc
  (by simpa only[UniformSelectedCRT.radices_product] using args)
  (retained_directory n s core.seed) ac bc f.directory
  (by simpa only[UniformSelectedCRT.radices_product] using f.alpha)
  (by simpa only[UniformSelectedCRT.radices_product] using f.beta)
  (by simpa only[UniformSelectedCRT.radices_product] using f.alphaEnd.le)
  (by simpa only[UniformSelectedCRT.radices_product] using f.inverseEnd.le)
  f.work (by simpa only[UniformSelectedCRT.radices_product] using f.volume) f.code wb
 refine ⟨ticks,u,?_,?_,up,?_,uc,uf,?_,?_,?_⟩
 · simpa only[UniformSelectedCRT.radices_product] using run
 · simpa only[UniformSelectedCRT.radices_product] using cost
 · simpa only[UniformSelectedCRT.radices_product] using ua
 · simpa only[UniformSelectedCRT.radices_product] using uh
 · intro p
   have h:=ap (cast.symm p)
   simpa only[cast,A,R,physicalAlpha,rho,physicalOrdinal,ordinalEquiv,
    UniformPhysicalCRTCoordinates.rho,Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply,finCongr_apply,finCongr_symm,Fin.cast_cast,Fin.cast_eq_self,Fin.val_cast] using h
 · intro p
   have h:=bi (cast.symm p)
   simpa only[cast,Q,R,physicalBeta,rho,physicalOrdinal,ordinalEquiv,
    UniformPhysicalCRTCoordinates.rho,Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply,Equiv.symm_apply_apply,finCongr_apply,finCongr_symm,Fin.cast_cast,Fin.cast_eq_self,Fin.val_cast] using h

lemma below{c:UniformJointAllocation.Constants}{n:ℕ}(hn:0<n){s u:State}
 (h:UniformFastPhysicalCRTProgress.Outside (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s.natHeap u)
 (q:ℕ)(hq:q<(addresses c n).physicalAlpha):u.natHeap q=s.natHeap q:=by
 have f:=fits c hn
 have ae:=f.alphaEnd
 have ie:=f.inverseEnd
 exact h q (Or.inl hq) (Or.inl (by omega)) (Or.inl (by omega))

lemma retained_core(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s u:State)
 (core:Core n x s)(frame:Frame s u)
 (outside:UniformFastPhysicalCRTProgress.Outside (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s.natHeap u):
 Core n x u:=by
 have arithmetic:=UniformJointAllocation.actual_arithmetic c n hn
 dsimp only at arithmetic
 have low:UniformAxisCacheSelectedPreparation.natAt c n 0≤(addresses c n).physicalAlpha:=by
  simp only[UniformAxisCacheSelectedPreparation.natAt,UniformJointCacheAllocation.offsetSum,
   Finset.range_zero,Finset.sum_empty,Nat.add_zero,UniformJointCacheAllocation.natStart,
   addresses,UniformKernelSpectrumStorage.alphaBase,UniformJointCacheAllocation.ell]
  omega
 apply UniformAxisCachePreparationRetention.transport c n 0 hn x s u core
 · exact ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
 · intro q hq;exact below hn outside q (hq.trans_le low)
 · intro q hq;exact frame.natReg q (Or.inl (by omega))

lemma retained_data(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n){x:Fin n→ℂ}{s u:State}
 (data:UniformFinalStartupData.Data n x s)(frame:Frame s u)
 (outside:UniformFastPhysicalCRTProgress.Outside (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s.natHeap u):
 UniformFinalStartupData.Data n x u:=by
 have directory:=nat_below c hn
 refine ⟨fun j=>(congrFun frame.scalarHeap _).trans (data.gathered j),?_,frame.roots.trans data.roots,frame.outputs.trans data.outputs⟩
 intro j
 have hj:j.val<len n:=j.isLt
 have endEq:UniformPermutationInversePreparation.inverseBase n+len n=UniformAllAxisSeedPreparation.directoryBase n:=rfl
 exact (below hn outside _ (by omega)).trans (data.inverse j)

lemma cache_frame(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n){s u:State}
 (outside:UniformFastPhysicalCRTProgress.Outside (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s.natHeap u)
 (j:Fin (UniformJointCacheAllocation.ell n))(q:ℕ)
 (hq:q<(UniformJointCacheAllocation.axis c n j).endNat):u.natHeap q=s.natHeap q:=
 below hn outside q (hq.trans_le (cache_before c hn j))
end
end ExactFourierCircuits.UniformFinalPhysicalTableExecution
