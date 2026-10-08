import UniformRetainedDirectDFTFallback
set_option autoImplicit false
namespace ExactFourierCircuits.UniformEmptyStartupBranchPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell)
open UniformAllAxisSeedPreparation (axisCount)
noncomputable section

def head:Program:=UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460)++
 [.natLiteral 3270 194,.branchLT 102 3270 1462 1511]
def program:Program:=head++UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++
 UniformEmptyStartupMatchingPreparation.initializer.map Op.code++
 UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]
lemma head_length:head.length=1462:=by
 simp only [head,List.length_append,List.length_map,UniformAllAxisConjugatePreparation.fullProgram_length];rfl
lemma program_length:program.length=4306:=by
 simp only [program,List.length_append,List.length_map,head_length,UniformRetainedDirectDFTFallback.program_length,
  UniformEmptyStartupMatchingPreparation.initializer_length,UniformSeedHighDataMatchingPreparation.program_length];rfl
attribute [local irreducible] UniformAllAxisConjugatePreparation.fullProgram UniformRetainedDirectDFTFallback.program
 UniformEmptyStartupMatchingPreparation.initializer UniformSeedHighDataMatchingPreparation.program
lemma startup_code:CodeAt UniformAllAxisConjugatePreparation.fullProgram program 0 1460:=by
 have eq:program=UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460)++
  ([.natLiteral 3270 194,.branchLT 102 3270 1462 1511]++
   UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++UniformEmptyStartupMatchingPreparation.initializer.map Op.code++
   UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]):=by
  simp only [program,head,List.append_assoc]
 rw [eq]
 exact UniformAllAxisConjugatePreparation.relocated_prefix_code _ _ _
lemma threshold_at:program[1460]?=some (.natLiteral 3270 194):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460))
  [.natLiteral 3270 194,.branchLT 102 3270 1462 1511]
  (UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++UniformEmptyStartupMatchingPreparation.initializer.map Op.code++
   UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]) 0 (by decide)
 simpa only [program,head,List.append_assoc,List.length_map,UniformAllAxisConjugatePreparation.fullProgram_length,
  Nat.add_zero,List.getElem?_cons_zero] using h
lemma branch_at:program[1461]?=some (.branchLT 102 3270 1462 1511):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460))
  [.natLiteral 3270 194,.branchLT 102 3270 1462 1511]
  (UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++UniformEmptyStartupMatchingPreparation.initializer.map Op.code++
   UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]) 1 (by decide)
 simpa only [program,head,List.append_assoc,List.length_map,UniformAllAxisConjugatePreparation.fullProgram_length,
  List.getElem?_cons_succ,List.getElem?_cons_zero] using h
lemma fallback_code:CodeAt UniformRetainedDirectDFTFallback.program program 1462 4305:=by
 have eq:program=head++UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++
  (UniformEmptyStartupMatchingPreparation.initializer.map Op.code++
   UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]):=by
  simp only [program,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code _ _ _ _ _ head_length
lemma initializer_code:BlockAt UniformEmptyStartupMatchingPreparation.initializer program 1511:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (head++UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305))
  (UniformEmptyStartupMatchingPreparation.initializer.map Op.code)
  (UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)++[.halt]) i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
  UniformRetainedDirectDFTFallback.program_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma matching_code:CodeAt UniformSeedHighDataMatchingPreparation.program program 1636 4305:=by
 have len:(head++UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++
  UniformEmptyStartupMatchingPreparation.initializer.map Op.code).length=1636:=by
  simp only [List.length_append,List.length_map,head_length,UniformRetainedDirectDFTFallback.program_length,
   UniformEmptyStartupMatchingPreparation.initializer_length]
 exact UniformRankCrossPreparationMachine.segment_code _ [.halt] _ _ _ len
lemma halt_at:program[4305]?=some .halt:=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (head++UniformRetainedDirectDFTFallback.program.map (relocate 1462 4305)++
   UniformEmptyStartupMatchingPreparation.initializer.map Op.code++UniformSeedHighDataMatchingPreparation.program.map (relocate 1636 4305)) [.halt] [] 0 (by decide)
 simpa only [program,List.append_assoc,List.append_nil,List.length_append,List.length_map,head_length,
  UniformRetainedDirectDFTFallback.program_length,UniformEmptyStartupMatchingPreparation.initializer_length,
  UniformSeedHighDataMatchingPreparation.program_length,List.getElem?_cons_zero] using h
lemma code_bound {n:ℕ} (hn:0<n):4306≤ UniformEmptyStartupMatchingPreparation.budget n:=by
 have h:=Nat.pow_le_pow_left (show 3≤ n+2 by omega) 19
 norm_num at h
 unfold UniformEmptyStartupMatchingPreparation.budget;omega

/-- The small branch is a genuine DFT; the large branch is a proved selected
matching action waiting for the global controller. These contracts are explicit. -/
def Outcome {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (u:State):Prop:=
 (ell n<194 ∧ComputesDFT n x u) ∨
 (∃hc:194≤ ell n,
  UniformHighDataConjugateMatchingPreparation.FullAction (UniformEmptyStartupMatchingPreparation.packingLayout hn hc)
   (UniformEmptyStartupMatchingPreparation.original hn hc x) u ∧
  UniformHighDataConjugateMatchingPreparation.LogicalPairs (UniformEmptyStartupMatchingPreparation.packingLayout hn hc)
   (UniformEmptyStartupMatchingPreparation.allocation hn hc).matching.capacity
   (UniformEmptyStartupMatchingPreparation.original hn hc x) u)

def threshold (s:State):State:=writeNat s 3270 194
lemma threshold_metadata {n:ℕ} {s:State} (m:UniformPermutationInversePreparation.Metadata n s):
 UniformPermutationInversePreparation.Metadata n (threshold s):=by
 apply m.transport_saved
 · constructor
   · simpa [threshold,writeNat,next] using m.saved.nextPrime
   · simpa [threshold,writeNat,next] using m.saved.inputLength
   · simpa [threshold,writeNat,next] using m.saved.count
   · simpa [threshold,writeNat,next] using m.saved.workingLength
   · simpa [threshold,writeNat,next] using m.saved.masterRoot
   · simpa [threshold,writeNat,next] using m.saved.copyAddress
   · simpa [threshold,writeNat,next] using m.saved.copyLength
 · intro i _;rfl
lemma threshold_operands {n:ℕ} {s:State} {x:Fin n→ℂ} (h:UniformInitialPreparation.Operands n x s):
 UniformInitialPreparation.Operands n x (threshold s):=h.transport rfl
lemma threshold_original {n:ℕ} {s:State} (h:UniformAllAxisSeedPreparation.Retained n (axisCount n) s):
 UniformAllAxisSeedPreparation.Retained n (axisCount n) (threshold s):=h.transport_before (fun _ _=>rfl) rfl
lemma threshold_conjugate {n:ℕ} {s:State} (h:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s):
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) (threshold s):=h.transport (fun _ _ _=>rfl) rfl


def runtimeBudget {n:ℕ} (hn:0<n):ℕ:=
 if hc:194≤ ell n then UniformEmptyStartupMatchingPreparation.runtimeBudget hn hc+2 else
 UniformAllAxisConjugatePreparation.fullBudget n+2+7*n^2+9*n+27+
 UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/n)+1

attribute [local irreducible] UniformEmptyStartupMatchingPreparation.entry
 UniformEmptyStartupMatchingPreparation.packingLayout
 UniformEmptyStartupMatchingPreparation.original

def selectedBudget {n:ℕ} (hn:0<n) (hc:194≤ ell n):ℕ:=125+
 UniformSeedChunkPreparation.runtimeBudget n (UniformEmptyStartupMatchingPreparation.selectedAxis n hc) (UniformEmptyStartupMatchingPreparation.seed n)+
 UniformConjugatePackedMatchingPreparation.runtimeBudget (UniformEmptyStartupMatchingPreparation.packingLayout hn hc) (UniformEmptyStartupMatchingPreparation.work n)+
 220*(UniformEmptyStartupMatchingPreparation.packingLayout hn hc).packing.total+62+1

lemma selected_execution {n:ℕ} (hn:0<n) (hc:194≤ ell n) (x:Fin n→ℂ) (b:State)
 (bm:UniformPermutationInversePreparation.Metadata n b) (bo:UniformInitialPreparation.Operands n x b)
 (br:UniformAllAxisSeedPreparation.Retained n (axisCount n) b)
 (bc:UniformAllAxisConjugatePreparation.Retained n (axisCount n) b) (pc:b.pc=1511)
 (bb:WordBound (UniformEmptyStartupMatchingPreparation.budget n) b):∃u ticks,
 BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) b ticks u ∧ticks≤ selectedBudget hn hc ∧
 UniformHighDataConjugateMatchingPreparation.FullAction (UniformEmptyStartupMatchingPreparation.packingLayout hn hc)
  (UniformEmptyStartupMatchingPreparation.original hn hc x) u ∧
 UniformHighDataConjugateMatchingPreparation.LogicalPairs (UniformEmptyStartupMatchingPreparation.packingLayout hn hc)
  (UniformEmptyStartupMatchingPreparation.allocation hn hc).matching.capacity
  (UniformEmptyStartupMatchingPreparation.original hn hc x) u ∧u.rootOrders=b.rootOrders ∧
 u.scalarHeap 0=some (UniformPairMachine.prepared (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))) ∧u.pc=4305:=by
 have code:=code_bound hn
 have safe:=UniformEmptyStartupMatchingPreparation.initializer_safe hn hc b bm br
 have install:=block_runs UniformEmptyStartupMatchingPreparation.initializer program 1511 n
  (UniformEmptyStartupMatchingPreparation.budget n) x b initializer_code pc bb
  (by rw [UniformEmptyStartupMatchingPreparation.initializer_length];omega) safe.1 safe.2
 let e:=UniformEmptyStartupMatchingPreparation.entry b
 have eb:WordBound (UniformEmptyStartupMatchingPreparation.budget n) e:=by
  unfold e UniformEmptyStartupMatchingPreparation.entry
  exact changePC_bound _ (applyBlock UniformEmptyStartupMatchingPreparation.initializer b) 0 install.final_bound (by omega)
 have em:=UniformEmptyStartupMatchingPreparation.entry_metadata bm
 have eo:=UniformEmptyStartupMatchingPreparation.entry_operands bo
 have er:=UniformEmptyStartupMatchingPreparation.entry_original br
 have ec:=UniformEmptyStartupMatchingPreparation.entry_conjugate bc
 obtain ⟨z,tx,last,cost,zp,action,logical,rz,cz,mz,oz,out,roots⟩:=
  UniformSeedHighDataMatchingPreparation.execution hn x (UniformEmptyStartupMatchingPreparation.packingLayout hn hc)
   (UniformPaddedInputPreparation.dataBase n) (UniformEmptyStartupMatchingPreparation.original hn hc x) e
   (UniformEmptyStartupMatchingPreparation.entry_seed_args hc b bm)
   (UniformEmptyStartupMatchingPreparation.entry_packing_args hn hc b bm)
   (UniformEmptyStartupMatchingPreparation.entry_low bm)
   (UniformEmptyStartupMatchingPreparation.original_present hn hc x eo)
   (UniformEmptyStartupMatchingPreparation.low_separated hn hc) (UniformEmptyStartupMatchingPreparation.placement hn hc)
   (UniformEmptyStartupMatchingPreparation.work n) (10*UniformEmptyStartupMatchingPreparation.arena n)
   (11*UniformEmptyStartupMatchingPreparation.arena n) (11*UniformEmptyStartupMatchingPreparation.arena n+1)
   (UniformEmptyStartupMatchingPreparation.allocation hn hc)
   (UniformEmptyStartupMatchingPreparation.entry_future_args hc b bm)
   (UniformEmptyStartupMatchingPreparation.entry_matching_args hn hc b bm br) em eo er ec
   (by rw [(UniformEmptyStartupMatchingPreparation.packing_shape hn hc).1];exact UniformEmptyStartupMatchingPreparation.freshness hn hc)
   (by omega) (by unfold e UniformEmptyStartupMatchingPreparation.entry;rfl) eb
 have tail:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformSeedHighDataMatchingPreparation.program_length];omega :1636+UniformSeedHighDataMatchingPreparation.program.length≤ UniformEmptyStartupMatchingPreparation.budget n)
  (by omega :4305≤ UniformEmptyStartupMatchingPreparation.budget n) last
 have ep:(applyBlock UniformEmptyStartupMatchingPreparation.initializer b).pc=1636:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,UniformEmptyStartupMatchingPreparation.initializer_length,pc]
 rw [show placed 1636 e=applyBlock UniformEmptyStartupMatchingPreparation.initializer b by
  unfold e UniformEmptyStartupMatchingPreparation.entry
  exact UniformSeedRankCrossPreparation.placed_zero _ _ ep] at tail
 let u:=setPC z 4305
 have stop:BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) u 1 u:=
  .halt tail.final_bound (by simp [step,u,setPC,halt_at])
 refine ⟨u,125+tx+1,?_,?_,action,logical,?_,?_,rfl⟩
 · simpa only [UniformEmptyStartupMatchingPreparation.initializer_length,Nat.add_assoc] using
    install.executes (tail.executes stop)
 · unfold selectedBudget;omega
 · exact roots.trans (UniformEmptyStartupMatchingPreparation.entry_frame b).2.2.2.2
 · change z.scalarHeap 0=some (UniformPairMachine.prepared (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))
   exact UniformSeedRankCrossPreparation.operands_master oz

/-- The actual finite branch program starts from empty. Small lengths produce
DFT outputs; the capacity branch produces the genuine selected matching action.
No startup/packing/spectrum/header/result premise survives this theorem. -/
theorem initial_execution {n:ℕ} (hn:0<n) (x:Fin n→ℂ):∃u ticks,
 BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) initial ticks u ∧
 ticks≤ runtimeBudget hn ∧Outcome hn x u ∧u.rootOrders=[UniformMasterRootMachine.order n] ∧
 u.scalarHeap 0=some (UniformPairMachine.prepared (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))) ∧u.pc=4305 :=by
 obtain ⟨t,v,hv,hcost,hcRet,hoRet,hm,ho,hroots,hout,vp,hbudget⟩:=UniformAllAxisConjugatePreparation.initial_execution hn x
 have code:=code_bound hn
 have first:=UniformBoundedAssembly.boundedExecution_placed startup_code
  (by rw [UniformAllAxisConjugatePreparation.fullProgram_length];omega :0+UniformAllAxisConjugatePreparation.fullProgram.length≤ UniformEmptyStartupMatchingPreparation.budget n)
  (by omega :1460≤ UniformEmptyStartupMatchingPreparation.budget n) hv
 rw [show placed 0 initial=initial by rfl] at first
 let s:State:={v with pc:=1460}
 have ms:UniformPermutationInversePreparation.Metadata n s:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
 have os:UniformInitialPreparation.Operands n x s:=ho.transport rfl
 have rs:UniformAllAxisSeedPreparation.Retained n (axisCount n) s:=hoRet.withPC
 have cs:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s:=hcRet.withPC
 have wb:WordBound (UniformEmptyStartupMatchingPreparation.budget n) (threshold s):=
  writeNat_bound _ s 3270 194 first.final_bound (by change 1461≤_;omega) (by omega)
 have load:BoundedRuns program n x (UniformEmptyStartupMatchingPreparation.budget n) s 1 (threshold s):=
  .next first.final_bound (by simp [step,s,threshold_at,threshold]) (.refl wb)
 have tm:=threshold_metadata ms
 have tops:=threshold_operands os
 have tr:=threshold_original rs
 have tc:=threshold_conjugate cs
 by_cases hc:194≤ ell n
 · let b:=setPC (threshold s) 1511
   have bb:=changePC_bound _ (threshold s) 1511 wb (by omega)
   have branch:BoundedRuns program n x (UniformEmptyStartupMatchingPreparation.budget n) (threshold s) 1 b:=by
    refine .next wb ?_ (.refl bb)
    have counter:(threshold s).natReg 102=ell n:=by simpa [threshold,writeNat,next] using ms.saved.count
    have thresholdVal:(threshold s).natReg 3270=194:=by simp [threshold,writeNat,next]
    have pc:(threshold s).pc=1461:=rfl
    simp only [step,pc,branch_at,counter,thresholdVal,show ¬ell n<194 by omega,ite_false]
    rfl
   obtain ⟨u,tx,run,cost,action,logical,roots,master,up⟩:=selected_execution hn hc x b
    (tm.transport (fun _ _=>rfl) (fun _ _=>rfl)) (tops.transport rfl) tr.withPC tc.withPC rfl bb
   refine ⟨u,t+UniformAllAxisSeedPreparation.preparationRuntime n+1+UniformAllAxisConjugatePreparation.preparationRuntime n+1+1+1+tx,
    ?_,?_,Or.inr ⟨hc,action,logical⟩,roots.trans hroots,master,?_⟩
   · simpa only [Nat.add_assoc] using first.executes (load.executes (branch.executes run))
   · simp only [runtimeBudget,dite_eq_left hc,UniformEmptyStartupMatchingPreparation.runtimeBudget]
     unfold selectedBudget at cost;omega
   · exact up

 · let b:=setPC (threshold s) 1462
   have bb:=changePC_bound _ (threshold s) 1462 wb (by omega)
   have branch:BoundedRuns program n x (UniformEmptyStartupMatchingPreparation.budget n) (threshold s) 1 b:=by
    refine .next wb ?_ (.refl bb)
    have counter:(threshold s).natReg 102=ell n:=by simpa [threshold,writeNat,next] using ms.saved.count
    have thresholdVal:(threshold s).natReg 3270=194:=by simp [threshold,writeNat,next]
    have pc:(threshold s).pc=1461:=rfl
    simp only [step,pc,branch_at,counter,thresholdVal,show ell n<194 by omega,ite_true]
    rfl
   let e:=setPC b 0
   have eb:=changePC_bound _ b 0 bb (by omega)
   have em:UniformPermutationInversePreparation.Metadata n e:=tm.transport (fun _ _=>rfl) (fun _ _=>rfl)
   have eo:UniformInitialPreparation.Operands n x e:=tops.transport rfl
   obtain ⟨z,last,DFT,roots,master,zp⟩:=UniformRetainedDirectDFTFallback.execution hn x e em eo rfl eb
   have tail:=UniformBoundedAssembly.boundedExecution_placed fallback_code
    (by rw [UniformRetainedDirectDFTFallback.program_length];omega :1462+UniformRetainedDirectDFTFallback.program.length≤ UniformEmptyStartupMatchingPreparation.budget n)
    (by omega :4305≤ UniformEmptyStartupMatchingPreparation.budget n) last
   rw [show placed 1462 e=b by rfl] at tail
   let u:=setPC z 4305
   have stop:BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) u 1 u:=
    .halt tail.final_bound (by simp [step,u,setPC,halt_at])
   refine ⟨u,t+UniformAllAxisSeedPreparation.preparationRuntime n+1+UniformAllAxisConjugatePreparation.preparationRuntime n+1+1+1+
    (7*n^2+9*n+27+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/n))+1,?_,?_,Or.inl ⟨by omega,DFT⟩,roots.trans hroots,master.trans (UniformSeedRankCrossPreparation.operands_master eo),rfl⟩
   · simpa only [Nat.add_assoc] using first.executes (load.executes (branch.executes (tail.executes stop)))
   · simp only [runtimeBudget,dite_eq_right hc];omega


/-- The fallback criterion bounds the original length by a single finite
constant. This does not make the large selected matching action a DFT. -/
lemma small_length_bound {n:ℕ} (hn:0<n) (small:ell n<194):
 n<UniformWorkingLength.primeProduct 194:=by
 have positive:=UniformWorkingLength.firstExceed_pos hn
 have stop:UniformWorkingLength.firstExceed n≤194:=by
  change UniformWorkingLength.firstExceed n-1<194 at small
  omega
 have bound:=Nat.find_spec (UniformWorkingLength.product_exceeds_exists n)
 change 2*n<UniformWorkingLength.primeProduct (UniformWorkingLength.firstExceed n) at bound
 exact (lt_of_le_of_lt (by omega :n≤2*n) bound).trans_le (UniformWorkingLength.primeProduct_strictMono.monotone stop)

end
end ExactFourierCircuits.UniformEmptyStartupBranchPreparation
