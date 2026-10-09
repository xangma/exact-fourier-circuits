import UniformLocalFactorDispatchControl
import UniformForwardMatchingFactorHeaderRetention
import UniformInverseMatchingFactorReloadRetention
import UniformLocalBroadcastPoolRetention

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.3, Lemma 3.4 preparation argument, PDF p. 17; §3.4, Proposition 3.1 conclusion, p. 18.
The three stored-slot branches and register retention are implementation bookkeeping for preparing fixed replay factors. All branches use integer metadata; supplied coefficient/source facts remain explicit intermediate contracts.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFactorDispatchMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B n:ℕ}
/-- A real stored slot selects one of three fixed physical producers. The
Processed/coefficients entry is the earlier rectangle/Height producer's bank;
there is no generated row, count, permutation or factor-pool entry premise. -/
/- Paper: Lemma 3.4 preparation argument, p. 17: physical factor production is charged and branches only on stored integer slot metadata. The Processed/Sources contracts must be produced by earlier stages. -/
theorem execution (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (I:ℕ) (il:UniformInverseMatchingFactorPreparation.InverseLayout (H.forward c q slot) l I)
 (x:Fin n→ℂ) (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ) (s:State)
 (args:H.Prepared c q slot s)
 (rectangle:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (processed:UniformCrossHeightPreparationMachine.Processed (H.forward c q slot).chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height (H.forward c q slot).chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative
  c.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (ip:s.natReg 6200=I) (code:1156≤B) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution program n x B s t u ∧t≤runtimeBudget c q slot l bl ha he ∧u.pc=1155 ∧
 Result c q slot l bl ha he I bank s u := by
 have safe:=boot_safe args record (by have:=bl.slotBound;omega) code wb
 have first:=block_runs boot program 0 n B x s boot_code pc wb
  (by rw[boot_length];omega) safe.1 safe.2
 let b:=applyBlock boot s
 have bp:b.pc=7:=by rw[applyBlock_pc,pc,boot_length]
 have flags:=boot_flags args record
 have choice:=select slot x b bp (boot_zero s) flags.1 flags.2 first.final_bound code
 let ready:=setPC b 0
 have readyHeap:ready.natHeap=s.natHeap:=rfl
 have bound:WordBound B ready:=changePC_bound B b 0 first.final_bound (by omega)
 have head:H.Prepared c q slot ready:=boot_prepared args 0
 have physicalSlot:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot ready:=record
 have row:UniformLocalRectangleBankMachine.RowSource c.rectangle q ready:=rectangle
 have proc:UniformCrossHeightPreparationMachine.Processed (H.forward c q slot).chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height (H.forward c q slot).chunk.height) ready:=processed
 have source:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative
  c.height.P c.conjugates bank ready:=UniformConjugatePackedMatchingPreparation.sources_transport sources rfl
 have cons:UniformHadamardPairMachine.Constants ready:=constants
 cases hb:slot.broadcast with
 | true=>
  obtain ⟨z,t,run,cost,zp,pool,table,count,src,const,nh,nhHigh,sh,out,roots⟩:=
   UniformLocalBroadcastPoolMachine.execution_high c.rectangle c.slot c.borrowed c.mapped c.translated
    c.pool c.mu c.conjugateMu c.height.C c.negative c.height.P c.conjugates c.ambient c.gates B
    q slot bank x ready head.2.1 row physicalSlot bl.capacity bl.outputCount bl.sourceRange bl.targetRange
    l.extent source cons l.coefficient l.low l.poolFresh bl.borrowedFresh bl.mappedFresh
    bl.translatedBound l.poolBound bl.rectangleBound bl.slotBound (by omega) rfl bound
  have last:=finish broadcast_code (by rw[BC.program,UniformLocalBroadcastPoolMachine.program_length];omega) code run
  have startEq:placed 439 ready=setPC b 439:=rfl
  rw[startEq] at last
  have selected:BoundedRuns program n x B b 1 (setPC b 439):=by
   simpa only [branches,target,hb,ite_true] using choice
  let u:=setPC z 1155
  have whole:BoundedExecution program n x B s (7+1+(t+1)) u:=by
   simpa only [boot_length,u] using (first.trans selected).executes last
  refine ⟨u,7+1+(t+1),whole,?_,rfl,?_⟩
  · simp only [runtimeBudget,hb,ite_true];omega
  · apply Result.withPC (u:=z)
    refine ⟨?_,?_,?_,?_,src,const,out,roots,nh,(by simpa only [natEnd,hb,ite_true,readyHeap] using nhHigh),sh,(by simpa only [u,setPC] using (final_saved whole).1),(by simpa only [u,setPC] using final_cacheHeaders whole),(by simpa only [u,setPC] using (final_saved whole).2)⟩
    · simpa only [entry,hb,ite_true] using broadcast_tensor_pool (l:=l) (bl:=bl) pool
    · simpa only [printedBase,printedRows,hb,ite_true] using table
    · rw [UniformNewtonTableMachine.Executes.keeps_nat run.executes
       (footprint_keeps broadcast_footprint 5847 (Or.inr (by omega))),prepared_rowBase head]
      simp only [printedBase,hb,ite_true]
    · simpa only [printedRows,hb,ite_true,UniformLocalBroadcastPoolMachine.rows_length] using count
 | false=>
  cases hi:slot.inverse with
  | false=>
   obtain ⟨z,t,run,cost,zp,result,count,nhHigh⟩:=
    UniformForwardMatchingFactorHeaderPreparation.execution_high (H.forward c q slot) l
     (by omega) ha he x bank ready head.1 (forward_slot physicalSlot hb hi) proc source cons rfl bound
   have last:=finish forward_code (by rw[FH.program,UniformForwardMatchingFactorHeaderPreparation.program_length];omega) code run
   have startEq:placed 9 ready=setPC b 9:=rfl
   rw[startEq] at last
   have selected:BoundedRuns program n x B b 2 (setPC b 9):=by
    simpa only [branches,target,hb,hi,Bool.false_eq_true,ite_false] using choice
   let u:=setPC z 1155
   have whole:BoundedExecution program n x B s (7+2+(t+1)) u:=by
    simpa only [boot_length,u] using (first.trans selected).executes last
   refine ⟨u,7+2+(t+1),whole,?_,rfl,?_⟩
   · simp only [runtimeBudget,hb,hi,Bool.false_eq_true,ite_false]
     change t≤4*c.height.K+180*q.width+45*c.ambient+
      136*(UniformForwardMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length+163 at cost
     omega
   · apply Result.withPC (u:=z)
     refine ⟨?_,?_,?_,?_,result.sources,result.constants,result.outputs,result.roots,
      result.natPrefix,(by simpa only [natEnd,hb,hi,Bool.false_eq_true,ite_false,ite_true,forward_translated,readyHeap] using nhHigh),result.scalarOutside,(by simpa only [u,setPC] using (final_saved whole).1),(by simpa only [u,setPC] using final_cacheHeaders whole),(by simpa only [u,setPC] using (final_saved whole).2)⟩
     · simpa only [entry,hb,hi,Bool.false_eq_true,ite_false] using result.tensor_pool
     · simpa only [printedBase,printedRows,hb,hi,Bool.false_eq_true,ite_false,forward_translated] using result.table
     · rw [UniformNewtonTableMachine.Executes.keeps_nat run.executes
        (footprint_keeps forward_footprint 5847 (Or.inr (by omega))),prepared_rowBase head]
       simp only [printedBase,hb,hi,Bool.false_eq_true,ite_false]
     · simpa only [printedRows,hb,hi,Bool.false_eq_true,ite_false] using count
  | true=>
   let atHeader:=setPC b 680
   have headerBound:=changePC_bound B b 680 first.final_bound (by omega)
   have headerSafe:=inverseSetup_safe (s:=atHeader) (boot_zero s) headerBound
   have write:=block_runs inverseSetup program 680 n B x atHeader inverseSetup_code rfl headerBound
    (by change 680+1≤B;omega) headerSafe.1 headerSafe.2
   let invReady:=setPC (applyBlock inverseSetup atHeader) 0
   have invHeap:invReady.natHeap=s.natHeap:=rfl
   have invBound:=changePC_bound B (applyBlock inverseSetup atHeader) 0 write.final_bound (by omega)
   have invArgs:UniformForwardMatchingFactorHeaderPreparation.Args (H.forward c q slot) invReady:=by
    apply forwardArgs_transport head.1
    intro j lo high
    exact inverseSetup_nat atHeader j (by omega)
   have inv:invReady.natReg 4460=I:=(inverseSetup_nat atHeader 4460 (by omega)).trans ((boot_inverse s).trans ip)
   obtain ⟨z,t,run,cost,zp,result,count,nhHigh⟩:=
    UniformInverseMatchingFactorPreparation.reload_execution_high (H.forward c q slot) l (by omega)
     ha he I il x bank invReady invArgs (inverse_slot (s:=invReady) record hb hi)
     processed (UniformConjugatePackedMatchingPreparation.sources_transport sources rfl) constants inv rfl invBound
   have last:=finish inverse_code (by rw[IV.program,UniformInverseMatchingFactorPreparation.reloadProgram_length];omega) code run
   have startEq:placed 681 invReady=applyBlock inverseSetup atHeader:=by
    change {applyBlock inverseSetup atHeader with pc:=681}=applyBlock inverseSetup atHeader
    have bp':(applyBlock inverseSetup atHeader).pc=681:=by rw [applyBlock_pc];rfl
    rw [←bp']
   rw[startEq] at last
   have selected:BoundedRuns program n x B b 2 atHeader:=by
    simpa only [branches,target,hb,hi,Bool.false_eq_true,ite_false,ite_true] using choice
   let u:=setPC z 1155
   have whole:BoundedExecution program n x B s (7+2+1+(t+1)) u:=by
    simpa only [boot_length,show inverseSetup.length=1 from rfl,u] using ((first.trans selected).trans write).executes last
   refine ⟨u,7+2+1+(t+1),whole,?_,rfl,?_⟩
   · simp only [runtimeBudget,hb,hi,Bool.false_eq_true,ite_false,ite_true]
     change t≤4*c.height.K+180*q.width+45*c.ambient+
      161*(UniformInverseMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length+177 at cost
     omega
   · apply Result.withPC (u:=z)
     refine ⟨?_,?_,?_,?_,result.sources,result.constants,result.outputs,result.roots,
      result.natPrefix,(by simpa only [natEnd,hb,hi,Bool.false_eq_true,ite_false,ite_true,forward_translated,invHeap] using nhHigh),result.scalarOutside,(by simpa only [u,setPC] using (final_saved whole).1),(by simpa only [u,setPC] using final_cacheHeaders whole),(by simpa only [u,setPC] using (final_saved whole).2)⟩
     · simpa only [entry,hb,hi,Bool.false_eq_true,ite_false,ite_true] using result.tensor_pool
     · simpa only [printedBase,printedRows,hb,hi,Bool.false_eq_true,ite_false,ite_true] using result.table
     · rw [UniformNewtonTableMachine.Executes.keeps_nat run.executes
        (footprint_keeps inverse_footprint 5847 (Or.inr (by omega)))]
       have eq:invReady.natReg 5847=I:=by
        simp only [invReady,atHeader,setPC,inverseSetup,applyBlock,Op.apply,writeNat,next]
        simp only [Function.update_self,show b.natReg 6210=0 from boot_zero s,Nat.add_zero]
        exact (boot_inverse s).trans ip
       rw [eq]
       simp only [printedBase,hb,hi,Bool.false_eq_true,ite_false,ite_true]
     · simpa only [printedRows,hb,hi,Bool.false_eq_true,ite_false,ite_true] using count
end
end ExactFourierCircuits.UniformLocalFactorDispatchMachine
