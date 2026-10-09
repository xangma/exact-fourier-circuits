import UniformLocalCacheSlotConductorMachine
import UniformLocalFactorDispatchExecution
import UniformMatchingSlotDirectoryFrames
import UniformLocalCacheDirectoryRetention

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalFactorDispatchMachine
noncomputable section
namespace Header
abbrev Parameters:=UniformLocalCacheSlotHeaderMachine.Parameters
abbrev forward:=UniformLocalCacheSlotHeaderMachine.forward
end Header

/-- The stored physical axis uses precisely the dispatched row occurrences. -/
def slotAxis {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot) (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height) (positive:2≤c.ambient):UniformSectorPackingMachine.PhysicalAxis:=
 UniformProducedMatchingSlotDirectory.rowAxis c.ambient c.cacheWidths c.cachePermutation
  (printedRows c q slot l bl ha he) positive
  (dispatched_geometry c q slot l bl ha he).1
  (dispatched_geometry c q slot l bl ha he).2.1
  (dispatched_geometry c q slot l bl ha he).2.2

structure Stored {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot) (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ) (positive:2≤c.ambient)
 (s u:State):Prop where
 abi:UniformLocalMatchingSlotDirectory.Entry c.cacheDirectory c.time c.ambient c.pool
  (c.ambient-(printedRows c q slot l bl ha he).length) c.cacheWidths c.cachePermutation c.kind u
 row:UniformSectorPackingMachine.Rows [slotAxis c q slot l bl ha he positive] 0 c.cacheAxis u
 widths:UniformSectorPackingMachine.Widths [slotAxis c q slot l bl ha he positive] u
 permutation:UniformSectorPackingMachine.Permutations [slotAxis c q slot l bl ha he positive] u
 factors:UniformGlobalDiagonalRowsMachine.Pools [entry c q slot l bl ha he bank] u
 sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank u
 constants:UniformHadamardPairMachine.Constants u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natPrefix:∀i,i<c.borrowed→i<c.cachePermutation→u.natHeap i=s.natHeap i
 cached:∀i, (natEnd c q slot l bl ha he I) ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i
 scalarOutside : ∀ i, (i < c.pool ∨ c.pool + 9*c.ambient ≤ i) → i ≠ c.mu → i ≠ c.conjugateMu → u.scalarHeap i = s.scalarHeap i
 driver : ∀ i, 6100 ≤ i → i ≤ 6187 → u.natReg i = s.natReg i
 inverseHeader : u.natReg 6200 = s.natReg 6200
 natHigh : ∀i, natEnd c q slot l bl ha he I ≤ i → c.cacheDirectory+7 ≤ i →
  u.natHeap i=s.natHeap i

/-- The actual74 selector, real1156 factor dispatcher and real80 partition/ABI
printer execute continuously. Their input consists of the earlier rectangle
producer's physical banks and ordinary allocation geometry. -/
theorem slot_execution {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height) (I:ℕ)
 (il:UniformInverseMatchingFactorPreparation.InverseLayout (Header.forward c q slot) l I)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ) (x:Fin n→ℂ) (s:State)
 (args:UniformLocalCacheSlotHeaderMachine.Args c s)
 (rectangle:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (processed:UniformCrossHeightPreparationMachine.Processed (Header.forward c q slot).chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height (Header.forward c q slot).chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (positive:2≤c.ambient) (inverse:s.natReg 6200=I)
 (rowEnd:c.rectangle+6≤B) (slotEnd:c.slot+1≤B)
 (rowsEnd:printedBase c slot I+3*(printedRows c q slot l bl ha he).length≤c.cachePermutation)
 (permutationEnd:c.cachePermutation+c.ambient≤c.cacheWidths)
 (widthsEnd:c.cacheWidths+c.ambient≤c.cacheMarkers)
 (markersEnd:c.cacheMarkers+c.ambient≤c.cacheAxis)
 (axisEnd:c.cacheAxis+4≤c.cacheDirectory) (directoryEnd:c.cacheDirectory+7≤B)
 (code:1336≤B) (pc:s.pc=15) (wb:WordBound B s):∃u ticks,
 BoundedRuns program n x B s ticks u ∧
 ticks≤runtimeBudget c q slot l bl ha he+21*c.ambient+116 ∧u.pc=1325 ∧
 Stored c q slot l bl ha he I bank positive s u:=by
 let start:=setPC s 0
 have startBound:=changePC_bound B s 0 wb (by omega)
 obtain ⟨a,header,ap,prepared,anh,ash,asr,aout,aroot,aargs⟩:=
  UniformLocalCacheSlotHeaderMachine.execution x start args rectangle record startBound rowEnd slotEnd (by omega) rfl
 have first:=UniformBoundedAssembly.boundedExecution_placed header_code
  (by rw [H.program,UniformLocalCacheSlotHeaderMachine.program_length];omega) (by omega) header
 rw [UniformSeedRankCrossPreparation.placed_zero s 15 pc] at first
 let ready:=setPC a 0
 have readyBound:=changePC_bound B a 0 header.final_bound (by omega)
 have head:UniformLocalCacheSlotHeaderMachine.Prepared c q slot ready:=
  UniformLocalCacheSlotHeaderMachine.prepared_nat prepared rfl
 have rrectangle:UniformLocalRectangleBankMachine.RowSource c.rectangle q ready:=by
  simpa only [UniformLocalRectangleBankMachine.RowSource,ready,setPC,anh,start] using rectangle
 have rrecord:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot ready:=by
  simpa only [UniformLocalBroadcastPoolMachine.SlotSource,ready,setPC,anh,start] using record
 have rprocessed:UniformCrossHeightPreparationMachine.Processed (Header.forward c q slot).chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height (Header.forward c q slot).chunk.height) ready:=by
  simpa only [UniformCrossHeightPreparationMachine.Processed,UniformCrossHeightPreparationMachine.Slice,
   UniformCrossHeightPreparationMachine.Record,UniformCrossShearTableMachine.Table,
   UniformCrossShearTableMachine.RowFields,ready,setPC,anh,start] using processed
 have rsource:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank ready:=
  UniformConjugatePackedMatchingPreparation.sources_transport sources ash
 have rconstants:UniformHadamardPairMachine.Constants ready:=by
  simpa only [UniformHadamardPairMachine.Constants,ready,setPC,ash,start] using constants
 have ri:ready.natReg 6200=I:=
  (UniformLocalCacheSlotHeaderMachine.driver_frame header 6200 (Or.inr (by omega))).trans inverse
 obtain ⟨b,bt,dispatch,bcost,bp,post⟩:=UniformLocalFactorDispatchMachine.execution c q slot l bl ha he I il x bank ready
  head rrectangle rrecord rprocessed rsource rconstants ri (by omega) rfl readyBound
 have second:=UniformBoundedAssembly.boundedExecution_placed factor_code
  (by rw [F.program,UniformLocalFactorDispatchMachine.program_length];omega) (by omega) dispatch
 have factorStart:placed 89 ready=setPC a 89:=rfl
 rw [factorStart] at second
 let dirReady:=setPC b 0
 have directoryBound:=changePC_bound B b 0 dispatch.final_bound (by omega)
 rcases prepared.2.2 with ⟨ht,hr,hpool,hP,hW,hU,hA,hT,hD,hkind⟩
 have keep (r:ℕ) (lo:5840≤r) (hi:r≤5849) (ne:r≠5847):dirReady.natReg r=a.natReg r:=post.cacheHeaders r lo hi ne
 have dargs:UniformLocalMatchingSlotDirectory.Args c.time c.ambient c.pool c.cachePermutation c.cacheWidths
  c.cacheMarkers c.cacheAxis (printedBase c slot I) c.cacheDirectory c.kind
  (printedRows c q slot l bl ha he).length dirReady:=
  ⟨(keep 5840 (by omega) (by omega) (by omega)).trans ht,
   (keep 5841 (by omega) (by omega) (by omega)).trans hr,
   (keep 5842 (by omega) (by omega) (by omega)).trans hpool,
   (keep 5843 (by omega) (by omega) (by omega)).trans hP,
   (keep 5844 (by omega) (by omega) (by omega)).trans hW,
   (keep 5845 (by omega) (by omega) (by omega)).trans hU,
   (keep 5846 (by omega) (by omega) (by omega)).trans hA,
   post.rowBase,
   (keep 5848 (by omega) (by omega) (by omega)).trans hD,
   (keep 5849 (by omega) (by omega) (by omega)).trans hkind,post.count⟩
 have geometry:=dispatched_geometry c q slot l bl ha he
 obtain ⟨d,done⟩:=UniformProducedMatchingSlotDirectory.from_rows x dirReady
  (printedRows c q slot l bl ha he) positive geometry.1 geometry.2.1 geometry.2.2 dargs post.table
  rowsEnd permutationEnd widthsEnd markersEnd axisEnd directoryEnd (by omega) rfl directoryBound
 have third:=UniformBoundedAssembly.boundedExecution_placed directory_code
  (by rw [D.program,UniformLocalMatchingSlotDirectory.program_length];omega) (by omega) done.execution
 have directoryStart:placed 1245 dirReady=setPC b 1245:=rfl
 rw [directoryStart] at third
 let u:=setPC d 1325
 have combined:BoundedRuns program n x B s
  (69+UniformLocalReplaySlotMachine.bit slot.enabled+bt+(UniformMatchingAxisTableMachine.runtime c.ambient
   (printedRows c q slot l bl ha he).length+25)) u:=by
  simpa only [u,setPC] using (first.trans second).trans third
 refine ⟨u,_,combined,?_,rfl,?_⟩
 · have bit:UniformLocalReplaySlotMachine.bit slot.enabled≤1:=by cases slot.enabled <;>simp [UniformLocalReplaySlotMachine.bit]
   have cheap:=done.ticks
   omega
 · refine ⟨done.entry,done.row,done.widths,done.permutation,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · simpa only [UniformGlobalDiagonalRowsMachine.Pools,UniformTensorDiagonalBankMachine.Coefficients,
      u,setPC,done.heap,dirReady] using post.factors
   · exact UniformConjugatePackedMatchingPreparation.sources_transport post.sources done.heap
   · simpa only [UniformHadamardPairMachine.Constants,u,setPC,done.heap,dirReady] using post.constants
   · exact done.outputs.trans (post.outputs.trans aout)
   · exact done.roots.trans (post.roots.trans aroot)
   · intro i low before
     exact (done.prefixHeap i before).trans ((post.natPrefix i low).trans (congrFun anh i))
   · intro i above before
     exact (done.prefixHeap i before).trans ((post.natHigh i above).trans (congrFun anh i))
   · intro i outside hm hb
     exact (congrFun done.heap i).trans ((post.scalarOutside i outside hm hb).trans (congrFun ash i))
   · intro r lo hi
     exact (UniformLocalMatchingSlotDirectory.execution_keeps_driver done.execution r lo).trans
      ((post.high r lo (Or.inl (by omega))).trans
       (UniformLocalCacheSlotHeaderMachine.driver_frame header r (Or.inl ⟨lo,by omega⟩)))
   · exact (UniformLocalMatchingSlotDirectory.execution_keeps_driver done.execution 6200 (by omega)).trans
      ((post.high 6200 (by omega) (Or.inl (by omega))).trans
       (UniformLocalCacheSlotHeaderMachine.driver_frame header 6200 (Or.inr (by omega))))
   · intro i above afterDirectory
     have high:=UniformProducedMatchingSlotDirectory.Produced.high x dirReady d
      (printedRows c q slot l bl ha he) positive geometry.1 geometry.2.1 geometry.2.2 dargs post.table
      rowsEnd permutationEnd widthsEnd markersEnd axisEnd directoryEnd (by omega) rfl directoryBound done
     exact (high i afterDirectory).trans ((post.natHigh i above).trans (congrFun anh i))

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
