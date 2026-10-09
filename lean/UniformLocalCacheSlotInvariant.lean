import UniformLocalCacheSlotExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformTensorMonomialMachine
open UniformLocalFactorDispatchMachine
noncomputable section

/-- These two banks are produced by2308; neither is a per-slot callback. -/
def enabledHeight (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row) (enabled:Bool):
 UniformCrossHeightPreparationMachine.Parameters:=
 UniformLocalCacheSlotHeaderMachine.selectedHeight c q ⟨false,enabled,false,0,0⟩

def SlotWitness (K j:ℕ) (slot:UniformLocalCacheChronology.Slot):Prop:=
 ∃p:Fin 6,∃t:ℕ,j=11*UniformLocalReplayAssembly.phasePrefix (8*K+6) p.val+t ∧
 t < 11*UniformLocalReplayAssembly.levels (8*K+6) p ∧
 slot=UniformLocalReplaySlotMachine.decodedSlot (8*K+6)
  (UniformLocalReplayAssembly.flags p).broadcast (UniformLocalReplayAssembly.flags p).enabled
  (UniformLocalReplayAssembly.flags p).inverse (t/11) (t%11)

structure Inputs (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ) (s:State):Prop where
 rectangle:UniformLocalRectangleBankMachine.RowSource c.rectangle q s
 generated:UniformLocalReplayAssembly.Generated c.height.K c.slot 6 s
 enabled:UniformCrossHeightPreparationMachine.Processed (enabledHeight c q true) c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s
 disabled:UniformCrossHeightPreparationMachine.Processed (enabledHeight c q false) c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s
 sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank s
 constants:UniformHadamardPairMachine.Constants s
 inverse:s.natReg 6200=I

/-- Ordinary footprint geometry suffices to retain both genuine height banks,
the actual rectangle and all physically generated phase controls. -/
structure InputLayout (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row):Prop where
 rectangle:c.rectangle+7 ≤ c.borrowed
 controls:c.slot+55*UniformLocalReplayAssembly.phasePrefix (8*c.height.K+6) 6 ≤ c.borrowed
 enabled:UniformCrossHeightPreparationMachine.Layout (enabledHeight c q true)
 disabled:UniformCrossHeightPreparationMachine.Layout (enabledHeight c q false)
 enabledEnd:UniformCrossHeightPreparationMachine.recordBase (enabledHeight c q true)
  (UniformCrossHeightPreparationMachine.height c.height) ≤ c.borrowed
 disabledEnd:UniformCrossHeightPreparationMachine.recordBase (enabledHeight c q false)
  (UniformCrossHeightPreparationMachine.height c.height) ≤ c.borrowed
 cache:c.borrowed ≤ c.cachePermutation

lemma Inputs.withPC {c q ha he I bank s} (h:Inputs c q ha he I bank s) (pc:ℕ):
 Inputs c q ha he I bank (setPC s pc):=
 ⟨h.rectangle,h.generated.withPC pc,h.enabled,h.disabled,
  ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩,h.constants,h.inverse⟩

lemma Inputs.transport {c q ha he I bank s u} (h:Inputs c q ha he I bank s)
 (layout:InputLayout c q) (heap:∀i,i < c.borrowed → u.natHeap i=s.natHeap i)
 (scalar:u.scalarHeap=s.scalarHeap) (inverse:u.natReg 6200=s.natReg 6200):
 Inputs c q ha he I bank u:=by
 have size: (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q true):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q true) ha he
 have sizeFalse: (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q false):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q false) ha he
 refine ⟨?_,h.generated.transport (fun i hi=>heap i (lt_of_lt_of_le hi layout.controls)),?_,?_,?_,?_,inverse.trans h.inverse⟩
 · intro f;exact (heap _ (by have:=f.isLt;have:=layout.rectangle;omega)).trans (h.rectangle f)
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.enabled size layout.enabled
    (fun i hi=>heap i (lt_of_lt_of_le hi layout.enabledEnd))
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.disabled sizeFalse layout.disabled
    (fun i hi=>heap i (lt_of_lt_of_le hi layout.disabledEnd))
 · exact UniformConjugatePackedMatchingPreparation.sources_transport h.sources scalar
 · simpa only [UniformHadamardPairMachine.Constants,scalar] using h.constants

lemma Inputs.processed {c q ha he I bank s} (h:Inputs c q ha he I bank s)
 (j:ℕ) (slot:UniformLocalCacheChronology.Slot):
 UniformCrossHeightPreparationMachine.Processed (Header.forward (Cursor.shifted c j) q slot).chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s:=by
 change UniformCrossHeightPreparationMachine.Processed (enabledHeight c q slot.enabled) c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s
 cases enabled:slot.enabled with
 | true=>exact h.enabled
 | false=>exact h.disabled

lemma Inputs.slot {c q ha he I bank s} (h:Inputs c q ha he I bank s) {j:ℕ}
 (hj:j < 352*c.height.K+330):∃slot,
 SlotWitness c.height.K j slot ∧
 UniformLocalBroadcastPoolMachine.SlotSource (Cursor.shifted c j).slot slot s:=by
 obtain ⟨p,t,jt,tl,record⟩:=UniformLocalReplayStoredSlots.generated_slot h.generated
  (by rw [UniformLocalReplayStoredSlots.slot_count];exact hj)
 exact ⟨_,⟨p,t,jt,tl,rfl⟩,record⟩

/-- A produced slot exposes real physical contents. Its proof witnesses retain
only ordinary allocation geometry, never an action or complete-table premise. -/
structure Contents {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ) (positive:2 ≤ c.ambient) (s:State):Prop where
 abi:UniformLocalMatchingSlotDirectory.Entry c.cacheDirectory c.time c.ambient c.pool
  (c.ambient-(printedRows c q slot l bl ha he).length) c.cacheWidths c.cachePermutation c.kind s
 row:UniformSectorPackingMachine.Rows [slotAxis c q slot l bl ha he positive] 0 c.cacheAxis s
 widths:UniformSectorPackingMachine.Widths [slotAxis c q slot l bl ha he positive] s
 permutation:UniformSectorPackingMachine.Permutations [slotAxis c q slot l bl ha he positive] s
 factors:UniformGlobalDiagonalRowsMachine.Pools [entry c q slot l bl ha he bank] s

lemma Stored.contents {B c q slot l bl ha he I bank positive s u}
 (h:@Stored B c q slot l bl ha he I bank positive s u):Contents c q slot l bl ha he bank positive u:=
 ⟨h.abi,h.row,h.widths,h.permutation,h.factors⟩

lemma Contents.withPC {B c q slot l bl ha he bank positive s}
 (h:@Contents B c q slot l bl ha he bank positive s) (pc:ℕ):Contents c q slot l bl ha he bank positive (setPC s pc):=
 ⟨h.abi,h.row,h.widths,h.permutation,h.factors⟩

/-- Local cache rows fit one real stride; no values are assumed here. -/
structure CacheLayout (c:Header.Parameters):Prop where
 widthsLow:c.cachePermutation ≤ c.cacheWidths
 widthsHigh:c.cacheWidths+c.ambient ≤ c.cachePermutation+(3*c.ambient+11)
 permutationHigh:c.cachePermutation+c.ambient ≤ c.cachePermutation+(3*c.ambient+11)
 axisLow:c.cachePermutation ≤ c.cacheAxis
 axisHigh:c.cacheAxis+4 ≤ c.cachePermutation+(3*c.ambient+11)
 directoryLow:c.cachePermutation ≤ c.cacheDirectory
 directoryHigh:c.cacheDirectory+7 ≤ c.cachePermutation+(3*c.ambient+11)

lemma axis_bounds {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B) (ha he) (positive:2 ≤ c.ambient):
 (slotAxis c q slot l bl ha he positive).geometry.widths.length ≤ c.ambient ∧
 (slotAxis c q slot l bl ha he positive).geometry.widths.sum=c.ambient:=by
 let rows:=printedRows c q slot l bl ha he
 let diff:= (dispatched_geometry c q slot l bl ha he).2.1
 let E:=UniformGlobalMatchingScaleBankBridge.rowEdges rows diff
 have hm:=UniformGlobalMatchingScaleBankBridge.rowEdges_matching rows diff
  (dispatched_geometry c q slot l bl ha he).2.2
 have hr:=UniformGlobalMatchingScaleBankBridge.rowEdges_range c.ambient rows diff
  (dispatched_geometry c q slot l bl ha he).1
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.ambient E hm hr
 change (UniformMatchingAxisTableMachine.widths c.ambient rows.length).length ≤ c.ambient ∧
  (UniformMatchingAxisTableMachine.widths c.ambient rows.length).sum=c.ambient
 rw [UniformMatchingAxisTableMachine.widths_length _ _ cap,
  UniformMatchingAxisTableMachine.widths_sum _ _ cap]
 exact ⟨Nat.sub_le _ _,rfl⟩

lemma Contents.transport {B:ℕ} {c:Header.Parameters} {q:UniformLocalRectangleDescriptors.Row}
 {slot:UniformLocalCacheChronology.Slot}
 {l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B}
 {bl:BroadcastLayout c q B} {ha he}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ} {positive:2 ≤ c.ambient} {s u:State}
 (h:Contents c q slot l bl ha he bank positive s) (layout:CacheLayout c)
 (nat:∀ i, c.cachePermutation ≤ i → i < c.cachePermutation+(3*c.ambient+11) → u.natHeap i=s.natHeap i)
 (scalar:∀ i, c.pool ≤ i → i < c.pool+9*c.ambient → u.scalarHeap i=s.scalarHeap i):
 Contents c q slot l bl ha he bank positive u:=by
 have axis:=axis_bounds c q slot l bl ha he positive
 refine ⟨?_,?_,?_,?_,?_⟩
 · rcases h.abi with ⟨a,b,d,e,f,g,k⟩
   exact ⟨(nat _ layout.directoryLow (by have:=layout.directoryHigh;omega)).trans a,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans b,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans d,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans e,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans f,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans g,
    (nat _ (by have:=layout.directoryLow;omega) (by have:=layout.directoryHigh;omega)).trans k⟩
 · rcases h.row with ⟨a,b,d,e,_⟩
   refine ⟨?_,?_,?_,?_,True.intro⟩
   · exact (nat _ (by have:=layout.axisLow;omega) (by have:=layout.axisHigh;omega)).trans a
   · exact (nat _ (by have:=layout.axisLow;omega) (by have:=layout.axisHigh;omega)).trans b
   · exact (nat _ (by have:=layout.axisLow;omega) (by have:=layout.axisHigh;omega)).trans d
   · exact (nat _ (by have:=layout.axisLow;omega) (by have:=layout.axisHigh;omega)).trans e
 · intro a member j
   have eq:a=slotAxis c q slot l bl ha he positive:=by simpa only [List.mem_singleton] using member
   subst a
   have hj:=j.isLt
   change u.natHeap (c.cacheWidths+j.val)=_
   exact (nat _ (by have:=layout.widthsLow;omega) (by have:=layout.widthsHigh;omega)).trans (h.widths _ (by simp) j)
 · intro a member j
   have eq:a=slotAxis c q slot l bl ha he positive:=by simpa only [List.mem_singleton] using member
   subst a
   have hj:=j.isLt
   change u.natHeap (c.cachePermutation+j.val)=_
   exact (nat _ (by omega) (by have:=layout.permutationHigh;omega)).trans (h.permutation _ (by simp) j)
 · intro a member lane j
   have eq:a=entry c q slot l bl ha he bank:=by simpa only [List.mem_singleton] using member
   subst a
   have hj : j.val < c.ambient := by simpa only [entry_radix] using j.isLt
   have address : (entry c q slot l bl ha he bank).pool + lane.val*(entry c q slot l bl ha he bank).radix+j.val=
    c.pool+lane.val*c.ambient+j.val := by simp only [entry_pool,entry_radix]
   have multiple := Nat.mul_le_mul_right c.ambient (show lane.val ≤ 8 by have:=lane.isLt;omega)
   exact (scalar _ (by rw [address];omega) (by rw [address];omega)).trans
    (h.factors _ (by simp) lane j)

lemma Inputs.transport_banks {c q ha he I bank s u} (h:Inputs c q ha he I bank s)
 (layout:InputLayout c q) (heap:∀ i, i < c.borrowed → u.natHeap i=s.natHeap i)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank u)
 (constants:UniformHadamardPairMachine.Constants u) (inverse:u.natReg 6200=s.natReg 6200):
 Inputs c q ha he I bank u:=by
 have size: (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q true):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q true) ha he
 have sizeFalse: (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q false):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q false) ha he
 refine ⟨?_,h.generated.transport (fun i hi=>heap i (lt_of_lt_of_le hi layout.controls)),?_,?_,sources,constants,inverse.trans h.inverse⟩
 · intro f;exact (heap _ (by have:=f.isLt;have:=layout.rectangle;omega)).trans (h.rectangle f)
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.enabled size layout.enabled
    (fun i hi=>heap i (lt_of_lt_of_le hi layout.enabledEnd))
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.disabled sizeFalse layout.disabled
    (fun i hi=>heap i (lt_of_lt_of_le hi layout.disabledEnd))

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
