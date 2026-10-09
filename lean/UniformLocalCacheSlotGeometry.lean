import UniformLocalCacheSlotInvariant

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformTensorMonomialMachine UniformLocalFactorDispatchMachine
noncomputable section

/-- All fields are integer extents/disjointness or typed index bounds. This
structure contains no generated banks, factor values, action or execution. -/
structure Geometry (B:ℕ) (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ):Prop where
 inputs:InputLayout c q
 cache:CacheLayout c
 positive:2 ≤ c.ambient
 layout:∀ j, j < 352*c.height.K+330 → ∀ slot, SlotWitness c.height.K j slot →
  UniformForwardMatchingFactorPreparation.Layout (Header.forward (Cursor.shifted c j) q slot) B
 broadcast:∀ j, j < 352*c.height.K+330 → BroadcastLayout (Cursor.shifted c j) q B
 inverse:∀ j, ∀ hj:j < 352*c.height.K+330, ∀ slot, ∀ hs:SlotWitness c.height.K j slot,
  UniformInverseMatchingFactorPreparation.InverseLayout (Header.forward (Cursor.shifted c j) q slot)
   (layout j hj slot hs) I
 rows:∀ j, ∀ hj:j < 352*c.height.K+330, ∀ slot, ∀ hs:SlotWitness c.height.K j slot,
  printedBase (Cursor.shifted c j) slot I+
   3*(printedRows (Cursor.shifted c j) q slot (layout j hj slot hs) (broadcast j hj) ha he).length
    ≤ (Cursor.shifted c j).cachePermutation
 natEnd:∀ j, ∀ hj:j < 352*c.height.K+330, ∀ slot, ∀ hs:SlotWitness c.height.K j slot,
  UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c j) q slot (layout j hj slot hs)
   (broadcast j hj) ha he I ≤ c.cachePermutation
 permutation:c.cachePermutation+c.ambient ≤ c.cacheWidths
 widths:c.cacheWidths+c.ambient ≤ c.cacheMarkers
 markers:c.cacheMarkers+c.ambient ≤ c.cacheAxis
 axis:c.cacheAxis+4 ≤ c.cacheDirectory
 rectangle:c.rectangle+6 ≤ B
 slots:∀ j, j < 352*c.height.K+330 → (Cursor.shifted c j).slot+4 ≤ B
 directories:∀ j, j < 352*c.height.K+330 → (Cursor.shifted c j).cacheDirectory+7 ≤ B
 mu:c.mu < c.pool
 conjugateMu:c.conjugateMu < c.pool
 endpoints:∀ j, j ≤ 352*c.height.K+330 →
  (Cursor.shifted c j).slot ≤ B ∧(Cursor.shifted c j).pool ≤ B ∧(Cursor.shifted c j).time ≤ B ∧
  (Cursor.shifted c j).cachePermutation ≤ B ∧(Cursor.shifted c j).cacheWidths ≤ B ∧
  (Cursor.shifted c j).cacheMarkers ≤ B ∧(Cursor.shifted c j).cacheAxis ≤ B ∧
  (Cursor.shifted c j).cacheDirectory ≤ B

lemma cache_shift {c:Header.Parameters} (h:CacheLayout c) (j:ℕ):CacheLayout (Cursor.shifted c j):=by
 rcases h with ⟨a,b,d,e,f,g,k⟩
 constructor <;>simp only [Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters] <;>omega

/-- Every cached ordinal is tied to an actual six-phase physical control. -/
def Cached {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ) (positive:2 ≤ c.ambient) (j:ℕ) (s:State):Prop:=
 ∃slot,SlotWitness c.height.K j slot ∧
 ∃l:UniformForwardMatchingFactorPreparation.Layout (Header.forward (Cursor.shifted c j) q slot) B,
 ∃bl:BroadcastLayout (Cursor.shifted c j) q B,
 Contents (Cursor.shifted c j) q slot l bl ha he bank positive s

lemma Cached.heaps {B c q ha he bank positive j s u}
 (h:@Cached B c q ha he bank positive j s) (layout:CacheLayout (Cursor.shifted c j))
 (nat:u.natHeap=s.natHeap) (scalar:u.scalarHeap=s.scalarHeap):Cached (B:=B) c q ha he bank positive j u:=by
 obtain ⟨slot,hs,l,bl,contents⟩:=h
 exact ⟨slot,hs,l,bl,contents.transport layout (fun i _ _=>congrFun nat i) (fun i _ _=>congrFun scalar i)⟩

/-- New slot writes retain the complete physical contents of every earlier
slot, including all nine prepared factor lanes and partition/permutation rows. -/
lemma Cached.afterStored {B:ℕ} {c:Header.Parameters} {q:UniformLocalRectangleDescriptors.Row}
 {ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height}
 {he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height} {I:ℕ}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ} {positive:2 ≤ c.ambient}
 {j k:ℕ} {slot:UniformLocalCacheChronology.Slot} {s u:State}
 {l:UniformForwardMatchingFactorPreparation.Layout (Header.forward (Cursor.shifted c j) q slot) B}
 {bl:BroadcastLayout (Cursor.shifted c j) q B}
 (h:Cached (B:=B) c q ha he bank positive k s) (earlier:k < j) (cache:CacheLayout c)
 (mu:c.mu < c.pool) (bar:c.conjugateMu < c.pool)
 (natEnd:UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c j) q slot l bl ha he I ≤ c.cachePermutation)
 (post:Stored (Cursor.shifted c j) q slot l bl ha he I bank positive s u):
 Cached (B:=B) c q ha he bank positive k u:=by
 obtain ⟨old,hs,ll,bb,contents⟩:=h
 refine ⟨old,hs,ll,bb,contents.transport (cache_shift cache k) ?_ ?_⟩
 · intro i low high
   have start:c.cachePermutation ≤ i:=by
    change c.cachePermutation+(3*c.ambient+11)*k ≤ i at low;omega
   have order:=Nat.mul_le_mul_left (3*c.ambient+11) (show k+1 ≤ j by omega)
   simp only [Nat.mul_add,Nat.mul_one] at order
   apply post.cached i (natEnd.trans start)
   change i < c.cachePermutation+(3*c.ambient+11)*j
   change i < c.cachePermutation+(3*c.ambient+11)*k+(3*c.ambient+11) at high
   omega
 · intro i low high
   have start:c.pool ≤ i:=by
    change c.pool+9*c.ambient*k ≤ i at low;omega
   have order:=Nat.mul_le_mul_left (9*c.ambient) (show k+1 ≤ j by omega)
   simp only [Nat.mul_add,Nat.mul_one] at order
   apply post.scalarOutside i (Or.inl ?_) (by change i≠c.mu;omega) (by change i≠c.conjugateMu;omega)
   change i < c.pool+9*c.ambient*j
   change i < c.pool+9*c.ambient*k+9*c.ambient at high
   omega

/-- A coarse linear per-slot charge; it includes74/1156/80, every actual
producer branch and the matching partition scan. -/
def bodyBudget (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row):ℕ:=
 4*c.height.K+191*q.width+227*c.ambient+304

lemma body_cost {B:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl:BroadcastLayout c q B) (ha he):
 runtimeBudget c q slot l bl ha he+21*c.ambient+116 ≤ bodyBudget c q:=by
 have geometry:=dispatched_geometry c q slot l bl ha he
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.ambient
  (UniformGlobalMatchingScaleBankBridge.rowEdges (printedRows c q slot l bl ha he) geometry.2.1)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_matching _ _ geometry.2.2)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_range c.ambient _ _ geometry.1)
 have count:UniformLocalBroadcastPoolMachine.count q slot ≤ q.a:=by
  rcases UniformLocalBroadcastPoolMachine.count_cases q slot with h|h <;>omega
 have ar:q.a ≤ c.ambient:=by have:=bl.capacity;have:=l.extent;change q.offset+q.width ≤ c.ambient at this;omega
 cases broadcast:slot.broadcast <;>cases inverse:slot.inverse
 all_goals simp only [printedRows,broadcast,inverse,Bool.false_eq_true,ite_false,ite_true] at cap
 all_goals simp only [runtimeBudget,broadcast,inverse,Bool.false_eq_true,ite_false,ite_true,bodyBudget]
 all_goals omega

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
