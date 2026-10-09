import UniformLocalFactorDispatchBoot
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFactorDispatchMachine
open UniformMachine UniformTensorMonomialMachine
namespace F
abbrev Config:=UniformForwardMatchingFactorPreparation.Config
abbrev Layout:=UniformForwardMatchingFactorPreparation.Layout
end F
noncomputable section
variable {B:ℕ}
structure BroadcastLayout (c:H.Parameters) (q:Rectangle) (B:ℕ):Prop where
 capacity:c.gates+q.e+q.a≤q.width
 outputCount:q.a≤c.gates
 sourceRange:q.j0+q.e≤q.width
 targetRange:q.i0+q.a≤q.width
 borrowedFresh:c.borrowed+c.gates≤c.mapped
 mappedFresh:c.mapped+3*q.a≤c.translated
 translatedBound:c.translated+3*q.a≤B
 rectangleBound:c.rectangle+6≤B
 slotBound:c.slot+4≤B
def broadcastEntry (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B):
 UniformGlobalDiagonalRowsMachine.Entry where
 radix:=c.ambient
 positive:=l.ambientPositive
 pool:=c.pool
 value:=fun lane d=>UniformGlobalMatchingScaleBankBridge.nativeFactor
  (UniformGlobalMatchingScaleBankBridge.rowEdges
   (UniformLocalBroadcastPoolMachine.rows q slot c.gates c.height.P bl.capacity)
   (UniformLocalBroadcastPoolMachine.different q slot c.gates c.height.P bl.capacity bl.outputCount))
  (fun _=>if slot.inverse then (-1:ℂ) else 1) lane d.val
lemma broadcast_tensor_pool {c:H.Parameters} {q:Rectangle} {slot:Slot}
 {l:F.Layout (H.forward c q slot) B} {bl:BroadcastLayout c q B}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ} {u:State}
 (h:UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=c.height.K) c.pool c.ambient
  (UniformLocalBroadcastPoolMachine.rows q slot c.gates c.height.P bl.capacity)
  bank (UniformLocalBroadcastPoolMachine.coefficients q slot c.gates c.height.P bl.capacity)
  (UniformLocalBroadcastPoolMachine.rows q slot c.gates c.height.P bl.capacity).length u):
 UniformGlobalDiagonalRowsMachine.Pools [broadcastEntry c q slot l bl] u := by
 intro entry member lane d
 have eq:entry=broadcastEntry c q slot l bl:=by simpa only [List.mem_singleton] using member
 subst entry
 have pool:=UniformGlobalMatchingScaleBankBridge.pool_coefficients
  (UniformLocalBroadcastPoolMachine.different q slot c.gates c.height.P bl.capacity bl.outputCount)
  (UniformLocalBroadcastPoolMachine.matching q slot c.gates c.height.P bl.capacity bl.outputCount) h lane
 have values:(fun i=>UniformMatchingConjugateLoadMachine.value c.height.K bank
   (UniformLocalBroadcastPoolMachine.coefficients q slot c.gates c.height.P bl.capacity i))=
   (fun _=>if slot.inverse then (-1:ℂ) else 1):=by
  funext i;exact UniformLocalBroadcastPoolMachine.coefficient_value c.height.K bank slot
 rw [values] at pool
 exact pool d
/-- The entry retains its actual coefficient formula in each branch. Inverse
rows have reversed order and negated typed leaves; broadcasts have signed1. -/
def entry (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B) (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ):UniformGlobalDiagonalRowsMachine.Entry :=
 if slot.broadcast then broadcastEntry c q slot l bl
 else if slot.inverse then UniformInverseMatchingFactorPreparation.poolEntry (H.forward c q slot) l ha he bank
 else UniformForwardMatchingFactorPreparation.poolEntry (H.forward c q slot) l ha he bank
def printedRows (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B) (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height):List UniformInPlaceMachine.Row :=
 if slot.broadcast then UniformLocalBroadcastPoolMachine.rows q slot c.gates c.height.P bl.capacity
 else if slot.inverse then UniformInverseMatchingFactorPreparation.rows (H.forward c q slot) l ha he
 else UniformForwardMatchingFactorPreparation.rows (H.forward c q slot) l ha he
def printedBase (c:H.Parameters) (slot:Slot) (I:ℕ):ℕ:=
 if slot.broadcast then c.translated else if slot.inverse then I else c.translated
def runtimeBudget (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (_bl:BroadcastLayout c q B) (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height):ℕ:=
 if slot.broadcast then 11*q.width+45*c.ambient+150*UniformLocalBroadcastPoolMachine.count q slot+83
 else if slot.inverse then 4*c.height.K+180*q.width+45*c.ambient+
  161*(UniformInverseMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length+188
 else 4*c.height.K+180*q.width+45*c.ambient+
  136*(UniformForwardMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length+173
def natEnd (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (_bl:BroadcastLayout c q B)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height) (I:ℕ):ℕ:=
 if slot.broadcast then c.translated+3*q.a
 else if slot.inverse then I+3*(UniformInverseMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length
 else c.translated+3*(UniformForwardMatchingFactorPreparation.rows (H.forward c q slot) l ha he).length
structure Result (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B) (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (H.forward c q slot).chunk.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ) (s u:State):Prop where
 factors:UniformGlobalDiagonalRowsMachine.Pools [entry c q slot l bl ha he bank] u
 table:UniformCrossShearTableMachine.Table (printedBase c slot I) (printedRows c q slot l bl ha he) u
 rowBase:u.natReg 5847=printedBase c slot I
 count:u.natReg 894=(printedRows c q slot l bl ha he).length
 sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative
  c.height.P c.conjugates bank u
 constants:UniformHadamardPairMachine.Constants u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natPrefix:∀ (i : ℕ), i < c.borrowed → u.natHeap i=s.natHeap i
 natHigh:∀ (i : ℕ), natEnd c q slot l bl ha he I ≤ i → u.natHeap i=s.natHeap i
 scalarOutside:∀ (i : ℕ), (i < c.pool ∨ c.pool+9*c.ambient ≤ i) → i ≠ c.mu → i ≠ c.conjugateMu → 
  u.scalarHeap i=s.scalarHeap i
 saved:∀ (i : ℕ), 100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i
 cacheHeaders:∀ (i : ℕ), 5840 ≤ i → i ≤ 5849 → i≠5847 → u.natReg i=s.natReg i
 high:∀ (i : ℕ), 6100 ≤ i → i < 6210 ∨ 6214 < i → u.natReg i=s.natReg i
lemma Result.withPC {c:H.Parameters} {q:Rectangle} {slot:Slot}
 {l:F.Layout (H.forward c q slot) B} {bl:BroadcastLayout c q B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ} {s u:State}
 (h:Result c q slot l bl ha he I bank s u) (pc:ℕ):
 Result c q slot l bl ha he I bank s (setPC u pc) := by
 refine ⟨?_,?_,h.rowBase,h.count,⟨h.sources.positive,h.sources.negative,
  h.sources.conjugate,h.sources.constants⟩,h.constants,h.outputs,h.roots,
  h.natPrefix,h.natHigh,h.scalarOutside,h.saved,h.cacheHeaders,h.high⟩
 · intro e member lane j;exact h.factors e member lane j
 · intro i;exact h.table i
lemma entry_radix (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ):
 (entry c q slot l bl ha he bank).radix=c.ambient := by
 cases hb:slot.broadcast <;>cases hi:slot.inverse <;>
  simp [entry,hb,hi,broadcastEntry,UniformForwardMatchingFactorPreparation.poolEntry,
   UniformInverseMatchingFactorPreparation.poolEntry,H.forward,UniformLocalCacheSlotHeaderMachine.forward]
lemma entry_pool (c:H.Parameters) (q:Rectangle) (slot:Slot)
 (l:F.Layout (H.forward c q slot) B) (bl:BroadcastLayout c q B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ):
 (entry c q slot l bl ha he bank).pool=c.pool := by
 cases hb:slot.broadcast <;>cases hi:slot.inverse <;>
  simp [entry,hb,hi,broadcastEntry,UniformForwardMatchingFactorPreparation.poolEntry,
   UniformInverseMatchingFactorPreparation.poolEntry,H.forward,UniformLocalCacheSlotHeaderMachine.forward]
end
end ExactFourierCircuits.UniformLocalFactorDispatchMachine
