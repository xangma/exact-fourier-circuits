import UniformActualCalendarBroadcastSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBroadcastReverse
open UniformReplayPrint UniformToeplitzChunkWord UniformDAGLayers
open UniformActualCalendarTypedSlots UniformLocalCacheChronology
open UniformLocalFactorDispatchMachine (BroadcastLayout)
open UniformLocalCacheSlotConductorMachine (SlotWitness)
noncomputable section

theorem pack_reverse {r e g a : ℕ} (positive : 0<e)
 (W : List (ShearCode ℕ r)) (stored : ∀s∈W,Stored e g a s)
 (back : ∀s∈W.reverse,Stored e g a s) :
 packList positive W.reverse back=(packList positive W stored).reverse:=by
 induction W with
 | nil=>rfl
 | cons s W ih=>
  have sb : ∀code∈W.reverse++[s],Stored e g a code:=by
   intro code hc
   exact back code (by simpa only[List.reverse_cons] using hc)
  refine (UniformActualCalendarWitnessSlots.packList_congr positive List.reverse_cons back sb).trans ?_
  rw[packList_append]
  simp only[packList,List.reverse_cons]
  rw[ih]

theorem canonical_gate {r v s e t a g h : ℕ} (eq : g=h)
 (source : s+e ≤ v) (target : t+a ≤ v) (sep : s+e ≤ t ∨ t+a ≤ s)
 (fg : g+e+a≤v) (fh : h+e+a≤v) (positive : 0<e)
 (W : List (ShearCode ℕ r))
 (sg : ∀code∈W,Stored e g a code) (sh : ∀code∈W,Stored e h a code) :
 (packList positive W sg).map
  (relabelCode (placementOfFit (g:=g)
   (UniformChunkPortMachine.intervalEmbedding v s e source)
   (UniformChunkPortMachine.intervalEmbedding v t a target)
   (UniformBorrowedCoordinateBridge.interval_separated source target sep) (by omega)).embedding)=
 (packList positive W sh).map
  (relabelCode (placementOfFit (g:=h)
   (UniformChunkPortMachine.intervalEmbedding v s e source)
   (UniformChunkPortMachine.intervalEmbedding v t a target)
   (UniformBorrowedCoordinateBridge.interval_separated source target sep) (by omega)).embedding):=by
 subst h
 rfl

theorem pack_relabel_reverse {r e g a v : ℕ} (positive : 0<e) (P : Placement e g a v)
 (W : List (ShearCode ℕ r)) (stored : ∀s∈W,Stored e g a s)
 (back : ∀s∈W.reverse,Stored e g a s) :
 (packList positive W.reverse back).map (relabelCode P.embedding)=
 ((packList positive W stored).map (relabelCode P.embedding)).reverse:=
 (congrArg (fun W=>W.map (relabelCode P.embedding)) (pack_reverse positive W stored back)).trans
  List.map_reverse

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row) (slot : Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)

/-- The only broadcast discrepancy is literal occurrence reversal in the
inverse slot; packing and the actual complement coordinate scan preserve it. -/
theorem normal_typed {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) :
 typedSlot c q slot (8*c.height.K+6) l ha he positive
  (UniformActualCalendarWitnessSlots.stored c q slot ha he h)=
 if slot.inverse then
  (UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast).reverse
 else UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast:=by
 let C:=UniformActualCalendarBroadcastSlots.codes c q slot bl
 have sn : ∀code∈C,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code:=by
  rw[←gates]
  exact UniformActualCalendarBroadcastSlots.stored c q slot bl ha he h gates broadcast
 have canon : (packList positive C sn).map
   (relabelCode (placement (Header.forward c q slot).chunk l.chunk).embedding)=
   UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast:=by
  exact (canonical_gate gates bl.sourceRange bl.targetRange l.chunk.separated
   bl.capacity l.chunk.capacity positive C
   (UniformActualCalendarBroadcastSlots.stored c q slot bl ha he h gates broadcast) sn).symm
 have shape:=UniformActualCalendarBroadcastSlots.normal c q slot bl ha he gates broadcast (8*c.height.K+6)
 cases inverse:slot.inverse
 · have eq : slotCodes c q slot (8*c.height.K+6) ha he=C:=by
    simpa only[inverse,Bool.false_eq_true,ite_false] using shape
   simp only[Bool.false_eq_true,ite_false]
   unfold typedSlot
   exact (congrArg (fun W=>W.map (relabelCode (placement (Header.forward c q slot).chunk l.chunk).embedding))
    (UniformActualCalendarWitnessSlots.packList_congr positive eq _ sn)).trans canon
 · have sb : ∀code∈C.reverse,Stored q.e
     (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code:=by
    intro code hc;exact sn code (List.mem_reverse.mp hc)
   have eq : slotCodes c q slot (8*c.height.K+6) ha he=C.reverse:=by
    simpa only[inverse,ite_true] using shape
   simp only[ite_true]
   unfold typedSlot
   refine (congrArg (fun W=>W.map (relabelCode (placement (Header.forward c q slot).chunk l.chunk).embedding))
    (UniformActualCalendarWitnessSlots.packList_congr positive eq _ sb)).trans ?_
   exact (pack_relabel_reverse (e:=q.e) (a:=q.a) positive
    (placement (Header.forward c q slot).chunk l.chunk) C sn sb).trans (congrArg List.reverse canon)

end
end ExactFourierCircuits.UniformActualCalendarBroadcastReverse
