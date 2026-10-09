import UniformActualCalendarRectangleSources
import UniformReplaySlotWitness

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarWitnessSlots
open UniformReplayPrint UniformToeplitzChunkWord UniformDAGLayers
open UniformActualCalendarTypedSlots UniformLocalCacheChronology
open UniformLocalCacheSlotConductorMachine (SlotWitness)
noncomputable section

theorem packLayers_get {r e g a : ℕ} (positive : 0<e)
 (L : List (List (ShearCode ℕ r)))
 (stored : ∀s∈L.flatten,Stored e g a s) (j : ℕ) (hj : j<L.length) :
 (packLayers positive L stored).get ⟨j,by simpa using hj⟩=
 packList positive (L.get ⟨j,hj⟩)
  (fun s hs=>stored s (List.mem_flatten.mpr ⟨L.get ⟨j,hj⟩,List.get_mem _ _,hs⟩)):=by
 induction L generalizing j with
 | nil => simp at hj
 | cons W L ih =>
  cases j with
  | zero => rfl
  | succ j =>
   exact ih (fun s hs=>stored s (by simp only[List.flatten_cons,List.mem_append];exact Or.inr hs)) j
    (by simpa using hj)

def castPlacement {e g h a v : ℕ} (eq : g=h) (P : Placement e g a v) : Placement e h a v:=
 eq ▸ P

theorem pack_relabel_cast {r e g h a v : ℕ} (eq : g=h) (positive : 0<e)
 (P : Placement e g a v) (W : List (ShearCode ℕ r))
 (sg : ∀s∈W,Stored e g a s) (sh : ∀s∈W,Stored e h a s) :
 (packList positive W sg).map (relabelCode P.embedding)=
 (packList positive W sh).map (relabelCode (castPlacement eq P).embedding):=by
 subst h
 rfl

theorem packList_congr {r e g a : ℕ} (positive : 0<e)
 {W U : List (ShearCode ℕ r)} (eq : W=U)
 (sw : ∀s∈W,Stored e g a s) (su : ∀s∈U,Stored e g a s) :
 packList positive W sw=packList positive U su:=by
 subst U
 rfl

theorem chunkLayers_get {r e a v H delta : ℕ}
 (D : UniformToeplitzCrossDAG.DAG r e a) (positive : 0<e) (P : Placement e D.size a v)
 (depth : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
 (fanout : ∀i,UniformToeplitzCrossDAG.physicalUseCount D i≤delta)
 (j : ℕ) (hj : j<(replayLayers D H delta).length) :
 (chunkLayers D positive P depth hd fanout).get ⟨j,by simpa using hj⟩=
 (packList positive ((replayLayers D H delta).get ⟨j,hj⟩)
  (fun s hs=>replayLayers_stored D depth hd fanout s
   (List.mem_flatten.mpr ⟨_,List.get_mem _ _,hs⟩))).map (relabelCode P.embedding):=by
 unfold chunkLayers relabelLayers
 simpa only[List.get_eq_getElem,List.getElem_map] using
  congrArg (fun W=>W.map (relabelCode P.embedding))
   (packLayers_get positive (replayLayers D H delta) (replayLayers_stored D depth hd fanout) j hj)

variable (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row) (slot : Slot)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)

/-- A genuine cached slot inherits stored endpoint bounds from the actual DAG. -/
theorem stored {j : ℕ} (h : SlotWitness c.height.K j slot) :
 ∀code∈slotCodes c q slot (8*c.height.K+6) ha he,Stored q.e
  (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code:=by
 let D:=UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he
 have hi:=UniformReplaySlotWitness.layer_bound D h
 have get:=UniformReplaySlotWitness.layer_get D h hi
 have bound:=replayLayers_stored D
  (UniformToeplitzCrossDAG.crossDAG_depth c.height.K q.a q.e ha he) (by omega : 2≤6)
  (UniformToeplitzCrossDAG.crossDAG_physicalFanout c.height.K q.a q.e ha he)
 have size:=UniformCrossHeightPreparationMachine.cross_size (Header.forward c q slot).chunk.height ha he
 intro code hc
 rw[←size]
 apply bound code
 apply List.mem_flatten.mpr
 refine ⟨(replayLayers D (8*c.height.K+6) 6).get ⟨j,hi⟩,List.get_mem _ _,?_⟩
 rw[get]
 exact hc

/-- Matching is derived from the cached ordinal and actual DAG fanout. -/
theorem matching {j : ℕ} (h : SlotWitness c.height.K j slot) :
 UniformDAGLayers.Matching (slotCodes c q slot (8*c.height.K+6) ha he):=by
 let D:=UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he
 have hi:=UniformReplaySlotWitness.layer_bound D h
 have get:=UniformReplaySlotWitness.layer_get D h hi
 have hm:=replayLayers_matching (H:=8*c.height.K+6) D (by omega : 2≤6)
  (UniformToeplitzCrossDAG.crossDAG_physicalFanout c.height.K q.a q.e ha he)
 change UniformDAGLayers.Matching (layer D (8*c.height.K+6) slot)
 rw[←get]
 exact hm _ (List.get_mem _ _)

def dag := UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he

theorem dag_depth : UniformToeplitzCrossDAG.DepthBound (dag c q slot ha he) (8*c.height.K+6):=
 UniformToeplitzCrossDAG.crossDAG_depth c.height.K q.a q.e ha he

theorem dag_fanout (i : ℕ) : UniformToeplitzCrossDAG.physicalUseCount (dag c q slot ha he) i≤6:=
 UniformToeplitzCrossDAG.crossDAG_physicalFanout c.height.K q.a q.e ha he i

theorem size : (dag c q slot ha he).size=
 UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height:=
 UniformCrossHeightPreparationMachine.cross_size (Header.forward c q slot).chunk.height ha he

variable {B : ℕ}
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)

def normalPlacement : Placement q.e (dag c q slot ha he).size q.a q.width:=
 castPlacement (size c q slot ha he).symm (placement (Header.forward c q slot).chunk l.chunk)

def chunkSlots (positive : 0<q.e) :=
 chunkLayers (dag c q slot ha he) positive (normalPlacement c q slot ha he l)
  (dag_depth c q slot ha he) (by omega : 2≤6) (dag_fanout c q slot ha he)

theorem chunkSlots_bound {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot) :
 j<(chunkSlots c q slot ha he l positive).length:=by
 unfold chunkSlots
 rw[chunkLayers_length]
 exact UniformReplaySlotWitness.layer_bound _ h

/-- Actual cached ordinal, canonical finite packing, and the normal chunk
schedule are the same typed slot, including inverse depth/color reversal. -/
theorem chunkSlots_get {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot) :
 (chunkSlots c q slot ha he l positive).get ⟨j,chunkSlots_bound c q slot ha he l positive h⟩=
 typedSlot c q slot (8*c.height.K+6) l ha he positive (stored c q slot ha he h):=by
 unfold chunkSlots
 rw[chunkLayers_get]
 have get:=UniformReplaySlotWitness.layer_get (dag c q slot ha he) h
  (UniformReplaySlotWitness.layer_bound _ h)
 change (replayLayers (dag c q slot ha he) (8*c.height.K+6) 6).get _=
  slotCodes c q slot (8*c.height.K+6) ha he at get
 have sd : ∀s∈slotCodes c q slot (8*c.height.K+6) ha he,
   Stored q.e (dag c q slot ha he).size q.a s:=by
  rw[size c q slot ha he]
  exact stored c q slot ha he h
 refine (congrArg (fun W=>W.map (relabelCode (normalPlacement c q slot ha he l).embedding))
  (packList_congr positive get _ sd)).trans ?_
 exact (pack_relabel_cast (size c q slot ha he).symm positive
  (placement (Header.forward c q slot).chunk l.chunk) _
  (stored c q slot ha he h) sd).symm

end
end ExactFourierCircuits.UniformActualCalendarWitnessSlots
