import UniformBroadcastActionBridge
import UniformSixCReplayDescriptor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCPhysicalAction
open UniformMachine UniformReplayPrint UniformPhysicalReplayBridge OAI.ExactFourier
noncomputable section

/-- Restrict every logical occurrence to the genuine zero-hole-free port domain. -/
def portWord {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 List (ShearCode (Port p) R) :=
 List.ofFn (fun i : Fin W.length =>
  let s := W[i.val]
  let d := dom s (List.getElem_mem i.isLt)
  ⟨⟨s.dst,d.1⟩,⟨s.src,d.2⟩,fun h=>s.different (congrArg Subtype.val h),s.coefficient⟩)

def physical {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) : List (ShearCode ℕ R) :=
 (portWord p W dom).map (UniformDAGLayers.relabelCode (portEmbedding l))

theorem portWord_natural {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 (portWord p W dom).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=W := by
 rw [portWord,List.map_ofFn]
 change List.ofFn (fun i : Fin W.length=>W[i.val])=W
 exact List.ofFn_getElem

theorem physical_action {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) (bank : Fin R→ℂ) (v : ℕ→ℂ) :
 runShears ((physical l W dom).map (ShearCode.eval bank)) v ∘ portEmbedding l =
 runShears (W.map (ShearCode.eval bank))
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.capacity) ∘ naturalEmbedding p := by
 have natural:=UniformDAGLayers.relabel_run (naturalEmbedding p) bank (portWord p W dom)
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.capacity)
 rw [portWord_natural] at natural
 rw [physical,UniformDAGLayers.relabel_run]
 exact natural.symm

theorem selected_domain {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 UniformChunkMatchingPreparation.CodesDomain p (selectedWord p W) := by
 intro s hs
 rw [selectedWord] at hs
 obtain ⟨i,hi⟩:=List.mem_ofFn.mp hs
 subst s
 exact dom _ (List.getElem_mem _)

theorem matching_physical {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 UniformSixCDirtyReplayMachine.physicalWord l W dom =
 physical l (selectedWord p W) (selected_domain p W dom) := by
 rw [physicalWord_relabel,physical]
 congr 1
 have inj : Function.Injective
  (UniformDAGLayers.relabelCode (naturalEmbedding p) : ShearCode (Port p) R→ShearCode ℕ R) := by
  intro a b h
  have dst : a.dst=b.dst:=Subtype.ext (congrArg ShearCode.dst h)
  have src : a.src=b.src:=Subtype.ext (congrArg ShearCode.src h)
  have coefficient : a.coefficient=b.coefficient:=congrArg (fun s : ShearCode ℕ R=>s.coefficient) h
  cases a;cases b
  simp_all
 apply (List.map_injective_iff.mpr inj)
 simp only [portWord_natural]
 exact (selectedWord_relabel p W dom).symm

open UniformSixCPhaseContext UniformSixCReplayDescriptor

/-- Actual computed depth/color occurrences in the common physical port domain. -/
def phasePorts {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (_l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 List (ShearCode (Port p) (UniformToeplitzCrossDAG.bankSize p.height.K)) :=
 (List.finRange ((8*p.height.K+7)*11)).flatMap (fun i=>
  let q:=layerParameters p backwards i.val
  let W:=logicalWord q (UniformChunkMatchingPreparation.crossWord q ha he)
   (UniformChunkMatchingPreparation.cross_domain q ha he)
  if backwards then reverseCode W else W)

theorem phasePorts_physical {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (phasePorts l backwards ha he).map (UniformDAGLayers.relabelCode (portEmbedding l.matching))=
 phaseWord l backwards ha he := by
 simp only [phasePorts,phaseWord,List.map_flatMap]
 apply congrArg (List.flatMap · (List.finRange ((8*p.height.K+7)*11)))
 funext i
 cases backwards
 · change (logicalWord (layerParameters p false i.val)
    (UniformChunkMatchingPreparation.crossWord (layerParameters p false i.val) ha he)
    (UniformChunkMatchingPreparation.cross_domain (layerParameters p false i.val) ha he)).map
    (UniformDAGLayers.relabelCode (portEmbedding l.matching))=_
   exact (physicalWord_relabel (atLayout l.matching false i.val i.isLt) _ _).symm
 · change (reverseCode (logicalWord (layerParameters p true i.val)
    (UniformChunkMatchingPreparation.crossWord (layerParameters p true i.val) ha he)
    (UniformChunkMatchingPreparation.cross_domain (layerParameters p true i.val) ha he))).map
    (UniformDAGLayers.relabelCode (portEmbedding l.matching))=reverseCode _
   dsimp only [layerParameters]
   rw [UniformDAGLayers.relabel_reverseCode]
   exact congrArg reverseCode (physicalWord_relabel (atLayout l.matching true i.val i.isLt) _ _).symm

theorem phasePorts_natural {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (phasePorts l backwards ha he).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=
 (if backwards then inverseSweepWords p
   (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
   p.height.enabled (8*p.height.K+6)
  else sweepWords p
   (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
   p.height.enabled (8*p.height.K+6)).flatten := by
 cases backwards
 · simp only [Bool.false_eq_true,ite_false,phasePorts,List.map_flatMap,sweepWords]
   rw [List.ofFn_eq_map,List.flatMap_def]
   congr 2
   funext i
   simpa only [layerParameters,UniformSixCTraversal.layerOrdinal,
    UniformSixCTraversal.layerDepth,UniformSixCTraversal.layerColor,Bool.false_eq_true,ite_false,
    UniformChunkMatchingPreparation.crossWord,naturalEmbedding] using
    (selectedWord_relabel (layerParameters p false i.val)
      (UniformChunkMatchingPreparation.crossWord (layerParameters p false i.val) ha he)
      (UniformChunkMatchingPreparation.cross_domain (layerParameters p false i.val) ha he)).symm
 · simp only [ite_true,phasePorts,List.map_flatMap,inverseSweepWords]
   rw [List.ofFn_eq_map,List.flatMap_def]
   congr 2
   funext i
   change (reverseCode (logicalWord (layerParameters p true i.val)
    (UniformChunkMatchingPreparation.crossWord (layerParameters p true i.val) ha he)
    (UniformChunkMatchingPreparation.cross_domain (layerParameters p true i.val) ha he))).map
    (UniformDAGLayers.relabelCode (naturalEmbedding p))=reverseCode _
   dsimp only [layerParameters]
   rw [UniformDAGLayers.relabel_reverseCode]
   have selected:=(selectedWord_relabel (layerParameters p true i.val)
      (UniformChunkMatchingPreparation.crossWord (layerParameters p true i.val) ha he)
      (UniformChunkMatchingPreparation.cross_domain (layerParameters p true i.val) ha he)).symm
   have yes : (true=true)↔True := by simp
   have ordinal : ((8*p.height.K+7)*11)-1-i.val=i.rev.val := (reverse_ordinal i).symm
   apply congrArg reverseCode
   simpa only [UniformSixCTraversal.layerOrdinal,UniformSixCTraversal.layerDepth,
    UniformSixCTraversal.layerColor,layerParameters,yes,ite_true,ordinal,
    UniformChunkMatchingPreparation.crossWord,naturalEmbedding] using selected


def broadcastPorts {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (positive:Bool) (R:ℕ) :
 List (ShearCode (Port p) R) :=
 (List.finRange p.height.a).map (fun j=>
  let g:=UniformCrossHeightPreparationMachine.gates p.height
  let ag: p.height.a≤g := (geometry l).ag
  ⟨⟨p.height.e+1+g+j.val,Or.inr (by have:=j.isLt;omega)⟩,
   ⟨p.height.e+1+(g-p.height.a+j.val),Or.inr (by have:=j.isLt;omega)⟩,
   by
    intro h
    have hv:=congrArg Subtype.val h
    change p.height.e+1+g+j.val=p.height.e+1+(g-p.height.a+j.val) at hv
    have:=j.isLt
    omega,
   .rational (if positive then -1 else 1)⟩)

theorem broadcastPorts_physical {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (positive:Bool) (R:ℕ) :
 (broadcastPorts l positive R).map (UniformDAGLayers.relabelCode (portEmbedding l))=
 UniformSixCBroadcast.word positive (geometry l) R := by
 simp only [broadcastPorts,UniformSixCBroadcast.word,List.map_map]
 apply congrArg (List.map · (List.finRange p.height.a))
 funext j
 have ag: p.height.a≤UniformCrossHeightPreparationMachine.gates p.height := (geometry l).ag
 have hj:UniformCrossHeightPreparationMachine.gates p.height-p.height.a+j.val<
  UniformCrossHeightPreparationMachine.gates p.height := by have:=j.isLt;omega
 dsimp only [Function.comp_apply,UniformDAGLayers.relabelCode,portEmbedding,geometry]
 congr 1
 · change UniformChunkPortMachine.mapped p.height.e (UniformCrossHeightPreparationMachine.gates p.height)
    p.source p.target _ (p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height+j.val)=p.target+j.val
   exact UniformChunkPortMachine.mapped_target _ _ _ _ _ _
 · change UniformChunkPortMachine.mapped p.height.e (UniformCrossHeightPreparationMachine.gates p.height)
    p.source p.target _ (p.height.e+1+(UniformCrossHeightPreparationMachine.gates p.height-p.height.a+j.val))=_
   rw [UniformChunkPortMachine.mapped_gate _ _ _ _ _ _ hj]
   simp only [UniformChunkPortMachine.borrowedCoordinate,UniformSixCBroadcast.Geometry.borrowedAt,
    dite_eq_left hj]

def signedLastBroadcast {R:ℕ} (e g a:ℕ) (ag:a≤g) (positive:Bool) : List (ShearCode ℕ R) :=
 (UniformBroadcastActionBridge.lastBroadcast e g a ag).map (fun s=>if positive then s.inverse else s)

theorem broadcastPorts_natural {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (positive:Bool) (R:ℕ) :
 (broadcastPorts l positive R).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=
 signedLastBroadcast p.height.e (UniformCrossHeightPreparationMachine.gates p.height)
  p.height.a (geometry l).ag positive := by
 simp only [broadcastPorts,signedLastBroadcast,UniformBroadcastActionBridge.lastBroadcast,List.map_map]
 apply congrArg (List.map · (List.finRange p.height.a))
 funext j
 cases positive <;> rfl

def halfPorts {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (positive:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :=
 phasePorts l false ha he ++ reverseCode (broadcastPorts l.matching positive
   (UniformToeplitzCrossDAG.bankSize p.height.K)) ++ phasePorts l true ha he

theorem halfPorts_physical {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (positive:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (halfPorts l positive ha he).map (UniformDAGLayers.relabelCode (portEmbedding l.matching))=
 halfWord l positive ha he := by
 simp only [halfPorts,halfWord,List.map_append,UniformDAGLayers.relabel_reverseCode,
  phasePorts_physical,broadcastPorts_physical]

def fullPorts {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 List (ShearCode (Port p) (UniformToeplitzCrossDAG.bankSize p.height.K)) :=
 (show List (ShearCode (Port p) (UniformToeplitzCrossDAG.bankSize p.height.K)) from
  halfPorts (p:=enabledParameters p true) (enabledPacking l true) true ha he) ++
 (show List (ShearCode (Port p) (UniformToeplitzCrossDAG.bankSize p.height.K)) from
  halfPorts (p:=enabledParameters p false) (enabledPacking l false) false ha he)

theorem fullPorts_physical {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (fullPorts l ha he).map (UniformDAGLayers.relabelCode (portEmbedding l.matching))=
 fullWord l ha he := by
 unfold fullPorts fullWord
 rw [List.map_append]
 exact congrArg₂ List.append (halfPorts_physical (enabledPacking l true) true ha he)
  (halfPorts_physical (enabledPacking l false) false ha he)

theorem signedLast_cross {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (positive enabled:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 signedLastBroadcast (R:=UniformToeplitzCrossDAG.bankSize p.height.K) p.height.e
  (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (geometry l).ag positive =
 (UniformDAGLayers.natBroadcast
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he) enabled).map
  (fun s=>if positive then s.inverse else s) := by
 let D:=UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he
 have ag:p.height.a≤D.size:=by
  rw [UniformCrossHeightPreparationMachine.cross_size p.height ha he]
  exact (geometry l).ag
 have last:=UniformBroadcastActionBridge.lastBroadcast_eq D ag
  (UniformBroadcastActionBridge.cross_outputs p.height.K p.height.a p.height.e ha he) enabled
 have actual : UniformDAGLayers.natBroadcast D enabled=
  UniformBroadcastActionBridge.lastBroadcast p.height.e
   (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (geometry l).ag := by
  simpa only [D,UniformCrossHeightPreparationMachine.cross_size p.height ha he] using last
 exact congrArg (List.map (fun s:ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)=>
  if positive then s.inverse else s)) actual.symm

theorem inverse_map_reverse {R:ℕ} (W:List (ShearCode ℕ R)) :
 reverseCode (W.map ShearCode.inverse)=W.reverse := by
 simp only [reverseCode,List.map_reverse,List.map_map,Function.comp_def,
  UniformDAGLayers.inverse_inverse,List.map_id']

def naturalHalf {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (positive:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :=
 (sweepWords p (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
   p.height.enabled (8*p.height.K+6)).flatten ++
 reverseCode (signedLastBroadcast (R:=UniformToeplitzCrossDAG.bankSize p.height.K) p.height.e
  (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (geometry l.matching).ag positive) ++
 (inverseSweepWords p (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
   p.height.enabled (8*p.height.K+6)).flatten

theorem halfPorts_natural {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (positive:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (halfPorts l positive ha he).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=
 naturalHalf l positive ha he := by
 simp only [halfPorts,naturalHalf,List.map_append,UniformDAGLayers.relabel_reverseCode,
  phasePorts_natural,broadcastPorts_natural,Bool.false_eq_true,ite_false,ite_true]

theorem fullPorts_natural {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 (fullPorts l ha he).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=
 (literalReplayWords p
   (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he)
   (8*p.height.K+6)).flatten := by
 have both:=congrArg₂ List.append
  (halfPorts_natural (enabledPacking l true) true ha he)
  (halfPorts_natural (enabledPacking l false) false ha he)
 have assembled : (fullPorts l ha he).map (UniformDAGLayers.relabelCode (naturalEmbedding p))=
  (show List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) from
   naturalHalf (p:=enabledParameters p true) (enabledPacking l true) true ha he) ++
  (show List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)) from
   naturalHalf (p:=enabledParameters p false) (enabledPacking l false) false ha he) := by
  exact (List.map_append (f:=UniformDAGLayers.relabelCode (naturalEmbedding p))).trans both
 apply assembled.trans
 have first:=signedLast_cross (enabledMatching l.matching true) true true ha he
 have second:=signedLast_cross (enabledMatching l.matching false) false false ha he
 dsimp only [enabledParameters] at first second
 dsimp only [naturalHalf,enabledParameters]
 rw [first,second]
 simp only [literalReplayWords,List.flatten_append,List.flatten_cons,List.flatten_nil,
  List.append_nil,inverse_map_reverse,Bool.false_eq_true,ite_false,ite_true,List.map_id',List.append_assoc]
 rfl

/-- Pull back the literal physical six-phase word through its actual common
injective coordinate map. No supplied matrix/action or broadcast-order premise. -/
theorem fullWord_action {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (v:ℕ→ℂ) :
 runShears ((fullWord l ha he).map (ShearCode.eval bank)) v ∘ portEmbedding l.matching =
 runShears ((literalReplayWords p
   (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he)
   (8*p.height.K+6)).flatten.map (ShearCode.eval bank))
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.matching.capacity) ∘ naturalEmbedding p := by
 rw [←fullPorts_physical,UniformDAGLayers.relabel_run]
 have natural :=UniformDAGLayers.relabel_run (naturalEmbedding p) bank (fullPorts l ha he)
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.matching.capacity)
 rw [fullPorts_natural] at natural
 exact natural.symm

end
end ExactFourierCircuits.UniformSixCPhysicalAction
