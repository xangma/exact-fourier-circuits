import UniformDAGLayers
import UniformLocalPreparationReferences

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheChronology
open UniformDAGLayers UniformReplayPrint

/-- A complete fixed-order replay slot. All fields are integer/Boolean control
metadata; inverse means reverse occurrence order and negate coefficients. -/
structure Slot where
 broadcast : Bool
 enabled : Bool
 inverse : Bool
 depth : ℕ
 color : ℕ
 deriving DecidableEq, Repr

def sweepSlots (H:ℕ) (enabled:Bool):List Slot:=
 (List.range (H+1)).flatMap fun d=>(List.range 11).map (fun c=>⟨false,enabled,false,d,c⟩)
def broadcastSlots (enabled:Bool):List Slot:=
 (List.range 11).map fun c=>⟨true,enabled,false,0,c⟩
def invertSlots (L:List Slot):List Slot:=L.reverse.map fun s=>{s with inverse:=!s.inverse}
def replaySlots (H:ℕ):List Slot:=
 let W:=sweepSlots H true
 let V:=sweepSlots H false
 let B:=broadcastSlots true
 let Z:=broadcastSlots false
 W++B++invertSlots W++V++invertSlots Z++invertSlots V

lemma sweepSlots_length (H:ℕ)(enabled:Bool):(sweepSlots H enabled).length=(H+1)*11:=by
 simp [sweepSlots,List.length_flatMap]
lemma broadcastSlots_length(enabled:Bool):(broadcastSlots enabled).length=11:=by simp [broadcastSlots]
lemma invertSlots_length(L:List Slot):(invertSlots L).length=L.length:=by simp [invertSlots]
lemma replaySlots_length(H:ℕ):(replaySlots H).length=(4*(H+1)+2)*11:=by
 simp only [replaySlots,List.length_append,sweepSlots_length,broadcastSlots_length,invertSlots_length]
 omega

/-- Evaluates only control metadata against the actual literal printed DAG. -/
def layer {r n a:ℕ} (D:UniformToeplitzCrossDAG.DAG r n a) (H:ℕ) (s:Slot):List (ShearCode ℕ r):=
 let base:=if s.broadcast then natBroadcast D s.enabled else
   ((depthBuckets (natSweep D.program s.enabled) (natLevel D.program) H)[s.depth]?).getD []
 let W:=((colorBlocks base 6)[s.color]?).getD []
 if s.inverse then reverseCode W else W

lemma indexed_list {α:Type} (L:List α) (zero:α):
 (List.range L.length).map (fun i=>(L[i]?).getD zero)=L:=by
 apply List.ext_getElem
 · simp
 · intro i h1 h2
   simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem h2,Option.getD_some]

lemma colors_indexed {r:ℕ} (L:List (ShearCode ℕ r)):
 (List.range 11).map (fun c=>((colorBlocks L 6)[c]?).getD [])=colorBlocks L 6:=by
 have len:(colorBlocks L 6).length=11:=by rw [colorBlocks_length]
 simpa only [len] using indexed_list (colorBlocks L 6) []

lemma sweepSlots_layers {r n a:ℕ} (D:UniformToeplitzCrossDAG.DAG r n a) (H:ℕ) (enabled:Bool):
 (sweepSlots H enabled).map (layer D H)=layeredSweep D.program enabled H 6:=by
 unfold sweepSlots layeredSweep coloredBuckets
 simp only [List.map_flatMap,List.map_map,Function.comp_def,layer,Bool.false_eq_true,ite_false]
 have he:(List.range (H+1)).map (fun d=>
  ((depthBuckets (natSweep D.program enabled) (natLevel D.program) H)[d]?).getD [])=
  depthBuckets (natSweep D.program enabled) (natLevel D.program) H:=by
  simpa only [depthBuckets_length] using indexed_list
   (depthBuckets (natSweep D.program enabled) (natLevel D.program) H) []
 conv_rhs=>rw [←he,List.flatMap_map]
 apply List.flatMap_congr
 intro d hd
 exact colors_indexed _

lemma broadcastSlots_layers {r n a:ℕ} (D:UniformToeplitzCrossDAG.DAG r n a) (H:ℕ) (enabled:Bool):
 (broadcastSlots enabled).map (layer D H)=colorBlocks (natBroadcast D enabled) 6:=by
 simp only [broadcastSlots,List.map_map,Function.comp_def,layer,ite_true,Bool.false_eq_true,ite_false]
 exact colors_indexed _

lemma invert_layers {r n a:ℕ} (D:UniformToeplitzCrossDAG.DAG r n a) (H:ℕ) (L:List Slot)
 (forward:∀s∈L,s.inverse=false):
 (invertSlots L).map (layer D H)=reverseLayers (L.map (layer D H)):=by
 unfold invertSlots reverseLayers
 simp only [List.map_map,List.map_reverse,Function.comp_def]
 apply congrArg List.reverse
 apply List.map_congr_left
 intro s hs
 have old: s∈L:=by simpa using hs
 simp [layer,forward s old]

lemma sweep_forward(H:ℕ)(enabled:Bool):∀s∈sweepSlots H enabled,s.inverse=false:=by
 intro s hs
 obtain ⟨d,_,hs⟩:=List.mem_flatMap.mp hs
 obtain ⟨c,_,rfl⟩:=List.mem_map.mp hs
 rfl
lemma broadcast_forward(enabled:Bool):∀s∈broadcastSlots enabled,s.inverse=false:=by
 intro s hs;obtain ⟨c,_,rfl⟩:=List.mem_map.mp hs;rfl

/-- Exact six-phase chronology, including every empty color slot and every
ascending/descending depth slot. No action or sorted-schedule premise occurs. -/
lemma replaySlots_layers {r n a:ℕ} (D:UniformToeplitzCrossDAG.DAG r n a) (H:ℕ):
 (replaySlots H).map (layer D H)=replayLayers D H 6:=by
 unfold replaySlots replayLayers
 simp only [List.map_append,sweepSlots_layers,broadcastSlots_layers,
 invert_layers D H _ (sweep_forward H true),invert_layers D H _ (sweep_forward H false),
 invert_layers D H _ (broadcast_forward false)]


end ExactFourierCircuits.UniformLocalCacheChronology
