import UniformLocalBroadcastPoolMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalBroadcastSemantics
open UniformColoring UniformReplayPrint UniformDAGLayers OAI.ExactFourier

lemma firstFree_empty (K:ℕ) (h:0<K) : firstFree K ∅=0 := by
 cases K with
 | zero => omega
 | succ K => simp [firstFree,List.range_succ_eq_map]

lemma disjoint_neighbors {m:ℕ} (E:Fin m→Edge)
 (matching:∀i j,i≠j→¬Conflict (E i) (E j)) (j:Fin m) : earlierNeighbors E j=∅ := by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro i hi
 obtain ⟨lt,conflict⟩:=by simpa only [earlierNeighbors,Finset.mem_filter,Finset.mem_univ,true_and] using hi
 have ne:j≠i:=by intro eq;have:=congrArg Fin.val eq;omega
 exact matching j i ne conflict

lemma disjoint_greedy_zero {m:ℕ} (E:Fin m→Edge)
 (matching:∀i j,i≠j→¬Conflict (E i) (E j)) (K:ℕ) (hK:0<K) (t:ℕ) :
 greedy E K t=fun _=>0 := by
 induction t with
 | zero => rfl
 | succ t ih =>
  by_cases h:t < m
  · rw [greedy_next E K t h,earlierColors,disjoint_neighbors E matching,Finset.image_empty,
     firstFree_empty K hK,ih]
    funext i;simp
  · simp only [greedy,h,dite_false,ih]

lemma disjoint_coloring_zero {m:ℕ} (E:Fin m→Edge)
 (matching:∀i j,i≠j→¬Conflict (E i) (E j)) (i:Fin m) : coloring E 6 i=0 := by
 unfold coloring
 rw [disjoint_greedy_zero E matching 11 (by omega)]

lemma disjoint_colorBlocks {r:ℕ} (W:List (ShearCode ℕ r))
 (matching:∀i j:Fin W.length,i≠j→¬Conflict (printedEdges W i) (printedEdges W j)) :
 colorBlocks W 6=(List.range 11).map (fun c=>if c=0 then W else []) := by
 unfold colorBlocks layers
 simp only [List.map_map]
 apply List.map_congr_left
 intro c _
 dsimp only [Function.comp_def]
 simp only [layer,disjoint_coloring_zero _ matching]
 by_cases h:c=0
 · simp only [h,decide_true,List.filter_true,ite_true]
   exact (List.ofFn_eq_map.symm.trans (List.ofFn_get W))
 · have hn:¬0=c:=Ne.symm h
   simp only [hn,decide_false,List.filter_false,List.map_nil,h,ite_false]

lemma disjoint_color_at {r:ℕ} (W:List (ShearCode ℕ r))
 (matching:∀i j:Fin W.length,i≠j→¬Conflict (printedEdges W i) (printedEdges W j)) (c:ℕ) :
 ((colorBlocks W 6)[c]?).getD []=if c=0 then W else [] := by
 rw [disjoint_colorBlocks W matching]
 by_cases h:c<11
 · simp only [List.getElem?_map,List.getElem?_eq_getElem (by simpa only [List.length_range] using h : c<(List.range 11).length),Option.map_some,
    Option.getD_some,List.getElem_range]
 · rw [List.getElem?_eq_none (by simpa only [List.length_map,List.length_range] using Nat.le_of_not_gt h : ((List.range 11).map (fun c=>if c=0 then W else [])).length ≤ c)]
   have ne:c≠0:=by omega
   simp only [Option.getD_none,ne,ite_false]

def entry {r:ℕ} (e a g:ℕ) (ag:a≤g) (j:Fin a) : ShearCode ℕ r :=
 ⟨e+1+g+j.val,e+1+(g-a)+j.val,by have:=j.isLt;omega,.rational 1⟩

lemma reference_some {ι:Type} {r:ℕ} (d src:ι) (ref:Option ι) (c:Coefficient r)
 (h:∀i,ref=some i→d≠i) (eq:ref=some src) : reference d ref c h=[⟨d,src,h src eq,c⟩] := by
 cases ref with
 | none => cases eq
 | some v => cases Option.some.inj eq;rfl

lemma cross_broadcast_eq (k a e:ℕ) (ha:a≤UniformRadixTwoDAG.width k)
 (he:e≤UniformRadixTwoDAG.width k) (enabled:Bool) :
 natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled=
 (List.finRange a).map (entry e a (UniformToeplitzCrossDAG.crossDAG k a e ha he).size (by
   rw [UniformToeplitzCrossDAG.crossDAG_size];omega)) := by
 let D:=UniformToeplitzCrossDAG.crossDAG k a e ha he
 have ag:a≤D.size:=by rw [UniformToeplitzCrossDAG.crossDAG_size];omega
 have each (j:Fin a) : reference (r:=UniformToeplitzCrossDAG.bankSize k) (e+1+D.size+j.val)
  (referenceMap enabled (fun i:Fin e=>i.val) (fun i:Fin D.size=>e+1+i.val) (D.outputs j))
  (.rational 1) (by
    intro src hs
    have same:=referenceMap_nat_some enabled (D.outputs j) src hs
    have small:=(D.outputs j).isLt
    omega)=[entry e a D.size ag j] := by
  have idx:(D.outputs j)=Fin.natAdd (e+1) (⟨D.size-a+j.val,by have:=j.isLt;omega⟩:Fin D.size):=by
   apply Fin.ext
   simpa only [D,Fin.val_natAdd,Nat.add_assoc] using
    UniformCrossBroadcastTableMachine.cross_output_index k a e ha he j
  have refEq:referenceMap enabled (fun i:Fin e=>i.val) (fun i:Fin D.size=>e+1+i.val)
   (D.outputs j)=some (e+1+(D.size-a)+j.val):=by
   rw [idx]
   simp only [referenceMap,Fin.addCases_right]
   congr 1;omega
  rw [reference_some _ _ _ _ _ refEq]
  rfl
 change natBroadcast D enabled=(List.finRange a).map (entry e a D.size ag)
 unfold natBroadcast
 rw [List.map_eq_flatMap]
 apply List.flatMap_congr
 intro j _
 exact each j

lemma cross_broadcast_matching (k a e:ℕ) (ha:a≤UniformRadixTwoDAG.width k)
 (he:e≤UniformRadixTwoDAG.width k) (enabled:Bool) :
 ∀i j:Fin (natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled).length,
 i≠j→¬Conflict (printedEdges (natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled) i)
  (printedEdges (natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled) j) := by
 intro i j ne
 have il:i.val<a:=by simpa only [cross_broadcast_eq,List.length_map,List.length_finRange] using i.isLt
 have jl:j.val<a:=by simpa only [cross_broadcast_eq,List.length_map,List.length_finRange] using j.isLt
 have iv:i.val≠j.val:=by intro eq;exact ne (Fin.ext eq)
 have ag:a≤(UniformToeplitzCrossDAG.crossDAG k a e ha he).size:=by
  rw [UniformToeplitzCrossDAG.crossDAG_size];omega
 unfold Conflict Incident printedEdges shearEdge
 simp only [cross_broadcast_eq,List.get_eq_getElem,List.getElem_map,List.getElem_finRange,entry,Fin.val_cast]
 omega

lemma cross_broadcast_color_at (k a e:ℕ) (ha:a≤UniformRadixTwoDAG.width k)
 (he:e≤UniformRadixTwoDAG.width k) (enabled:Bool) (c:ℕ) :
 ((colorBlocks (natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled) 6)[c]?).getD []=
 if c=0 then natBroadcast (UniformToeplitzCrossDAG.crossDAG k a e ha he) enabled else [] :=
 disjoint_color_at _ (cross_broadcast_matching k a e ha he enabled) c

end ExactFourierCircuits.UniformLocalBroadcastSemantics
