import UniformReplayPrint

set_option autoImplicit false

/-! Deterministic greedy coloring of a printed finite multigraph. Edges keep
their indices, including parallel edges. All choices inspect integer endpoints
and earlier integer colors; scalar coefficients do not occur in this module. -/
namespace ExactFourierCircuits.UniformColoring

def firstFree (K : ℕ) (used : Finset ℕ) : ℕ :=
  ((List.range K).find? (fun c => decide (c ∉ used))).getD K

theorem firstFree_spec (K : ℕ) (used : Finset ℕ) (h : used.card  <  K) :
    firstFree K used  <  K ∧ firstFree K used ∉ used := by
  obtain ⟨c,hc,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (by simpa using h : used.card  <  (Finset.range K).card)
  cases hf : (List.range K).find? (fun c => decide (c ∉ used)) with
  | none =>
    have hn := List.find?_eq_none.mp hf c (by simpa using hc)
    simp [hu] at hn
  | some c =>
    have hm := List.mem_of_find?_eq_some hf
    have hv := List.find?_some hf
    simp only [firstFree,hf,Option.getD_some]
    exact ⟨List.mem_range.mp hm,of_decide_eq_true hv⟩

structure Edge where
  left : ℕ
  right : ℕ
  different : left  ≠  right

def Incident (e : Edge) (v : ℕ) : Prop := e.left=v ∨ e.right=v

instance (e : Edge) (v : ℕ) : Decidable (Incident e v) := inferInstanceAs (Decidable (_ ∨ _))

def Conflict (e f : Edge) : Prop := Incident f e.left ∨ Incident f e.right

instance (e f : Edge) : Decidable (Conflict e f) := inferInstanceAs (Decidable (_ ∨ _))

theorem conflict_symm (e f : Edge) : Conflict e f ↔ Conflict f e := by
  simp only [Conflict,Incident]
  constructor  <;> rintro ((h|h)|(h|h))  <;> simp_all [eq_comm]

def incidentEdges {m : ℕ} (E : Fin m → Edge) (v : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Incident (E i) v)

def earlierNeighbors {m : ℕ} (E : Fin m → Edge) (j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.val < j.val ∧ Conflict (E j) (E i))

def earlierColors {m : ℕ} (E : Fin m → Edge) (j : Fin m) (c : ℕ → ℕ) : Finset ℕ :=
  (earlierNeighbors E j).image (fun i => c i.val)

def DegreeBound {m : ℕ} (E : Fin m → Edge) (delta : ℕ) : Prop :=
  ∀ v, (incidentEdges E v).card  ≤  delta

theorem neighbors_subset {m : ℕ} (E : Fin m → Edge) (j : Fin m) :
    earlierNeighbors E j ⊆ (incidentEdges E (E j).left).erase j ∪
      (incidentEdges E (E j).right).erase j := by
  intro i hi
  simp only [earlierNeighbors,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  obtain ⟨hij,hc⟩ := hi
  have hn : i  ≠  j := by intro h; subst i; omega
  rcases hc with h|h
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hn,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

theorem neighbors_card {m delta : ℕ} (E : Fin m → Edge) (j : Fin m)
    (hd : DegreeBound E delta) : (earlierNeighbors E j).card  ≤  2*delta-2 := by
  have hl : j ∈ incidentEdges E (E j).left := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
  have hr : j ∈ incidentEdges E (E j).right := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr rfl⟩
  have hcl := Finset.card_erase_add_one hl
  have hcr := Finset.card_erase_add_one hr
  have hb := (Finset.card_le_card (neighbors_subset E j)).trans
    (Finset.card_union_le _ _)
  have hdl := hd (E j).left
  have hdr := hd (E j).right
  omega

theorem earlierColors_card {m delta : ℕ} (E : Fin m → Edge) (j : Fin m)
    (c : ℕ → ℕ) (hd : DegreeBound E delta) : (earlierColors E j c).card  ≤  2*delta-2 :=
  Finset.card_image_le.trans (neighbors_card E j hd)

def greedy {m : ℕ} (E : Fin m → Edge) (K : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 0
  | j+1 =>
    let c := greedy E K j
    if hj : j < m then Function.update c j (firstFree K (earlierColors E ⟨j,hj⟩ c)) else c

theorem greedy_next {m : ℕ} (E : Fin m → Edge) (K j : ℕ) (hj : j < m) :
    greedy E K (j+1) = Function.update (greedy E K j) j
      (firstFree K (earlierColors E ⟨j,hj⟩ (greedy E K j))) := by simp [greedy,hj]

def Good {m : ℕ} (E : Fin m → Edge) (K j : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ i : Fin m, i.val < j → c i.val < K) ∧
    ∀ i h : Fin m, i.val < j → h.val < j → i.val < h.val → Conflict (E i) (E h) → c i.val ≠ c h.val

theorem greedy_good {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (j : ℕ) (hj : j ≤ m) : Good E (2*delta-1) j (greedy E (2*delta-1) j) := by
  induction j with
  | zero => exact ⟨fun _ h => by omega,fun _ _ h => by omega⟩
  | succ j ih =>
    have hjm : j < m := by omega
    have hprev := ih (by omega)
    let here : Fin m := ⟨j,hjm⟩
    have hfree := firstFree_spec (2*delta-1)
      (earlierColors E here (greedy E (2*delta-1) j))
      (by have h := earlierColors_card E here (greedy E (2*delta-1) j) hd; omega)
    rw [greedy_next E (2*delta-1) j hjm]
    constructor
    · intro i hi
      by_cases he : i.val=j
      · simpa [he,here] using hfree.1
      · simpa [he] using hprev.1 i (by omega)
    · intro i h hi hh hlt hc
      have hij : i.val ≠ j := by omega
      by_cases he : h.val=j
      · have hhE : h=here := Fin.ext he
        subst h
        have hmem : greedy E (2*delta-1) j i.val ∈ earlierColors E here (greedy E (2*delta-1) j) := by
          apply Finset.mem_image.mpr
          refine ⟨i,?_,rfl⟩
          simp only [earlierNeighbors,Finset.mem_filter,Finset.mem_univ,true_and]
          exact ⟨hlt,(conflict_symm _ _).mp hc⟩
        have hn : greedy E (2*delta-1) j i.val  ≠ 
            firstFree (2*delta-1) (earlierColors E here (greedy E (2*delta-1) j)) := by
          intro h; exact hfree.2 (h ▸ hmem)
        simpa [hij,here] using hn
      · simpa [hij,he] using hprev.2 i h (by omega) (by omega) hlt hc

def coloring {m : ℕ} (E : Fin m → Edge) (delta : ℕ) (i : Fin m) : ℕ :=
  greedy E (2*delta-1) m i.val

theorem coloring_bound {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (i : Fin m) : coloring E delta i  <  2*delta-1 :=
  (greedy_good E hd hpos m le_rfl).1 i i.isLt

theorem coloring_proper {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (i j : Fin m) (hne : i ≠ j) (hc : Conflict (E i) (E j)) :
    coloring E delta i  ≠  coloring E delta j := by
  have hgood := (greedy_good E hd hpos m le_rfl).2
  have hv : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h|h
  · exact hgood i j i.isLt j.isLt h hc
  · exact (hgood j i j.isLt i.isLt h ((conflict_symm _ _).mp hc)).symm

theorem same_color_disjoint {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (i j : Fin m) (hne : i ≠ j) (hc : coloring E delta i = coloring E delta j) :
    ¬Conflict (E i) (E j) := fun h => coloring_proper E hd hpos i j hne h hc

/-- Ordered lists retain the original edge order within each color. -/
def layer {m : ℕ} (E : Fin m → Edge) (delta c : ℕ) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (coloring E delta i = c))

def layers {m : ℕ} (E : Fin m → Edge) (delta : ℕ) : List (List (Fin m)) :=
  (List.range (2*delta-1)).map (layer E delta)

@[simp] theorem mem_layer {m : ℕ} (E : Fin m → Edge) (delta c : ℕ) (i : Fin m) :
    i ∈ layer E delta c ↔ coloring E delta i = c := by
  simp [layer]

theorem layer_nodup {m : ℕ} (E : Fin m → Edge) (delta c : ℕ) :
    (layer E delta c).Nodup := (List.nodup_finRange m).filter _

@[simp] theorem layers_length {m : ℕ} (E : Fin m → Edge) (delta : ℕ) :
    (layers E delta).length = 2*delta-1 := by simp [layers]

/-- Each indexed edge occurs in exactly one color, also for parallel edges. -/
theorem unique_layer {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (i : Fin m) :
    ∃! c : ℕ, c < 2*delta-1 ∧ i ∈ layer E delta c := by
  refine ⟨coloring E delta i,⟨coloring_bound E hd hpos i,by simp⟩,?_⟩
  intro c hc
  exact (mem_layer E delta c i).mp hc.2 |>.symm

/-- Every color is an actual matching of integer coordinate pairs. -/
theorem layer_disjoint {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (c : ℕ) (i j : Fin m) (hi : i ∈ layer E delta c)
    (hj : j ∈ layer E delta c) (hne : i ≠ j) : ¬Conflict (E i) (E j) :=
  same_color_disjoint E hd hpos i j hne ((mem_layer E delta c i).mp hi |>.trans
    ((mem_layer E delta c j).mp hj).symm)

/-- The graph projection never evaluates a coefficient. -/
def shearEdge {r : ℕ} (s : UniformReplayPrint.ShearCode ℕ r) : Edge :=
  ⟨s.dst,s.src,s.different⟩

def printedEdges {r : ℕ} (W : List (UniformReplayPrint.ShearCode ℕ r)) :
    Fin W.length → Edge := fun i => shearEdge (W.get i)

def printedLayers {r : ℕ} (W : List (UniformReplayPrint.ShearCode ℕ r)) (delta : ℕ) :
    List (List (Fin W.length)) := layers (printedEdges W) delta

theorem printedLayers_length {r : ℕ} (W : List (UniformReplayPrint.ShearCode ℕ r))
    (delta : ℕ) : (printedLayers W delta).length = 2*delta-1 := layers_length _ _

theorem printed_matching {r delta : ℕ} (W : List (UniformReplayPrint.ShearCode ℕ r))
    (hd : DegreeBound (printedEdges W) delta) (hpos : 0 < delta) (c : ℕ)
    (i j : Fin W.length) (hi : i ∈ layer (printedEdges W) delta c)
    (hj : j ∈ layer (printedEdges W) delta c) (hne : i ≠ j) :
    (W.get i).dst ≠ (W.get j).dst ∧ (W.get i).dst ≠ (W.get j).src ∧
    (W.get i).src ≠ (W.get j).dst ∧ (W.get i).src ≠ (W.get j).src := by
  have h := layer_disjoint (printedEdges W) hd hpos c i j hi hj hne
  simpa only [Conflict,Incident,printedEdges,shearEdge,not_or,eq_comm,and_assoc] using h

end ExactFourierCircuits.UniformColoring
