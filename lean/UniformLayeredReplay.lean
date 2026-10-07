import UniformColoring

set_option autoImplicit false

/-! A color partition is an actual permutation of the indexed printed level.
Regrouping preserves action only under the explicit within-level dependency
condition: no destination is read as a source anywhere in this level. This
module does not reorder arbitrary dependent replay instructions. -/
namespace ExactFourierCircuits.UniformLayeredReplay
open UniformColoring UniformReplayPrint OAI.ExactFourier

def layerOrder {m : ℕ} (E : Fin m → Edge) (delta : ℕ) : List (Fin m) :=
  (layers E delta).flatten

theorem layerOrder_nodup {m : ℕ} (E : Fin m → Edge) (delta : ℕ) :
    (layerOrder E delta).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hl
    exact layer_nodup E delta c
  · apply List.pairwise_map.mpr
    apply List.Nodup.pairwise_of_forall_ne List.nodup_range
    intro c _ d _ hcd
    apply List.disjoint_left.mpr
    intro i hi hj
    exact hcd (((mem_layer E delta c i).mp hi).symm.trans
      ((mem_layer E delta d i).mp hj))

theorem mem_layerOrder {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) (i : Fin m) : i ∈ layerOrder E delta := by
  apply List.mem_flatten.mpr
  refine ⟨layer E delta (coloring E delta i),?_,by simp⟩
  apply List.mem_map.mpr
  exact ⟨coloring E delta i,List.mem_range.mpr (coloring_bound E hd hpos i),rfl⟩

theorem layerOrder_perm {m delta : ℕ} (E : Fin m → Edge) (hd : DegreeBound E delta)
    (hpos : 0 < delta) : (layerOrder E delta).Perm (List.finRange m) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_eq_one_of_mem (layerOrder_nodup E delta) (mem_layerOrder E hd hpos i)]
  exact (List.count_eq_one_of_mem (List.nodup_finRange m) (by simp)).symm

/-- Only endpoint comparisons occur in this independent-level condition. -/
def LevelSafe {r : ℕ} (W : List (ShearCode ℕ r)) : Prop :=
  ∀ s ∈ W, ∀ t ∈ W, s.dst ≠ t.src

/-- Target vertices have this level; source vertices have strictly smaller levels. -/
def OnLevel {r : ℕ} (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ s ∈ W, level s.dst = d ∧ level s.src < d

theorem OnLevel.safe {r d : ℕ} {W : List (ShearCode ℕ r)} {level : ℕ → ℕ}
    (h : OnLevel W level d) : LevelSafe W := by
  intro s hs t ht he
  have hd := (h s hs).1
  have hl := (h t ht).2
  rw [← he,hd] at hl
  omega

def destinationUses {r : ℕ} (W : List (ShearCode ℕ r)) (v : ℕ) : Finset (Fin W.length) :=
  Finset.univ.filter (fun i => (W.get i).dst = v)

def sourceUses {r : ℕ} (W : List (ShearCode ℕ r)) (v : ℕ) : Finset (Fin W.length) :=
  Finset.univ.filter (fun i => (W.get i).src = v)

/-- Since source and target roles occupy different levels, the degree bound
is the maximum of their multiplicity bounds, rather than their sum. -/
theorem degree_of_level {r d delta : ℕ} (W : List (ShearCode ℕ r)) (level : ℕ → ℕ)
    (hl : OnLevel W level d)
    (hi : ∀ v, (destinationUses W v).card ≤ delta)
    (ho : ∀ v, (sourceUses W v).card ≤ delta) : DegreeBound (printedEdges W) delta := by
  intro v
  by_cases hv : level v = d
  · have he : incidentEdges (printedEdges W) v = destinationUses W v := by
      ext i
      unfold incidentEdges destinationUses
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change ((W.get i).dst = v ∨ (W.get i).src = v) ↔ (W.get i).dst = v
      constructor
      · rintro (h|h)
        · exact h
        · have hs := (hl (W.get i) (List.get_mem W i)).2
          rw [h,hv] at hs
          omega
      · exact Or.inl
    rw [he]
    exact hi v
  · have he : incidentEdges (printedEdges W) v = sourceUses W v := by
      ext i
      unfold incidentEdges sourceUses
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change ((W.get i).dst = v ∨ (W.get i).src = v) ↔ (W.get i).src = v
      constructor
      · rintro (h|h)
        · have hs := (hl (W.get i) (List.get_mem W i)).1
          rw [h] at hs
          exact (hv hs).elim
        · exact h
      · exact Or.inr
    rw [he]
    exact ho v

noncomputable section

theorem shear_commute {r : ℕ} (bank : Fin r → ℂ) (s t : ShearCode ℕ r)
    (hs : s.dst ≠ t.src) (ht : t.dst ≠ s.src) (v : ℕ → ℂ) :
    (t.eval bank).act ((s.eval bank).act v) =
      (s.eval bank).act ((t.eval bank).act v) := by
  funext a
  by_cases h : a = s.dst
  · subst a
    by_cases g : s.dst = t.dst
    · simp [Shear.act,ShearCode.eval,g,ht.symm,t.different.symm]
      ring
    · simp [Shear.act,ShearCode.eval,g,ht.symm]
  · by_cases g : a = t.dst
    · subst a
      simp [Shear.act,ShearCode.eval,h,hs.symm]
    · simp [Shear.act,ShearCode.eval,h,g]

theorem safe_perm {r : ℕ} {W V : List (ShearCode ℕ r)} (h : W.Perm V)
    (hs : LevelSafe W) : LevelSafe V := by
  intro s hsV t htV
  exact hs s (h.mem_iff.mpr hsV) t (h.mem_iff.mpr htV)

theorem run_perm {r : ℕ} (bank : Fin r → ℂ) {W V : List (ShearCode ℕ r)}
    (h : W.Perm V) (hs : LevelSafe W) (v : ℕ → ℂ) :
    runShears (W.map (ShearCode.eval bank)) v =
      runShears (V.map (ShearCode.eval bank)) v := by
  induction h generalizing v with
  | nil => rfl
  | cons s h ih =>
    simp only [List.map_cons,runShears_cons]
    apply ih
    intro a ha b hb
    exact hs a (by simp [ha]) b (by simp [hb])
  | swap s t W =>
    simp only [List.map_cons,runShears_cons]
    rw [shear_commute bank t s (hs t (by simp) s (by simp)) (hs s (by simp) t (by simp))]
  | trans h h' ih ih' => exact (ih hs v).trans (ih' (safe_perm h hs) v)

end

/-- The fully printed order by color, retaining every indexed occurrence. -/
def colorOrdered {r : ℕ} (W : List (ShearCode ℕ r)) (delta : ℕ) : List (ShearCode ℕ r) :=
  (layerOrder (printedEdges W) delta).map W.get

theorem colorOrdered_perm {r delta : ℕ} (W : List (ShearCode ℕ r))
    (hd : DegreeBound (printedEdges W) delta) (hpos : 0 < delta) :
    (colorOrdered W delta).Perm W := by
  have h := (layerOrder_perm (printedEdges W) hd hpos).map W.get
  simpa [colorOrdered,List.ofFn_eq_map] using h

noncomputable section

/-- Coefficient values, including zero, do not affect the valid regrouping. -/
theorem colorOrdered_action {r delta : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode ℕ r))
    (hd : DegreeBound (printedEdges W) delta) (hpos : 0 < delta)
    (hs : LevelSafe W) (v : ℕ → ℂ) :
    runShears ((colorOrdered W delta).map (ShearCode.eval bank)) v =
      runShears (W.map (ShearCode.eval bank)) v :=
  run_perm bank (colorOrdered_perm W hd hpos) (safe_perm (colorOrdered_perm W hd hpos).symm hs) v

end
end ExactFourierCircuits.UniformLayeredReplay
