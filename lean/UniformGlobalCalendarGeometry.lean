import UniformCacheTimingEvents
import UniformLayerSnapshotCount

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarGeometry
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformBalancedToeplitz UniformCacheTimingEvents

def Active (e : TimedEvent) (t : ℕ) : Prop := e.start ≤ t ∧ t < e.stop

def Event.low : Event → ℕ
  | .direct _ o => o
  | .rectangle q => q.offset

def Event.high : Event → ℕ
  | .direct v o => o + v
  | .rectangle q => q.offset + q.width

def DisjointBands (e f : TimedEvent) : Prop :=
  Event.high e.event ≤ Event.low f.event ∨ Event.high f.event ≤ Event.low e.event

def SeparatedAt (t : ℕ) (e f : TimedEvent) : Prop :=
  Active e t → Active f t → DisjointBands e f

lemma sequenceRows_event (start : ℕ) (L : List Row) (e : TimedEvent)
    (he : e ∈ sequenceRows start L) : ∃ q ∈ L, e.event = .rectangle q := by
  induction L generalizing start with
  | nil => simp [sequenceRows] at he
  | cons q L ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨q, by simp, rfl⟩
    · obtain ⟨p,hp,eq⟩ := ih _ he
      exact ⟨p, by simp [hp], eq⟩

lemma rows_shape (v o b : ℕ) (q : Row) (hq : q ∈ rows v o b) :
    q.width = v ∧ q.offset = o := by
  obtain ⟨i,_,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl,rfl⟩

lemma sequenceRows_band (v o b start : ℕ) (e : TimedEvent)
    (he : e ∈ sequenceRows start (rows v o b)) :
    Event.low e.event = o ∧ Event.high e.event = o + v := by
  obtain ⟨q,hq,eq⟩ := sequenceRows_event _ _ e he
  rw [eq]
  obtain ⟨width,offset⟩ := rows_shape v o b q hq
  simp [Event.low, Event.high, width, offset]

/-- Every event borrows only its genuine original subtree interval. -/
lemma tree_band {v : ℕ} (P : Plan v) (o start : ℕ) (e : TimedEvent)
    (he : e ∈ treeTimed start (ofPlan P o)) :
    o ≤ Event.low e.event ∧ Event.high e.event ≤ o + v := by
  induction P generalizing o start with
  | direct v cap =>
    have eq : e = ⟨start,.direct v o⟩ := List.mem_singleton.mp he
    subst e
    simp [Event.low, Event.high]
  | split v hn hv L R ihL ihR =>
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · have h := ihL o start he
        omega
      · have h := ihR (o + v / 2) start he
        omega
    · have h := sequenceRows_band v o _ _ e he
      rw [h.1,h.2]
      exact ⟨le_rfl,le_rfl⟩

/-- A sequential rectangle stream can never have two active entries. -/
lemma sequenceRows_separated (start t : ℕ) (L : List Row) :
    (sequenceRows start L).Pairwise (SeparatedAt t) := by
  induction L generalizing start with
  | nil => simp [sequenceRows]
  | cons q L ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro e he a b
    rcases b with ⟨bt,_⟩
    have bound := sequenceRows_bounds (start + rectangleDuration q) L e he
    change start ≤ t ∧ t < start + rectangleDuration q at a
    exact False.elim (by omega)

/-- Parallel children may both be active, but their original intervals are disjoint.
Parent rectangles begin only after both children finish. -/
theorem tree_separated {v : ℕ} (P : Plan v) (o start t : ℕ) :
    (treeTimed start (ofPlan P o)).Pairwise (SeparatedAt t) := by
  induction P generalizing o start with
  | direct v cap => simp [ofPlan,treeTimed]
  | split v hn hv L R ihL ihR =>
    let left := treeTimed start (ofPlan L o)
    let right := treeTimed start (ofPlan R (o + v / 2))
    let barrier := start + max (treeDuration (ofPlan L o)) (treeDuration (ofPlan R (o + v / 2)))
    let correction := sequenceRows barrier (rows v o (UniformWorkspacePlanner.selected v))
    change ((left ++ right) ++ correction).Pairwise (SeparatedAt t)
    apply List.pairwise_append.mpr
    refine ⟨?_,sequenceRows_separated _ _ _,?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨ihL o start,ihR (o + v / 2) start,?_⟩
      intro e he f hf _ _
      have hl := tree_band L o start e he
      have hr := tree_band R (o + v / 2) start f hf
      exact Or.inl (by omega)
    · intro e he f hf ae af
      rcases ae with ⟨_,ae⟩
      rcases af with ⟨af,_⟩
      have corr := sequenceRows_bounds barrier _ f hf
      have child : e.stop ≤ barrier := by
        rcases List.mem_append.mp he with he | he
        · have h := timed_bounds (ofPlan L o) start e he
          have hm := le_max_left (treeDuration (ofPlan L o)) (treeDuration (ofPlan R (o + v / 2)))
          omega
        · have h := timed_bounds (ofPlan R (o + v / 2)) start e he
          have hm := le_max_right (treeDuration (ofPlan L o)) (treeDuration (ofPlan R (o + v / 2)))
          omega
      exact False.elim (by omega)

/-- Real preparation-order events inherit the parallel schedule's separation. -/
theorem actual_walk_separated (v o R start t : ℕ) :
    (UniformCacheTimingEvents.events start
      (UniformLocalCacheTreeMachine.walk (2 * v + 1) 0 R [⟨v,o,0,0⟩]).1).Pairwise (SeparatedAt t) := by
  have hs : ∀ {e f}, SeparatedAt t e f → SeparatedAt t f e := by
    intro e f h af ae
    rcases h ae af with h | h
    · exact Or.inr h
    · exact Or.inl h
  exact ((root_events v o R start).pairwise_iff hs).mpr (tree_separated (plan v) o start t)

/-- The exact physical ordinary ABI timestamp selects its local matching and phase. -/
theorem ordinary_clock (start j t : ℕ)
    (lo : start + 28 * j ≤ t) (hi : t < start + 28 * (j + 1)) :
    (t - start) / 28 = j ∧ (t - start) % 28 = t - (start + 28 * j) := by
  omega

theorem ordinary_disjoint (start i j t : ℕ) (ne : i ≠ j)
    (iLo : start + 28 * i ≤ t) (iHi : t < start + 28 * (i + 1))
    (jLo : start + 28 * j ≤ t) (jHi : t < start + 28 * (j + 1)) : False := by
  have hi := (ordinary_clock start i t iLo iHi).1
  have hj := (ordinary_clock start j t jLo jHi).1
  exact ne (hi.symm.trans hj)

end ExactFourierCircuits.UniformGlobalCalendarGeometry
