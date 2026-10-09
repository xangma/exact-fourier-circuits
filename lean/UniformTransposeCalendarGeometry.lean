import UniformTransposeCalendar

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeCalendarGeometry
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarRenderPieces UniformCalendarRenderPosition UniformTransposeCalendar

abbrev weight {n : ℕ} (L : List (Piece n)) := (L.map (fun p => p.descriptor.event.duration)).sum

theorem stamp_bounds {n : ℕ} (L : List (Piece n)) (start : ℕ) (p : Piece n)
    (hp : p∈stamp start L) : start≤p.descriptor.start ∧ p.descriptor.stop≤ start+weight L := by
  induction L generalizing start with
  | nil => simp [stamp] at hp
  | cons q L ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · simp only [Piece.withStart,TimedEvent.stop,weight,List.map_cons,List.sum_cons]
      omega
    · have h:=ih (start+q.descriptor.event.duration) hp
      simp only [weight,List.map_cons,List.sum_cons] at h ⊢
      omega

theorem stamp_separated {n : ℕ} (L : List (Piece n)) (start t : ℕ) :
    (stamp start L).Pairwise (fun p q => SeparatedAt t p.descriptor q.descriptor) := by
  induction L generalizing start with
  | nil => simp [stamp]
  | cons q L ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro p hp activeP activeQ
    have h:=stamp_bounds L (start+q.descriptor.event.duration) p hp
    change start≤t ∧ t<start+q.descriptor.event.duration at activeP
    exact False.elim (by have:=activeQ.1;omega)

theorem stamp_property {n : ℕ} (L : List (Piece n)) (start : ℕ)
    (Q : UniformLocalCacheTiming.Event→Prop) (h : ∀p∈L,Q p.descriptor.event) :
    ∀p∈stamp start L,Q p.descriptor.event := by
  induction L generalizing start with
  | nil => simp [stamp]
  | cons q L ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact h q (by simp)
    · exact ih _ (fun a ha => h a (by simp [ha])) p hp

theorem correction_weight (v : ℕ) (hv : 0<selected v) (o : ℕ) (f : PowerSeries ℂ) :
    weight ((pairs v).reverse.map (pairPiece v hv o f)) = (correctionSchedule v hv f).length := by
  simp only [weight,List.map_map,Function.comp_def]
  change ((pairs v).reverse.map (fun q => rectangleDuration
    (UniformLocalRectangleDescriptors.row v o (selected v) q.1.val q.2.val))).sum = _
  simp only [correctionSchedule,List.length_flatten,List.map_map,Function.comp_def]
  generalize pairs v = L
  rw [List.map_reverse,List.sum_reverse]
  have each : (fun q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v)) =>
      rectangleDuration (UniformLocalRectangleDescriptors.row v o (selected v) q.1.val q.2.val)) =
      (fun q => (pairSchedule v hv f q).length) := by
    funext q
    exact (pairSchedule_duration v hv f q).symm
  exact congrArg (fun g => (L.map g).sum) each

theorem correction_band (v : ℕ) (hv : 0<selected v) (o start : ℕ) (f : PowerSeries ℂ) :
    ∀p∈correctionPieces v hv o start f,
      Event.low p.descriptor.event=o ∧ Event.high p.descriptor.event=o+v := by
  unfold correctionPieces
  apply stamp_property _ start (fun e => Event.low e=o ∧ Event.high e=o+v)
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  exact ⟨rfl,rfl⟩

theorem calendar_bounds {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) (p : Piece v)
    (hp : p∈calendar P o start f hf) :
    start≤p.descriptor.start ∧ p.descriptor.stop≤ start+planDuration P ∧
      o≤Event.low p.descriptor.event ∧ Event.high p.descriptor.event≤o+v := by
  induction P generalizing o start with
  | direct v cap =>
    have eq:=List.mem_singleton.mp hp
    subst p
    simp only [directPiece,Piece.withStart,TimedEvent.stop,Event.duration,
      planDuration,Event.low,Event.high]
    exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
  | split v hn hv L R ihL ihR =>
    rcases List.mem_append.mp hp with hp|hp
    · rcases List.mem_append.mp hp with hp|hp
      · have times:=stamp_bounds ((pairs v).reverse.map (pairPiece v hv o f)) start p hp
        rw [correction_weight] at times
        have band:=correction_band v hv o start f p hp
        simp only [planDuration]
        rw [←correctionSchedule_duration v hv f]
        exact ⟨times.1,by omega,by omega,by omega⟩
      · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
        have h:=ihL o _ q hq
        have maxL:=Nat.le_max_left (planDuration L) (planDuration R)
        simp only [planDuration,Piece.embed]
        rw [←correctionSchedule_duration v hv f]
        exact ⟨by omega,by omega,h.2.2.1,by omega⟩
    · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
      have h:=ihR (o+v/2) _ q hq
      have maxR:=Nat.le_max_right (planDuration L) (planDuration R)
      simp only [planDuration,Piece.embed]
      rw [←correctionSchedule_duration v hv f]
      exact ⟨by omega,by omega,by omega,by omega⟩

theorem calendar_positioned {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    ∀p∈calendar P o start f hf,Positioned o p := by
  induction P generalizing o start with
  | direct v cap =>
    intro p hp
    have eq:=List.mem_singleton.mp hp
    subst p
    intro i
    rfl
  | split v hn hv L R ihL ihR =>
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · rcases List.mem_append.mp hp with hp|hp
      · apply stamp_positioned o start ((pairs v).reverse.map (pairPiece v hv o f)) _ p hp
        intro q hq
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
        intro i
        rfl
      · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
        intro i
        change o+(left v (q.position i)).val=_
        rw [left_val]
        exact ihL o _ q hq i
    · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
      intro i
      change o+(right v (q.position i)).val=_
      rw [right_val]
      have h:=ihR (o+v/2) _ q hq i
      simpa only [Nat.add_assoc,Piece.embed] using h


theorem calendar_separated {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (calendar P o start f hf).Pairwise (fun p q => SeparatedAt t p.descriptor q.descriptor) := by
  induction P generalizing o start with
  | direct v cap => simp [calendar]
  | split v hn hv L R ihL ihR =>
    rw [calendar,List.append_assoc]
    apply List.pairwise_append.mpr
    refine ⟨stamp_separated _ start t,?_,?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨?_,?_,?_⟩
      · simpa only [List.pairwise_map,Piece.embed] using ihL o
          (start+(correctionSchedule v hv f).length+(max (planDuration L) (planDuration R)-planDuration L))
      · simpa only [List.pairwise_map,Piece.embed] using ihR (o+v/2)
          (start+(correctionSchedule v hv f).length+(max (planDuration L) (planDuration R)-planDuration R))
      · intro p hp q hq _ _
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
        obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hq
        have leftBound:=calendar_bounds L o _ f hf a ha
        have rightBound:=calendar_bounds R (o+v/2) _ f hf b hb
        exact Or.inl (by change Event.high a.descriptor.event≤Event.low b.descriptor.event;omega)
    · intro p hp q hq activeP activeQ
      have before:=stamp_bounds ((pairs v).reverse.map (pairPiece v hv o f)) start p hp
      rw [correction_weight] at before
      rcases List.mem_append.mp hq with hq|hq
      · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
        have after:=calendar_bounds L o _ f hf a ha
        exact False.elim (by have:=activeP.2;have:=activeQ.1;change a.descriptor.start≤t at this;omega)
      · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
        have after:=calendar_bounds R (o+v/2) _ f hf a ha
        exact False.elim (by have:=activeP.2;have:=activeQ.1;change a.descriptor.start≤t at this;omega)

end
end ExactFourierCircuits.UniformTransposeCalendarGeometry
