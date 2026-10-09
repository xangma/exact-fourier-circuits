import UniformLocalCacheTreeCoverage
import UniformLocalReplayAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTiming
open UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformWorkspacePlanner UniformBalancedToeplitz

/-- Literal kernel/monomial slots, including empty colored matchings. -/
def directDuration (v : ℕ) : ℕ := v + 14*v*(v-1)
def rectangleDuration (q : Row) : ℕ := 28*(4*(8*exponent q.a q.e+7)+2)*11
def rectanglesDuration (L : List Row) : ℕ := (L.map rectangleDuration).sum
def treeDuration : Tree → ℕ
 | .direct v _ => directDuration v
 | .split v o b L R => max (treeDuration L) (treeDuration R) + rectanglesDuration (rows v o b)
def planDuration : {v : ℕ} → Plan v → ℕ
 | _,.direct v _ => directDuration v
 | _,.split v _ _ L R => max (planDuration L) (planDuration R) +
   rectanglesDuration (rows v 0 (selected v))

lemma rectangle_duration_offset (q : Row) (o : ℕ) :
 rectangleDuration ({q with offset := o} : Row)=rectangleDuration q := rfl
lemma row_duration_offset (v o b i j : ℕ) :
 rectangleDuration (row v o b i j)=rectangleDuration (row v 0 b i j) := rfl
lemma rectangles_duration_offset (v o b : ℕ) :
 rectanglesDuration (rows v o b)=rectanglesDuration (rows v 0 b) := by
 simp only [rectanglesDuration,rows,List.map_flatMap,List.map_map,Function.comp_def]
 rfl
lemma ofPlan_duration {v : ℕ} (P : Plan v) (o : ℕ) :
 treeDuration (ofPlan P o)=planDuration P := by
 induction P generalizing o with
 | direct v _ => rfl
 | split v _ _ L R ihL ihR =>
   simp only [ofPlan,treeDuration,planDuration,ihL,ihR,rectangles_duration_offset]

noncomputable section
lemma pairSchedule_duration (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ)
 (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) :
 (UniformLocalFourierLayers.pairSchedule v hv f q).length=
 rectangleDuration (row v 0 (selected v) q.1.val q.2.val) := by
 unfold UniformLocalFourierLayers.pairSchedule UniformLocalFourierLayers.selectedSchedule
 rw [UniformLocalFourierLayers.chunkSchedule_length]
 rfl

lemma correctionSchedule_duration (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ) :
 (UniformLocalFourierLayers.correctionSchedule v hv f).length=
 rectanglesDuration (rows v 0 (selected v)) := by
 have eq:(pairs v).map (fun q=>(UniformLocalFourierLayers.pairSchedule v hv f q).length)=
   (pairs v).map (fun q=>rectangleDuration (row v 0 (selected v) q.1.val q.2.val)):=by
  apply List.map_congr_left
  intro q _
  exact pairSchedule_duration v hv f q
 change (((pairs v).map (UniformLocalFourierLayers.pairSchedule v hv f)).flatten).length=_
 rw [List.length_flatten,List.map_map]
 simp only [Function.comp_def]
 rw [eq]
 rw [rectanglesDuration,rows_pairs,List.map_map]
 rfl

/-- Exact slot count of the actual algebraic balanced schedule, rather than a
bound or a serialized sum of child durations. -/
lemma render_duration {v : ℕ} (P : Plan v) (f : PowerSeries ℂ)
 (hf : PowerSeries.constantCoeff f ≠ 0) :
 (UniformLocalFourierLayers.render P f hf).length=planDuration P := by
 induction P with
 | direct v cap =>
   change (UniformLocalFourierLayers.serial (UniformBalancedToeplitz.render (.direct v cap) f hf)).length=_
   rw [UniformLocalFourierLayers.serial_length]
   dsimp only [UniformBalancedToeplitz.render,planDuration]
   split_ifs with hv
   · rw [UniformDirectToeplitz.word_length]
     rfl
   · have zero:v=0:=by omega
     subst v
     rfl
 | split v hn hv L R ihL ihR =>
   change (UniformLocalFourierLayers.parallel (coordinates v)
     (UniformLocalFourierLayers.render L f hf) (UniformLocalFourierLayers.render R f hf) ++
     UniformLocalFourierLayers.correctionSchedule v hv f).length=_
   rw [List.length_append,UniformLocalFourierLayers.parallel_length,ihL,ihR,
     correctionSchedule_duration]
   rfl

lemma macro_duration {r N o v : ℕ} (b : UniformLocalPreparationDAG.State r N o)
 (P : Plan v) (hN : v ≤ N) (hc : UniformLocalPreparationReferences.Covered b P hN)
 (roots : Fin r→ℂ) (f : PowerSeries ℂ)
 (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
 (hg : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
 (hf : PowerSeries.constantCoeff f ≠ 0) :
 ((UniformLocalPreparationReferences.renderMacro b P hN hc).expand (b.program.eval roots)
  (UniformLocalPreparationReferences.renderMacro_valid b P hN hc roots f hi hf)).length=
 planDuration P := by
 rw [UniformLocalPreparationReferences.renderMacro_expand b P hN hc roots f hi hg hf]
 exact render_duration P f hf
end

/-- Control-only event descriptors. Their coefficients are prepared separately. -/
inductive Event where
 | direct (width offset : ℕ)
 | rectangle (q : Row)
 deriving Repr, DecidableEq
def Event.duration : Event→ℕ
 | .direct v _ => directDuration v
 | .rectangle q => rectangleDuration q
structure TimedEvent where
 start : ℕ
 event : Event
 deriving Repr, DecidableEq
def TimedEvent.stop (t : TimedEvent) : ℕ := t.start+t.event.duration
def sequenceRows : ℕ→List Row→List TimedEvent
 | _,[] => []
 | t,q::qs => ⟨t,.rectangle q⟩::sequenceRows (t+rectangleDuration q) qs
def treeTimed (start : ℕ) : Tree→List TimedEvent
 | .direct v o => [⟨start,.direct v o⟩]
 | .split v o b L R => treeTimed start L++treeTimed start R++
    sequenceRows (start+max (treeDuration L) (treeDuration R)) (rows v o b)

lemma sequenceRows_length (t : ℕ) (L : List Row) :
 (sequenceRows t L).length=L.length := by
 induction L generalizing t with
 | nil => rfl
 | cons q L ih => simp only [sequenceRows,List.length_cons,ih]
lemma sequenceRows_bounds (t : ℕ) (L : List Row) (e : TimedEvent)
 (he : e ∈ sequenceRows t L) : t ≤ e.start ∧ e.stop ≤ t+rectanglesDuration L := by
 induction L generalizing t with
 | nil => simp only [sequenceRows,List.not_mem_nil] at he
 | cons q L ih =>
   simp only [sequenceRows,List.mem_cons] at he
   rcases he with rfl|he
   · simp only [TimedEvent.stop,Event.duration,rectanglesDuration,List.map_cons,List.sum_cons]
     omega
   · have h:=ih (t+rectangleDuration q) he
     simp only [rectanglesDuration,List.map_cons,List.sum_cons] at h ⊢
     omega
lemma timed_bounds (T : Tree) (start : ℕ) (e : TimedEvent)
 (he : e ∈ treeTimed start T) : start ≤ e.start ∧ e.stop ≤ start+treeDuration T := by
 induction T generalizing start with
 | direct v o =>
   simp only [treeTimed,List.mem_singleton] at he
   subst e
   simp only [treeDuration,TimedEvent.stop,Event.duration]
   omega
 | split v o b L R ihL ihR =>
   simp only [treeTimed,List.mem_append] at he
   simp only [treeDuration]
   rcases he with (he|he)|he
   · have h:=ihL start he
     have hm:=le_max_left (treeDuration L) (treeDuration R)
     omega
   · have h:=ihR start he
     have hm:=le_max_right (treeDuration L) (treeDuration R)
     omega
   · have h:=sequenceRows_bounds (start+max (treeDuration L) (treeDuration R)) (rows v o b) e he
     omega

/-- Parallel children share their entry time. The following cross sequence
begins only after the longer child, preserving the paper's idle padding. -/
lemma timed_split (v o b start : ℕ) (L R : Tree) :
 treeTimed start (.split v o b L R : Tree)=treeTimed start L++treeTimed start R++
 sequenceRows (start+max (treeDuration L) (treeDuration R)) (rows v o b) := rfl

lemma rectangle_slots_duration (q : Row) : rectangleDuration q=
 28*(UniformLocalCacheChronology.replaySlots (8*exponent q.a q.e+6)).length := by
 rw [UniformLocalCacheChronology.replaySlots_length]
 unfold rectangleDuration
 ring

end ExactFourierCircuits.UniformLocalCacheTiming
