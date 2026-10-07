import UniformLayeredReplay
import UniformToeplitzCrossDAG

set_option autoImplicit false

/-! Stable depth grouping of actual topological printed sweeps.  Only integer
labels and endpoints affect their ordering; no scalar value is inspected.
These finite schedules do not claim a RAM implementation of sorting/coloring. -/
namespace ExactFourierCircuits.UniformDAGLayers
open UniformReplayPrint UniformLayeredReplay UniformColoring UniformToeplitzCrossDAG
open OAI.ExactFourier

variable {r : ℕ}

/-- Stable insertion sort by the actual destination depth. -/
def depthOrdered (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) : List (ShearCode ℕ r) :=
  W.insertionSort (fun s t => level s.dst ≤ level t.dst)

def Causal (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) : Prop :=
  (∀ s ∈ W, s.src < s.dst ∧ level s.src < level s.dst) ∧
    W.Pairwise (fun s t => s.dst ≤ t.dst)

lemma depthOrdered_perm (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) :
    (depthOrdered W level).Perm W := List.perm_insertionSort _ _

lemma depthOrdered_pairwise (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) :
    (depthOrdered W level).Pairwise (fun s t => level s.dst ≤ level t.dst) := by
  apply List.pairwise_insertionSort

noncomputable section

lemma orderedInsert_action (bank : Fin r → ℂ) (s : ShearCode ℕ r)
    (W : List (ShearCode ℕ r)) (level : ℕ → ℕ)
    (hs : s.src < s.dst)
    (hw : ∀ t ∈ W, s.dst ≤ t.dst ∧ level t.src < level t.dst)
    (v : ℕ → ℂ) :
    runShears ((W.orderedInsert (fun a b => level a.dst ≤ level b.dst) s).map (ShearCode.eval bank)) v =
      runShears (W.map (ShearCode.eval bank)) ((s.eval bank).act v) := by
  induction W generalizing v with
  | nil => rfl
  | cons t W ih =>
    rw [List.orderedInsert_cons]
    split
    · rfl
    · rename_i hst
      simp only [List.map_cons,runShears_cons]
      rw [ih (fun a ha => hw a (by simp [ha]))]
      have hts : t.dst ≠ s.src := by have := (hw t (by simp)).1; omega
      have hst' : s.dst ≠ t.src := by
        intro h
        have := (hw t (by simp)).2
        rw [← h] at this
        omega
      rw [shear_commute bank t s hts hst']

/-- Reordering only moves mutually independent inversions. Whole-DAG level
safety is neither assumed nor needed. -/
theorem depthOrdered_action (bank : Fin r → ℂ) (W : List (ShearCode ℕ r))
    (level : ℕ → ℕ) (hc : Causal W level) (v : ℕ → ℂ) :
    runShears ((depthOrdered W level).map (ShearCode.eval bank)) v =
      runShears (W.map (ShearCode.eval bank)) v := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
    have hp := List.pairwise_cons.mp hc.2
    have hW : Causal W level := ⟨fun t ht => hc.1 t (by simp [ht]),hp.2⟩
    change runShears (((depthOrdered W level).orderedInsert
      (fun a b => level a.dst ≤ level b.dst) s).map (ShearCode.eval bank)) v = _
    rw [orderedInsert_action bank s _ level (hc.1 s (by simp)).1
      (fun t ht => ⟨hp.1 t ((depthOrdered_perm W level).mem_iff.mp ht),
        (hW.1 t ((depthOrdered_perm W level).mem_iff.mp ht)).2⟩), ih hW]
    rfl

end

/-- Retain every indexed occurrence in increasing depth, including zero coefficients. -/
def bucketsFrom (start count : ℕ) (level : ℕ → ℕ) :
    List (ShearCode ℕ r) → List (List (ShearCode ℕ r))
  | W => match count with
    | 0 => []
    | c+1 => W.filter (fun s => decide (level s.dst = start)) ::
        bucketsFrom (start+1) c level (W.filter (fun s => decide (start < level s.dst)))

lemma bucketsFrom_length (start count : ℕ) (level : ℕ → ℕ) (W : List (ShearCode ℕ r)) :
    (bucketsFrom start count level W).length = count := by
  induction count generalizing start W with
  | zero => rfl
  | succ c ih => simp only [bucketsFrom,List.length_cons,ih]

lemma sorted_split (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (start : ℕ)
    (hp : W.Pairwise (fun s t => level s.dst ≤ level t.dst))
    (hl : ∀ s ∈ W, start ≤ level s.dst) :
    W.filter (fun s => decide (level s.dst = start)) ++
      W.filter (fun s => decide (start < level s.dst)) = W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    have hpair := List.pairwise_cons.mp hp
    have htail := fun (t : ShearCode ℕ r) (ht : t ∈ W) => hl t (by simp [ht])
    by_cases hs : level s.dst=start
    · simpa [hs] using congrArg (List.cons s) (ih hpair.2 htail)
    · have hgt : start < level s.dst := by have := hl s (by simp); omega
      have hnone : W.filter (fun t => decide (level t.dst=start))=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht
        have := hpair.1 t ht
        intro h
        have := of_decide_eq_true h
        omega
      have h := ih hpair.2 htail
      rw [hnone,List.nil_append] at h
      simp [hs,hgt,hnone,h]

lemma bucketsFrom_flatten (start count : ℕ) (level : ℕ → ℕ) (W : List (ShearCode ℕ r))
    (hp : W.Pairwise (fun s t => level s.dst ≤ level t.dst))
    (hb : ∀ s ∈ W, start ≤ level s.dst ∧ level s.dst < start+count) :
    (bucketsFrom start count level W).flatten = W := by
  induction count generalizing start W with
  | zero =>
    have he : W=[] := by
      cases W with
      | nil => rfl
      | cons s W => have := hb s (by simp); omega
    simp [he,bucketsFrom]
  | succ c ih =>
    simp only [bucketsFrom,List.flatten_cons]
    rw [ih (start+1) _ (hp.filter _) (by
      intro s hs
      have hm := List.mem_filter.mp hs
      have := hb s hm.1
      have := of_decide_eq_true hm.2
      omega)]
    exact sorted_split W level start hp (fun s hs => (hb s hs).1)

lemma bucketsFrom_onLevel (start count : ℕ) (level : ℕ → ℕ) (W : List (ShearCode ℕ r))
    (hsource : ∀ s ∈ W, level s.src < level s.dst) :
    ∀ V ∈ bucketsFrom start count level W, ∃ d, OnLevel V level d := by
  induction count generalizing start W with
  | zero => simp [bucketsFrom]
  | succ c ih =>
    intro V hV
    simp only [bucketsFrom,List.mem_cons] at hV
    rcases hV with rfl | hV
    · refine ⟨start,fun s hs => ?_⟩
      have hm := List.mem_filter.mp hs
      have he := of_decide_eq_true hm.2
      exact ⟨he, by simpa only [← he] using hsource s hm.1⟩
    · exact ih (start+1) _ (fun s hs => hsource s (List.mem_filter.mp hs).1) V hV

/-- Actual physical integer ports, with the literal-zero port n left unused. -/
def natSweep {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    List (ShearCode ℕ r) :=
  p.sweep enabled (fun i => i.val) (fun j => n+1+j.val)
    (by intro i j h; apply Fin.ext; change n+1+i.val=n+1+j.val at h; omega)
    (by intro i j; have := i.isLt; omega)

/-- The real typed program's constructor-longest-path labels, extended outside its storage. -/
def natLevel {n k : ℕ} (p : UniformReplayPrint.Program r n k) (a : ℕ) : ℕ :=
  if h : a < n+1+k then runDepth p (fun _ => 0) ⟨a,h⟩ else 0

lemma natLevel_at {n k : ℕ} (p : UniformReplayPrint.Program r n k) (a : Fin (n+1+k)) :
    natLevel p a.val = runDepth p (fun _ => 0) a := by simp [natLevel,a.isLt]

lemma natLevel_step_old {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (g : UniformReplayPrint.Gate r (n+1+k)) (a : ℕ) (ha : a < n+1+k) :
    natLevel (p.step g) a = natLevel p a := by
  rw [natLevel, dite_eq_left (by omega), natLevel, dite_eq_left ha]
  change (Fin.snoc (runDepth p (fun _ => 0)) (gateDepth (runDepth p (fun _ => 0)) g) :
    Fin (n+1+k+1) → ℕ)
    (Fin.castSucc (⟨a,ha⟩ : Fin (n+1+k))) = _
  rw [Fin.snoc_castSucc]

lemma natLevel_step_last {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (g : UniformReplayPrint.Gate r (n+1+k)) :
    natLevel (p.step g) (n+1+k) = gateDepth (runDepth p (fun _ => 0)) g := by
  rw [natLevel,dite_eq_left (by omega)]
  exact Fin.snoc_last _ _

lemma referenceMap_nat_some {n k : ℕ} (enabled : Bool) (a : Fin (n+1+k)) (v : ℕ)
    (h : referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val) a = some v) :
    v=a.val := by
  revert h
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · intro h
    revert h
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro h; simp [referenceMap] at h
    · intro h; cases enabled <;> simp_all [referenceMap]
  · intro h; simpa [referenceMap] using h.symm

lemma reference_member (d : ℕ) (ref : Option ℕ) (c : Coefficient r)
    (h : ∀ i, ref=some i → d≠i) (s : ShearCode ℕ r)
    (hs : s ∈ reference d ref c h) : s.dst=d ∧ ref=some s.src := by
  cases ref with
  | none => simp [reference] at hs
  | some a =>
    simp only [reference,List.mem_singleton] at hs
    subst s
    exact ⟨rfl,rfl⟩

lemma gateCode_member (d : ℕ) {w : ℕ} (refs : Fin w → Option ℕ)
    (h : ∀ a i, refs a=some i → d≠i) (g : UniformReplayPrint.Gate r w)
    (dep : Fin w → ℕ) (s : ShearCode ℕ r) (hs : s∈gateCode d refs h g) :
    s.dst=d ∧ ∃ a : Fin w, refs a=some s.src ∧ dep a < gateDepth dep g := by
  cases g with
  | add a b =>
    simp only [gateCode,List.mem_append] at hs
    rcases hs with hs|hs
    · have he := reference_member _ _ _ _ _ hs
      exact ⟨he.1,a,he.2,by simp only [gateDepth]; omega⟩
    · have he := reference_member _ _ _ _ _ hs
      exact ⟨he.1,b,he.2,by simp only [gateDepth]; omega⟩
  | sub a b =>
    simp only [gateCode,List.mem_append] at hs
    rcases hs with hs|hs
    · have he := reference_member _ _ _ _ _ hs
      exact ⟨he.1,a,he.2,by simp only [gateDepth]; omega⟩
    · have he := reference_member _ _ _ _ _ hs
      exact ⟨he.1,b,he.2,by simp only [gateDepth]; omega⟩
  | scale c a =>
    have he := reference_member _ _ _ _ _ hs
    exact ⟨he.1,a,he.2,by simp only [gateDepth]; omega⟩

lemma natSweep_step {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (g : UniformReplayPrint.Gate r (n+1+k)) (enabled : Bool) :
    natSweep (p.step g) enabled = natSweep p enabled ++
      gateCode (n+1+k)
        (referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val))
        (referenceMap_avoids enabled _ _ _
          (by intro i; have := i.isLt; omega) (by intro j; have := j.isLt; omega)) g := rfl

lemma natSweep_bounds {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    ∀ s∈natSweep p enabled, n<s.dst ∧ s.dst<n+1+k ∧ s.src<s.dst := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep]
  | @step k p g ih =>
    rw [natSweep_step]
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · have he := ih s hs
      exact ⟨he.1,by omega,he.2.2⟩
    · obtain ⟨hd,a,ha,_⟩ := gateCode_member _ _ _ g (runDepth p (fun _ => 0)) s hs
      have hr := referenceMap_nat_some enabled a s.src ha
      rw [hd,hr]
      have := a.isLt
      omega

lemma natSweep_depth {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    ∀ s∈natSweep p enabled, natLevel p s.src < natLevel p s.dst := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep]
  | @step k p g ih =>
    rw [natSweep_step]
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · have hb := natSweep_bounds p enabled s hs
      rw [natLevel_step_old p g s.src (by omega),natLevel_step_old p g s.dst hb.2.1]
      exact ih s hs
    · obtain ⟨hd,a,ha,hdep⟩ := gateCode_member _ _ _ g (runDepth p (fun _ => 0)) s hs
      have hr := referenceMap_nat_some enabled a s.src ha
      rw [hd,hr,natLevel_step_last,natLevel_step_old p g a.val a.isLt,natLevel_at]
      exact hdep

lemma natSweep_pairwise {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    (natSweep p enabled).Pairwise (fun s t => s.dst ≤ t.dst) := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep]
  | @step k p g ih =>
    rw [natSweep_step,List.pairwise_append]
    refine ⟨ih,?_,?_⟩
    · apply List.Pairwise.imp_of_mem (R := fun _ _ => True) ?_
        (List.pairwise_of_forall (fun _ _ => True.intro))
      intro s t hs ht _
      have hd := (gateCode_member _ _ _ g (runDepth p (fun _ => 0)) s hs).1
      have he := (gateCode_member _ _ _ g (runDepth p (fun _ => 0)) t ht).1
      rw [hd,he]
    · intro s hs t ht
      have hd := (natSweep_bounds p enabled s hs).2.1
      have he := (gateCode_member _ _ _ g (runDepth p (fun _ => 0)) t ht).1
      omega

theorem natSweep_causal {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    Causal (natSweep p enabled) (natLevel p) :=
  ⟨fun s hs => ⟨(natSweep_bounds p enabled s hs).2.2,natSweep_depth p enabled s hs⟩,
    natSweep_pairwise p enabled⟩

noncomputable section

/-- Whole actual sweep action, with arbitrary dirty storage, is preserved. -/
theorem sorted_natSweep_action {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (bank : Fin r → ℂ) (enabled : Bool) (v : ℕ → ℂ) :
    runShears ((depthOrdered (natSweep p enabled) (natLevel p)).map (ShearCode.eval bank)) v =
      runShears ((natSweep p enabled).map (ShearCode.eval bank)) v :=
  depthOrdered_action bank _ _ (natSweep_causal p enabled) v

end

def depthBuckets (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (H : ℕ) :
    List (List (ShearCode ℕ r)) := bucketsFrom 0 (H+1) level (depthOrdered W level)

lemma depthBuckets_length (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (H : ℕ) :
    (depthBuckets W level H).length = H+1 := bucketsFrom_length ..

lemma depthBuckets_flatten (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (H : ℕ)
    (hb : ∀ s∈W, level s.dst ≤ H) :
    (depthBuckets W level H).flatten = depthOrdered W level := by
  apply bucketsFrom_flatten _ _ _ _ (depthOrdered_pairwise W level)
  intro s hs
  have := hb s ((depthOrdered_perm W level).mem_iff.mp hs)
  omega

lemma depthBuckets_onLevel (W : List (ShearCode ℕ r)) (level : ℕ → ℕ) (H : ℕ)
    (hs : ∀ s∈W, level s.src < level s.dst) :
    ∀ V∈depthBuckets W level H, ∃ d, OnLevel V level d :=
  bucketsFrom_onLevel _ _ _ _ (fun s h => hs s ((depthOrdered_perm W level).mem_iff.mp h))

/-- Integer color classes, preserving their original indexed occurrences. -/
def colorBlocks (W : List (ShearCode ℕ r)) (delta : ℕ) : List (List (ShearCode ℕ r)) :=
  (layers (printedEdges W) delta).map (fun is => is.map W.get)

lemma colorBlocks_flatten (W : List (ShearCode ℕ r)) (delta : ℕ) :
    (colorBlocks W delta).flatten = colorOrdered W delta := by
  simp [colorBlocks,colorOrdered,layerOrder,List.map_flatten]

lemma colorBlocks_length (W : List (ShearCode ℕ r)) (delta : ℕ) :
    (colorBlocks W delta).length = 2*delta-1 := by simp [colorBlocks]

def coloredBuckets (B : List (List (ShearCode ℕ r))) (delta : ℕ) :
    List (List (ShearCode ℕ r)) := B.flatMap (fun W => colorBlocks W delta)

lemma coloredBuckets_length (B : List (List (ShearCode ℕ r))) (delta : ℕ) :
    (coloredBuckets B delta).length = B.length*(2*delta-1) := by
  induction B with
  | nil => simp [coloredBuckets]
  | cons W B ih => simp only [coloredBuckets,List.flatMap_cons,List.length_append,
      colorBlocks_length,List.length_cons] at *; rw [ih]; ring

noncomputable section

lemma coloredBuckets_action (bank : Fin r → ℂ) (B : List (List (ShearCode ℕ r)))
    (delta : ℕ) (hpos : 0<delta)
    (hb : ∀ W∈B, DegreeBound (printedEdges W) delta ∧ LevelSafe W) (v : ℕ → ℂ) :
    runShears ((coloredBuckets B delta).flatten.map (ShearCode.eval bank)) v =
      runShears (B.flatten.map (ShearCode.eval bank)) v := by
  induction B generalizing v with
  | nil => rfl
  | cons W B ih =>
    simp only [coloredBuckets,List.flatMap_cons,List.flatten_append,List.flatten_cons,
      List.map_append,runShears_append]
    rw [colorBlocks_flatten,colorOrdered_action bank W (hb W (by simp)).1 hpos (hb W (by simp)).2]
    exact ih (fun V hV => hb V (by simp [hV])) _

end

/-- Literal forward layers: depth first, then integer edge color within that depth. -/
def layeredSweep {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (enabled : Bool) (H delta : ℕ) : List (List (ShearCode ℕ r)) :=
  coloredBuckets (depthBuckets (natSweep p enabled) (natLevel p) H) delta

lemma layeredSweep_length {n k : ℕ} (p : UniformReplayPrint.Program r n k)
    (enabled : Bool) (H delta : ℕ) :
    (layeredSweep p enabled H delta).length = (H+1)*(2*delta-1) := by
  rw [layeredSweep,coloredBuckets_length,depthBuckets_length]

lemma natSweep_depthBound {n a H : ℕ} (D : DAG r n a) (enabled : Bool) (hD : DepthBound D H) :
    ∀ s∈natSweep D.program enabled, natLevel D.program s.dst ≤ H := by
  intro s hs
  have hb := (natSweep_bounds D.program enabled s hs).2.1
  rw [natLevel,dite_eq_left hb]
  exact hD _

lemma uses_card (W : List (ShearCode ℕ r)) (f : ShearCode ℕ r → ℕ) (v : ℕ) :
    (Finset.univ.filter (fun i : Fin W.length => f (W.get i)=v)).card =
      W.countP (fun s => decide (f s=v)) := by
  rw [← List.toFinset_finRange W.length,(List.nodup_finRange W.length).card_eq_countP]
  have hm : (List.finRange W.length).map W.get = W := by
    rw [← List.ofFn_eq_map,List.ofFn_get]
  conv_rhs => rw [← hm,List.countP_map]
  rfl

lemma reference_src_count (d : ℕ) (ref : Option ℕ) (c : Coefficient r)
    (h : ∀ i, ref=some i → d≠i) (a v : ℕ) (hval : ∀ i, ref=some i → i=a) :
    (reference d ref c h).countP (fun s => decide (s.src=v)) ≤ (if a=v then 1 else 0) := by
  cases ref with
  | none => simp [reference]
  | some b => have hb := hval b rfl; simp [reference,hb]

lemma gateCode_src_count (d : ℕ) {n k : ℕ} (enabled : Bool)
    (h : ∀ a i, referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val) a=some i → d≠i)
    (g : UniformReplayPrint.Gate r (n+1+k)) (v : ℕ) :
    (gateCode d (referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val)) h g).countP
      (fun s => decide (s.src=v)) ≤ (gateRecord g).refs.count v := by
  have hc (a : Fin (n+1+k)) (c : Coefficient r) :
      (reference d (referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val) a) c (h a)).countP
        (fun s => decide (s.src=v)) ≤ (if a.val=v then 1 else 0) := by
    exact reference_src_count _ _ _ _ a.val v
      (fun b hb => referenceMap_nat_some enabled a b hb)
  cases g with
  | add a b =>
    simp only [gateCode,List.countP_append,gateRecord,UniformConvolutionDAG.Expr.refs,
      List.count_cons,List.count_nil]
    simp only [beq_iff_eq]
    have := hc a (.rational 1); have := hc b (.rational 1)
    omega
  | sub a b =>
    simp only [gateCode,List.countP_append,gateRecord,UniformConvolutionDAG.Expr.refs,
      List.count_cons,List.count_nil]
    simp only [beq_iff_eq]
    have := hc a (.rational 1); have := hc b (.rational (-1))
    omega
  | scale c a =>
    simpa only [gateCode,gateRecord,UniformConvolutionDAG.Expr.refs,List.count_singleton,beq_iff_eq] using hc a c

lemma natSweep_src_count {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) (v : ℕ) :
    (natSweep p enabled).countP (fun s => decide (s.src=v)) ≤ (allRefs p).count v := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep,allRefs,programRecords]
  | @step k p g ih =>
    rw [natSweep_step,List.countP_append]
    simp only [allRefs,programRecords,List.flatMap_append,List.flatMap_singleton,List.count_append]
    exact Nat.add_le_add ih (gateCode_src_count _ enabled _ g v)

lemma countP_zero {α : Type} (W : List α) (P : α → Bool) (h : ∀ a∈W, P a=false) :
    W.countP P=0 := by
  induction W with
  | nil => rfl
  | cons a W ih => simp [h a (by simp),ih (fun b hb => h b (by simp [hb]))]

lemma gateCode_dst_zero (d : ℕ) {w : ℕ} (refs : Fin w → Option ℕ)
    (h : ∀ a i, refs a=some i → d≠i) (g : UniformReplayPrint.Gate r w) (v : ℕ) (hv : v≠d) :
    (gateCode d refs h g).countP (fun s => decide (s.dst=v))=0 := by
  apply countP_zero
  intro s hs
  have he := (gateCode_member _ _ _ g (fun _ => 0) s hs).1
  simp [he,hv.symm]

lemma natSweep_dst_count {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) (v : ℕ) :
    (natSweep p enabled).countP (fun s => decide (s.dst=v)) ≤ 2 := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep]
  | @step k p g ih =>
    rw [natSweep_step,List.countP_append]
    by_cases hv : v=n+1+k
    · have hz : (natSweep p enabled).countP (fun s => decide (s.dst=v))=0 := by
        apply countP_zero
        intro s hs
        have := (natSweep_bounds p enabled s hs).2.1
        apply decide_eq_false; omega
      rw [hz,Nat.zero_add]
      exact List.countP_le_length.trans (gateCode_length _ _ _ g)
    · rw [gateCode_dst_zero _ _ _ g v hv,Nat.add_zero]
      exact ih

lemma referenceMap_nat_nonzero {n k : ℕ} (enabled : Bool) (a : Fin (n+1+k)) (v : ℕ)
    (h : referenceMap enabled (fun i : Fin n => i.val) (fun j : Fin k => n+1+j.val) a=some v) : v≠n := by
  revert h
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · intro h
    revert h
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro h; simp [referenceMap] at h
    · intro h; cases enabled
      · simp [referenceMap] at h
      · have he : i.val=v := by simpa [referenceMap] using h
        have := i.isLt
        omega
  · intro h
    have he : n+1+j.val=v := by simpa [referenceMap] using h
    omega

lemma natSweep_src_nonzero {n k : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    ∀ s∈natSweep p enabled, s.src≠n := by
  induction p with
  | nil => simp [natSweep,UniformReplayPrint.Program.sweep]
  | @step k p g ih =>
    rw [natSweep_step]
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact ih s hs
    · obtain ⟨_,a,ha,_⟩ := gateCode_member _ _ _ g (runDepth p (fun _ => 0)) s hs
      exact referenceMap_nat_nonzero enabled a s.src ha

lemma natSweep_physical_src_count {n a : ℕ} (D : DAG r n a) (enabled : Bool) (v : ℕ) :
    (natSweep D.program enabled).countP (fun s => decide (s.src=v)) ≤ physicalUseCount D v := by
  by_cases hv : v=n
  · have hz : (natSweep D.program enabled).countP (fun s => decide (s.src=v))=0 := by
      apply countP_zero
      intro s hs
      simp [hv,natSweep_src_nonzero D.program enabled s hs]
    rw [hz]
    exact Nat.zero_le _
  · rw [physicalUseCount,ite_eq_right hv]
    exact (natSweep_src_count D.program enabled v).trans (Nat.le_add_right _ _)

lemma bucketsFrom_sublist (start count : ℕ) (level : ℕ → ℕ) (W : List (ShearCode ℕ r)) :
    ∀ V∈bucketsFrom start count level W, V.Sublist W := by
  induction count generalizing start W with
  | zero => simp [bucketsFrom]
  | succ c ih =>
    intro V hV
    simp only [bucketsFrom,List.mem_cons] at hV
    rcases hV with rfl|hV
    · exact List.filter_sublist
    · exact (ih (start+1) _ V hV).trans List.filter_sublist

/-- Actual occurrence counts give the maximum of input/output degree, even for
parallel reads. No duplicate operand or zero scalar coefficient is deleted. -/
lemma depthBuckets_degree {n a H delta : ℕ} (D : DAG r n a) (enabled : Bool)
    (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    ∀ W∈depthBuckets (natSweep D.program enabled) (natLevel D.program) H,
      DegreeBound (printedEdges W) delta := by
  intro W hW
  have hsub := bucketsFrom_sublist 0 (H+1) (natLevel D.program) _ W hW
  have hc (P : ShearCode ℕ r → Bool) : W.countP P≤(natSweep D.program enabled).countP P := by
    have h := hsub.countP_le (p := P)
    rw [(depthOrdered_perm _ _).countP_eq P] at h
    exact h
  obtain ⟨d,hd⟩ := depthBuckets_onLevel _ _ H (natSweep_depth D.program enabled) W hW
  apply degree_of_level W (natLevel D.program) hd
  · intro v
    change (Finset.univ.filter (fun i : Fin W.length => (W.get i).dst=v)).card ≤ delta
    rw [uses_card]
    exact (hc _).trans ((natSweep_dst_count D.program enabled v).trans hdelta)
  · intro v
    change (Finset.univ.filter (fun i : Fin W.length => (W.get i).src=v)).card ≤ delta
    rw [uses_card]
    exact (hc _).trans ((natSweep_physical_src_count D enabled v).trans (huse v))


noncomputable section

/-- No whole-action certificate is assumed: causality follows from the typed
program, and degree bounds refer only to actual per-level integer occurrences. -/
theorem layeredSweep_action {n a H delta : ℕ} (D : DAG r n a)
    (bank : Fin r → ℂ) (enabled : Bool) (hD : DepthBound D H) (hpos : 0<delta)
    (hdegree : ∀ W∈depthBuckets (natSweep D.program enabled) (natLevel D.program) H,
      DegreeBound (printedEdges W) delta) (v : ℕ → ℂ) :
    runShears ((layeredSweep D.program enabled H delta).flatten.map (ShearCode.eval bank)) v =
      runShears ((natSweep D.program enabled).map (ShearCode.eval bank)) v := by
  rw [layeredSweep,coloredBuckets_action bank _ delta hpos (by
    intro W hW
    obtain ⟨d,hd⟩ := depthBuckets_onLevel _ _ H (natSweep_depth D.program enabled) W hW
    exact ⟨hdegree W hW,hd.safe⟩),depthBuckets_flatten _ _ H (natSweep_depthBound D enabled hD)]
  exact sorted_natSweep_action D.program bank enabled v

end

/-- Each physical layer is a matching, including indexed parallel occurrences. -/
def Matching (W : List (ShearCode ℕ r)) : Prop :=
  W.Pairwise (fun s t => s.dst≠t.dst ∧ s.dst≠t.src ∧ s.src≠t.dst ∧ s.src≠t.src)

lemma colorBlocks_matching (W : List (ShearCode ℕ r)) (delta : ℕ)
    (hdegree : DegreeBound (printedEdges W) delta) (hpos : 0<delta) :
    ∀ V∈colorBlocks W delta, Matching V := by
  intro V hV
  obtain ⟨is,his,rfl⟩ := List.mem_map.mp hV
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp his
  apply List.pairwise_map.mpr
  apply (layer_nodup (printedEdges W) delta c).pairwise_of_forall_ne
  intro i hi j hj hne
  exact printed_matching W hdegree hpos c i j hi hj hne

lemma layeredSweep_matching {n a H delta : ℕ} (D : DAG r n a) (enabled : Bool)
    (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    ∀ V∈layeredSweep D.program enabled H delta, Matching V := by
  intro V hV
  obtain ⟨W,hW,hV⟩ := List.mem_flatMap.mp hV
  exact colorBlocks_matching W delta (depthBuckets_degree D enabled hdelta huse W hW)
    (by omega) V hV

lemma cross_layeredSweep_length (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) (enabled : Bool) :
    (layeredSweep (crossDAG k a e ha he).program enabled (8*k+6) 6).length = 11*(8*k+7) := by
  rw [layeredSweep_length]
  omega

noncomputable section

theorem cross_layeredSweep_action (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) (enabled : Bool)
    (bank : Fin (bankSize k) → ℂ) (v : ℕ → ℂ) :
    runShears ((layeredSweep (crossDAG k a e ha he).program enabled (8*k+6) 6).flatten.map
      (ShearCode.eval bank)) v =
      runShears ((natSweep (crossDAG k a e ha he).program enabled).map (ShearCode.eval bank)) v :=
  layeredSweep_action _ bank enabled (crossDAG_depth k a e ha he) (by omega)
    (depthBuckets_degree _ enabled (by omega) (crossDAG_physicalFanout k a e ha he)) v

end

/-- Explicit integer coordinate relabeling retains the printed coefficient reference. -/
def relabelCode {ι κ : Type} (e : ι ↪ κ) (s : ShearCode ι r) : ShearCode κ r :=
  ⟨e s.dst,e s.src,fun h => s.different (e.injective h),s.coefficient⟩

lemma relabelCode_inverse {ι κ : Type} (e : ι ↪ κ) (s : ShearCode ι r) :
    relabelCode e s.inverse = (relabelCode e s).inverse := rfl

lemma relabel_reverseCode {ι κ : Type} (e : ι ↪ κ) (W : List (ShearCode ι r)) :
    (reverseCode W).map (relabelCode e) = reverseCode (W.map (relabelCode e)) := by
  simp [reverseCode,List.map_map,Function.comp_def,relabelCode_inverse]

lemma relabel_reference {ι κ : Type} (e : ι ↪ κ) (d : ι) (ref : Option ι)
    (c : Coefficient r) (h : ∀ i, ref=some i → d≠i) :
    (reference d ref c h).map (relabelCode e) = reference (e d) (ref.map e) c
      (by intro j hj; obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp hj; exact fun he => h i hi (e.injective he)) := by
  cases ref <;> rfl

lemma relabel_gateCode {ι κ : Type} {w : ℕ} (e : ι ↪ κ) (d : ι)
    (refs : Fin w → Option ι) (h : ∀ a i, refs a=some i → d≠i) (g : UniformReplayPrint.Gate r w) :
    (gateCode d refs h g).map (relabelCode e) = gateCode (e d) (fun a => (refs a).map e)
      (by intro a j hj; obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp hj; exact fun he => h a i hi (e.injective he)) g := by
  cases g <;> simp only [gateCode,List.map_append,relabel_reference]

lemma referenceMap_relabel {ι κ : Type} {n k : ℕ} (e : ι ↪ κ) (enabled : Bool)
    (xs : Fin n → ι) (zs : Fin k → ι) (a : Fin (n+1+k)) :
    (referenceMap enabled xs zs a).map e = referenceMap enabled (e ∘ xs) (e ∘ zs) a := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [referenceMap]
    · cases enabled <;> simp [referenceMap]
  · simp [referenceMap]

lemma sweep_relabel {ι κ : Type} {n k : ℕ} (e : ι ↪ κ) (p : UniformReplayPrint.Program r n k)
    (enabled : Bool) (xs : Fin n → ι) (zs : Fin k → ι)
    (hz : Function.Injective zs) (hxz : ∀ i j, xs i≠zs j) :
    (p.sweep enabled xs zs hz hxz).map (relabelCode e) =
      p.sweep enabled (e ∘ xs) (e ∘ zs) (e.injective.comp hz)
        (fun i j h => hxz i j (e.injective h)) := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
    simp only [UniformReplayPrint.Program.sweep,List.map_append,relabel_gateCode]
    rw [ih]
    simp only [referenceMap_relabel]
    rfl

/-- Physical memory has an unused zero-port hole; output accumulators follow all gates. -/
def replayEmbedding (n k a : ℕ) : ((Fin n ⊕ Fin k) ⊕ Fin a) ↪ ℕ where
  toFun := Sum.elim (Sum.elim (fun i => i.val) (fun j => n+1+j.val)) (fun j => n+1+k+j.val)
  inj' := by
    intro i j h
    rcases i with (i|i)|i
    · rcases j with (j|j)|j
      · exact congrArg Sum.inl (congrArg Sum.inl (Fin.ext h))
      · dsimp at h; have := i.isLt; have := j.isLt; omega
      · dsimp at h; have := i.isLt; have := j.isLt; omega
    · rcases j with (j|j)|j
      · dsimp at h; have := i.isLt; have := j.isLt; omega
      · apply congrArg Sum.inl; apply congrArg Sum.inr; apply Fin.ext
        dsimp at h; omega
      · dsimp at h; have := i.isLt; have := j.isLt; omega
    · rcases j with (j|j)|j
      · dsimp at h; have := i.isLt; have := j.isLt; omega
      · dsimp at h; have := i.isLt; have := j.isLt; omega
      · apply congrArg Sum.inr; apply Fin.ext; dsimp at h; omega

noncomputable section

lemma relabel_act {ι κ : Type} (e : ι ↪ κ) (bank : Fin r → ℂ) (s : ShearCode ι r) (v : κ → ℂ) :
    ((relabelCode e s).eval bank).act v ∘ e = (s.eval bank).act (v ∘ e) := by
  classical
  funext i
  simp only [Shear.act,ShearCode.eval,relabelCode,Function.comp_apply,e.injective.eq_iff]
  by_cases h : i=s.dst <;> simp [h]

lemma relabel_run {ι κ : Type} (e : ι ↪ κ) (bank : Fin r → ℂ) (W : List (ShearCode ι r))
    (v : κ → ℂ) :
    runShears ((W.map (relabelCode e)).map (ShearCode.eval bank)) v ∘ e =
      runShears (W.map (ShearCode.eval bank)) (v ∘ e) := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
    simp only [List.map_cons,runShears_cons]
    rw [ih,relabel_act]

end


lemma Coefficient.negate_negate (c : Coefficient r) : c.negate.negate=c := by
  cases c with
  | rational q => simp [Coefficient.negate]
  | prepared i b => cases b <;> rfl

lemma inverse_inverse {ι : Type} (s : ShearCode ι r) : s.inverse.inverse=s := by
  cases s
  simp [ShearCode.inverse,Coefficient.negate_negate]

lemma reverseCode_reverse {ι : Type} (W : List (ShearCode ι r)) : reverseCode (reverseCode W)=W := by
  simp [reverseCode,List.map_reverse,List.map_map,Function.comp_def,inverse_inverse]

noncomputable section

lemma reverseCode_run_right {ι : Type} (bank : Fin r → ℂ) (W : List (ShearCode ι r)) (v : ι → ℂ) :
    runShears (W.map (ShearCode.eval bank))
      (runShears ((reverseCode W).map (ShearCode.eval bank)) v)=v := by
  have h := runShears_reverse ((reverseCode W).map (ShearCode.eval bank)) v
  rw [← reverseCode_eval,reverseCode_reverse] at h
  exact h

lemma reverseCode_action_congr {ι : Type} (bank : Fin r → ℂ) (W V : List (ShearCode ι r))
    (h : ∀ v, runShears (W.map (ShearCode.eval bank)) v=runShears (V.map (ShearCode.eval bank)) v)
    (v : ι → ℂ) :
    runShears ((reverseCode W).map (ShearCode.eval bank)) v =
      runShears ((reverseCode V).map (ShearCode.eval bank)) v := by
  have hr := runShears_reverse (V.map (ShearCode.eval bank))
    (runShears ((reverseCode W).map (ShearCode.eval bank)) v)
  rw [← reverseCode_eval,← h,reverseCode_run_right] at hr
  exact hr.symm

end

def memoryEmbedding (n k a : ℕ) : (Fin n ⊕ Fin k) ↪ ℕ :=
  Function.Embedding.inl.trans (replayEmbedding n k a)

lemma natSweep_from_memory {n k a : ℕ} (p : UniformReplayPrint.Program r n k) (enabled : Bool) :
    ((p.memorySweep enabled).map (fun s => s.sumInl (κ := Fin a))).map
      (relabelCode (replayEmbedding n k a)) = natSweep p enabled := by
  simp only [List.map_map]
  change (p.memorySweep enabled).map (relabelCode (memoryEmbedding n k a)) = _
  exact sweep_relabel (memoryEmbedding n k a) p enabled Sum.inl Sum.inr
    (fun _ _ h => Sum.inr.inj h) (by intros; simp)

/-- The actual integer output table, with no scalar-value branch. -/
def natBroadcast {n a : ℕ} (D : DAG r n a) (enabled : Bool) : List (ShearCode ℕ r) :=
  (List.finRange a).flatMap (fun j => reference (n+1+D.size+j.val)
    (referenceMap enabled (fun i : Fin n => i.val) (fun i : Fin D.size => n+1+i.val) (D.outputs j))
    (.rational 1) (by
      intro src hs
      have hv := referenceMap_nat_some enabled (D.outputs j) src hs
      have := (D.outputs j).isLt
      omega))

lemma natReference_as_map {n k a : ℕ} (enabled : Bool) (j : Fin (n+1+k)) :
    referenceMap enabled (fun i : Fin n => i.val) (fun i : Fin k => n+1+i.val) j =
      (referenceMap enabled (Sum.inl : Fin n → Fin n ⊕ Fin k) Sum.inr j).map (memoryEmbedding n k a) := by
  rw [referenceMap_relabel]
  rfl

lemma relabel_output_reference {ι : Type} {a : ℕ} (e : (ι ⊕ Fin a) ↪ ℕ)
    (ref : Option ι) (j : Fin a) :
    ((match ref with
      | none => []
      | some src => [⟨Sum.inr j,Sum.inl src,(by intro h; cases h),.rational 1⟩]) :
      List (ShearCode (ι ⊕ Fin a) r)).map (relabelCode e) =
    reference (e (Sum.inr j)) (ref.map (fun i => e (Sum.inl i))) (.rational 1)
      (by intro dst hd
          obtain ⟨src,_,rfl⟩ := Option.map_eq_some_iff.mp hd
          intro h
          have he := e.injective h
          cases he) := by
  cases ref <;> rfl

lemma natBroadcast_from_output {n a : ℕ} (D : DAG r n a) (enabled : Bool) :
    (broadcast (r := r) (fun j => referenceMap enabled
      (Sum.inl : Fin n → Fin n ⊕ Fin D.size) Sum.inr (D.outputs j))).map
        (relabelCode (replayEmbedding n D.size a)) = natBroadcast D enabled := by
  have ho (j : Fin a) :
      (broadcastOne (r := r) (fun j => referenceMap enabled
        (Sum.inl : Fin n → Fin n ⊕ Fin D.size) Sum.inr (D.outputs j)) j).map
          (relabelCode (replayEmbedding n D.size a)) =
      reference (n+1+D.size+j.val)
        (referenceMap enabled (fun i : Fin n => i.val) (fun i : Fin D.size => n+1+i.val) (D.outputs j))
        (.rational 1) (by
          intro src hs
          have hv := referenceMap_nat_some enabled (D.outputs j) src hs
          have := (D.outputs j).isLt; omega) := by
    simp only [natReference_as_map (a := a)]
    exact relabel_output_reference (replayEmbedding n D.size a)
      (referenceMap enabled (Sum.inl : Fin n → Fin n ⊕ Fin D.size) Sum.inr (D.outputs j)) j
  unfold broadcast natBroadcast
  generalize List.finRange a = L
  induction L with
  | nil => rfl
  | cons j L ih => simp only [broadcastList,List.map_append,List.flatMap_cons,ho,ih]

/-- This tape is literally the previously verified dirty replay in fixed integer ports. -/
def natReplayCode {n a : ℕ} (D : DAG r n a) : List (ShearCode ℕ r) :=
  (replayCode D.program D.outputs).map (relabelCode (replayEmbedding n D.size a))

lemma natReplayCode_phases {n a : ℕ} (D : DAG r n a) :
    natReplayCode D = natSweep D.program true ++ natBroadcast D true ++ reverseCode (natSweep D.program true) ++
      natSweep D.program false ++ reverseCode (natBroadcast D false) ++ reverseCode (natSweep D.program false) := by
  unfold natReplayCode replayCode
  simp only [List.map_append,relabel_reverseCode,natSweep_from_memory,natBroadcast_from_output]

/-- Reverse layers reverse their order and negate each prepared coefficient reference. -/
def reverseLayers (L : List (List (ShearCode ℕ r))) : List (List (ShearCode ℕ r)) :=
  L.reverse.map reverseCode

lemma reverseLayers_flatten (L : List (List (ShearCode ℕ r))) :
    (reverseLayers L).flatten = reverseCode L.flatten := by
  have h : (reverseCode : List (ShearCode ℕ r) → List (ShearCode ℕ r)) =
      fun x => (x.map ShearCode.inverse).reverse := by
    funext x
    simp [reverseCode]
  simp [reverseLayers,reverseCode,List.reverse_flatten,List.map_flatten,List.map_map,Function.comp_def]
  rw [h]

lemma reverseLayers_length (L : List (List (ShearCode ℕ r))) : (reverseLayers L).length=L.length := by
  simp [reverseLayers]

def replayLayers {n a : ℕ} (D : DAG r n a) (H delta : ℕ) : List (List (ShearCode ℕ r)) :=
  let W := layeredSweep D.program true H delta
  let V := layeredSweep D.program false H delta
  let B := colorBlocks (natBroadcast D true) delta
  let Z := colorBlocks (natBroadcast D false) delta
  W ++ B ++ reverseLayers W ++ V ++ reverseLayers Z ++ reverseLayers V

lemma replayLayers_length {n a : ℕ} (D : DAG r n a) (H delta : ℕ) :
    (replayLayers D H delta).length = (4*(H+1)+2)*(2*delta-1) := by
  simp only [replayLayers,List.length_append,reverseLayers_length,layeredSweep_length,colorBlocks_length]
  ring

lemma reference_dst_count (d : ℕ) (ref : Option ℕ) (c : Coefficient r)
    (h : ∀ i, ref=some i → d≠i) (v : ℕ) :
    (reference d ref c h).countP (fun s => decide (s.dst=v)) ≤ (if d=v then 1 else 0) := by
  cases ref <;> simp [reference]

lemma natBroadcast_avoid {n a : ℕ} (D : DAG r n a) (enabled : Bool) (j : Fin a) :
    ∀ src, referenceMap enabled (fun i : Fin n => i.val) (fun i : Fin D.size => n+1+i.val)
      (D.outputs j)=some src → n+1+D.size+j.val≠src := by
  intro src hs
  have hv := referenceMap_nat_some enabled (D.outputs j) src hs
  have := (D.outputs j).isLt
  omega

lemma natBroadcast_src_count {n a : ℕ} (D : DAG r n a) (enabled : Bool) (v : ℕ) :
    (natBroadcast D enabled).countP (fun s => decide (s.src=v)) ≤ (outputRefs D).count v := by
  unfold natBroadcast outputRefs
  generalize List.finRange a = L
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.flatMap_cons,List.countP_append,List.map_cons,List.count_cons]
    have h := reference_src_count (r := r) (n+1+D.size+j.val) _ (.rational 1)
      (natBroadcast_avoid D enabled j) (D.outputs j).val v
      (fun b hb => referenceMap_nat_some enabled (D.outputs j) b hb)
    simp only [beq_iff_eq]
    omega

lemma natBroadcast_dst_count {n a : ℕ} (D : DAG r n a) (enabled : Bool) (v : ℕ) :
    (natBroadcast D enabled).countP (fun s => decide (s.dst=v)) ≤ 1 := by
  have hc : (natBroadcast D enabled).countP (fun s => decide (s.dst=v)) ≤ (nodePorts n D.size a).count v := by
    unfold natBroadcast nodePorts
    generalize List.finRange a = L
    induction L with
    | nil => rfl
    | cons j L ih =>
      simp only [List.flatMap_cons,List.countP_append,List.map_cons,List.count_cons]
      have h := reference_dst_count (r := r) (n+1+D.size+j.val) _ (.rational 1)
        (natBroadcast_avoid D enabled j) v
      simp only [beq_iff_eq]
      omega
  exact hc.trans (nodePorts_count n D.size a v)

lemma natBroadcast_bounds {n a : ℕ} (D : DAG r n a) (enabled : Bool) :
    ∀ s∈natBroadcast D enabled,
      n+1+D.size ≤ s.dst ∧ s.dst<n+1+D.size+a ∧ s.src<n+1+D.size ∧ s.src≠n := by
  intro s hs
  obtain ⟨j,_,hs⟩ := List.mem_flatMap.mp hs
  have he := reference_member _ _ _ _ s hs
  have hv := referenceMap_nat_some enabled (D.outputs j) s.src he.2
  have hn := referenceMap_nat_nonzero enabled (D.outputs j) s.src he.2
  rw [he.1,hv]
  have := j.isLt; have := (D.outputs j).isLt
  exact ⟨by omega,by omega,by omega,by simpa only [← hv] using hn⟩

lemma natBroadcast_onLevel {n a : ℕ} (D : DAG r n a) (enabled : Bool) :
    OnLevel (natBroadcast D enabled) (fun v => if v<n+1+D.size then 0 else 1) 1 := by
  intro s hs
  have hb := natBroadcast_bounds D enabled s hs
  simp [Nat.not_lt_of_ge hb.1,hb.2.2.1]

lemma natBroadcast_physical_src_count {n a : ℕ} (D : DAG r n a) (enabled : Bool) (v : ℕ) :
    (natBroadcast D enabled).countP (fun s => decide (s.src=v)) ≤ physicalUseCount D v := by
  by_cases hv : v=n
  · rw [countP_zero _ _ (fun s hs => by
      have := (natBroadcast_bounds D enabled s hs).2.2.2
      simp [hv,this])]
    exact Nat.zero_le _
  · rw [physicalUseCount,ite_eq_right hv]
    exact (natBroadcast_src_count D enabled v).trans (Nat.le_add_left _ _)

lemma natBroadcast_degree {n a delta : ℕ} (D : DAG r n a) (enabled : Bool)
    (hpos : 0<delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    DegreeBound (printedEdges (natBroadcast D enabled)) delta := by
  apply degree_of_level _ _ (natBroadcast_onLevel D enabled)
  · intro v
    change (Finset.univ.filter (fun i : Fin (natBroadcast D enabled).length =>
      ((natBroadcast D enabled).get i).dst=v)).card ≤ delta
    rw [uses_card]
    exact (natBroadcast_dst_count D enabled v).trans (by omega)
  · intro v
    change (Finset.univ.filter (fun i : Fin (natBroadcast D enabled).length =>
      ((natBroadcast D enabled).get i).src=v)).card ≤ delta
    rw [uses_card]
    exact (natBroadcast_physical_src_count D enabled v).trans (huse v)

lemma Matching.reverseCode {W : List (ShearCode ℕ r)} (hW : Matching W) : Matching (reverseCode W) := by
  unfold Matching UniformReplayPrint.reverseCode
  apply List.pairwise_map.mpr
  change W.reverse.Pairwise (fun s t => s.dst≠t.dst ∧ s.dst≠t.src ∧ s.src≠t.dst ∧ s.src≠t.src)
  rw [List.pairwise_reverse]
  exact hW.imp (fun h => ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩)

lemma reverseLayers_matching (L : List (List (ShearCode ℕ r))) (hL : ∀ W∈L, Matching W) :
    ∀ W∈reverseLayers L, Matching W := by
  intro W hW
  obtain ⟨V,hV,rfl⟩ := List.mem_map.mp hW
  exact (hL V (List.mem_reverse.mp hV)).reverseCode

lemma replayLayers_matching {n a H delta : ℕ} (D : DAG r n a)
    (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    ∀ W∈replayLayers D H delta, Matching W := by
  have hs (enabled : Bool) := layeredSweep_matching (H := H) D enabled hdelta huse
  have hb (enabled : Bool) := colorBlocks_matching (natBroadcast D enabled) delta
    (natBroadcast_degree D enabled (by omega) huse) (by omega)
  intro W hW
  simp only [replayLayers,List.mem_append] at hW
  rcases hW with ((((h|h)|h)|h)|h)|h
  · exact hs true W h
  · exact hb true W h
  · exact reverseLayers_matching _ (hs true) W h
  · exact hs false W h
  · exact reverseLayers_matching _ (hb false) W h
  · exact reverseLayers_matching _ (hs false) W h

noncomputable section

/-- Literal colored forward/reverse sweeps and colored output rounds preserve
all dirty replay inputs; all hypotheses concern the actual DAG geometry. -/
theorem replayLayers_action {n a H delta : ℕ} (D : DAG r n a) (bank : Fin r → ℂ)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta)
    (v : ℕ → ℂ) :
    runShears ((replayLayers D H delta).flatten.map (ShearCode.eval bank)) v =
      runShears ((natReplayCode D).map (ShearCode.eval bank)) v := by
  have hs (enabled : Bool) := layeredSweep_action D bank enabled hD (by omega)
    (depthBuckets_degree D enabled hdelta huse)
  have hb (enabled : Bool) := colorOrdered_action bank (natBroadcast D enabled)
    (natBroadcast_degree D enabled (by omega) huse) (by omega) (natBroadcast_onLevel D enabled).safe
  have hrs (enabled : Bool) := reverseCode_action_congr bank
    (layeredSweep D.program enabled H delta).flatten (natSweep D.program enabled) (hs enabled)
  have hrb (enabled : Bool) := reverseCode_action_congr bank
    (colorOrdered (natBroadcast D enabled) delta) (natBroadcast D enabled) (hb enabled)
  rw [natReplayCode_phases]
  simp only [replayLayers,List.flatten_append,reverseLayers_flatten,colorBlocks_flatten,
    List.map_append,runShears_append]
  rw [hs true,hb true,hrs true,hs false,hrb false,hrs false]

/-- Exact dirty replay semantics at all packed input/gate/output coordinates.
The unused zero-port hole and any other external coordinates are not inputs. -/
theorem natReplayCode_spec {n a : ℕ} (D : DAG r n a) (bank : Fin r → ℂ) (v : ℕ → ℂ) :
    runShears ((natReplayCode D).map (ShearCode.eval bank)) v ∘ replayEmbedding n D.size a =
      Sum.elim (Sum.elim (fun i : Fin n => v i.val) (fun j : Fin D.size => v (n+1+j.val)))
        (fun j : Fin a => v (n+1+D.size+j.val) +
          (D.program.eval bank).eval (fun i => v i.val) (D.outputs j)) := by
  rw [natReplayCode,relabel_run]
  have hv : v ∘ replayEmbedding n D.size a =
      Sum.elim (Sum.elim (fun i : Fin n => v i.val) (fun j : Fin D.size => v (n+1+j.val)))
        (fun j : Fin a => v (n+1+D.size+j.val)) := by
    funext q
    rcases q with (i|i)|i <;> rfl
  rw [hv,replayCode_spec]

theorem cross_replayLayers_spec (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) (bank : Fin (bankSize k) → ℂ) (v : ℕ → ℂ) :
    runShears ((replayLayers (crossDAG k a e ha he) (8*k+6) 6).flatten.map (ShearCode.eval bank)) v ∘
        replayEmbedding e (crossDAG k a e ha he).size a =
      Sum.elim (Sum.elim (fun i : Fin e => v i.val)
        (fun j : Fin (crossDAG k a e ha he).size => v (e+1+j.val)))
        (fun j : Fin a => v (e+1+(crossDAG k a e ha he).size+j.val) +
          ((crossDAG k a e ha he).program.eval bank).eval (fun i => v i.val)
            ((crossDAG k a e ha he).outputs j)) := by
  rw [replayLayers_action _ bank (crossDAG_depth k a e ha he) (by omega)
    (crossDAG_physicalFanout k a e ha he),natReplayCode_spec]

end

lemma cross_replayLayers_length (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) :
    (replayLayers (crossDAG k a e ha he) (8*k+6) 6).length ≤ 66*(8*k+7) := by
  rw [replayLayers_length]
  omega

lemma cross_replayLayers_matching (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) :
    ∀ W∈replayLayers (crossDAG k a e ha he) (8*k+6) 6, Matching W :=
  replayLayers_matching _ (by omega) (crossDAG_physicalFanout k a e ha he)

lemma coloredBuckets_perm (B : List (List (ShearCode ℕ r))) (delta : ℕ) (hpos : 0<delta)
    (hdegree : ∀ W∈B, DegreeBound (printedEdges W) delta) :
    (coloredBuckets B delta).flatten.Perm B.flatten := by
  induction B with
  | nil => exact List.Perm.refl _
  | cons W B ih =>
    simp only [coloredBuckets,List.flatMap_cons,List.flatten_append,List.flatten_cons,colorBlocks_flatten]
    exact (colorOrdered_perm W (hdegree W (by simp)) hpos).append
      (ih (fun V hV => hdegree V (by simp [hV])))

lemma layeredSweep_perm {n a H delta : ℕ} (D : DAG r n a) (enabled : Bool)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    (layeredSweep D.program enabled H delta).flatten.Perm (natSweep D.program enabled) := by
  have h := coloredBuckets_perm (depthBuckets (natSweep D.program enabled) (natLevel D.program) H)
    delta (by omega) (depthBuckets_degree D enabled hdelta huse)
  rw [depthBuckets_flatten _ _ H (natSweep_depthBound D enabled hD)] at h
  exact h.trans (depthOrdered_perm _ _)

lemma reverseCode_perm {ι : Type} {W V : List (ShearCode ι r)} (h : W.Perm V) :
    (reverseCode W).Perm (reverseCode V) :=
  (((List.reverse_perm W).trans h).trans (List.reverse_perm V).symm).map ShearCode.inverse

/-- All original indexed instructions survive the complete layer compiler. -/
theorem replayLayers_perm {n a H delta : ℕ} (D : DAG r n a)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    (replayLayers D H delta).flatten.Perm (natReplayCode D) := by
  have hs (enabled : Bool) := layeredSweep_perm D enabled hD hdelta huse
  have hb (enabled : Bool) := colorOrdered_perm (natBroadcast D enabled)
    (natBroadcast_degree D enabled (by omega) huse) (by omega)
  rw [natReplayCode_phases]
  simp only [replayLayers,List.flatten_append,reverseLayers_flatten,colorBlocks_flatten]
  exact (((((hs true).append (hb true)).append (reverseCode_perm (hs true))).append
    (hs false)).append (reverseCode_perm (hb false))).append (reverseCode_perm (hs false))

theorem replayLayers_instruction_count {n a H delta : ℕ} (D : DAG r n a)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    (replayLayers D H delta).flatten.length = (replayCode D.program D.outputs).length := by
  have h := (replayLayers_perm D hD hdelta huse).length_eq
  simpa only [natReplayCode,List.length_map] using h

lemma cross_replayLayers_instruction_count (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
    (he : e≤UniformRadixTwoDAG.width k) :
    (replayLayers (crossDAG k a e ha he) (8*k+6) 6).flatten.length = (crossReplay k a e ha he).length :=
  replayLayers_instruction_count _ (crossDAG_depth k a e ha he) (by omega)
    (crossDAG_physicalFanout k a e ha he)

noncomputable section

/-- Closed rank-three cross action, with the actual displacement recurrence
and the actual shared prepared bank. Dirty input and gate ports are restored. -/
theorem cross_replayLayers_matrix (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k) (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ)
    (hrec : ∀ i j, i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1))
    (X : ℕ → ℂ) :
    runShears ((replayLayers (crossDAG k a e (by omega) (by omega)) (8*k+6) 6).flatten.map
        (ShearCode.eval (sharedBank k (rankKernels k a e M v w)))) X ∘
        replayEmbedding e (crossDAG k a e (by omega) (by omega)).size a =
      Sum.elim (Sum.elim (fun i : Fin e => X i.val)
        (fun j : Fin (crossDAG k a e (by omega) (by omega)).size => X (e+1+j.val)))
        (fun j : Fin a => X (e+1+(crossDAG k a e (by omega) (by omega)).size+j.val) +
          Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (fun i => X i.val) j) := by
  rw [cross_replayLayers_spec]
  have h := crossDAG_eval k a e ha he hsize M v w hrec (fun i => X i.val)
  exact congrArg (fun o : Fin a → ℂ =>
    Sum.elim (Sum.elim (fun i : Fin e => X i.val)
      (fun j : Fin (crossDAG k a e (by omega) (by omega)).size => X (e+1+j.val)))
      (fun j => X (e+1+(crossDAG k a e (by omega) (by omega)).size+j.val)+o j)) h

end

lemma replayEmbedding_bound (n k a : ℕ) (i : (Fin n ⊕ Fin k) ⊕ Fin a) :
    replayEmbedding n k a i < n+1+k+a := by
  rcases i with (i|i)|i
  · change i.val < n+1+k+a
    have := i.isLt; omega
  · change n+1+i.val < n+1+k+a
    have := i.isLt; omega
  · change n+1+k+i.val < n+1+k+a
    have := i.isLt; omega

lemma natReplayCode_bounds {n a : ℕ} (D : DAG r n a) :
    ∀ s∈natReplayCode D, s.dst<n+1+D.size+a ∧ s.src<n+1+D.size+a := by
  intro s hs
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hs
  exact ⟨replayEmbedding_bound _ _ _ t.dst,replayEmbedding_bound _ _ _ t.src⟩

lemma replayLayers_bounds {n a H delta : ℕ} (D : DAG r n a)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta) :
    ∀ s∈(replayLayers D H delta).flatten, s.dst<n+1+D.size+a ∧ s.src<n+1+D.size+a := by
  intro s hs
  exact natReplayCode_bounds D s ((replayLayers_perm D hD hdelta huse).mem_iff.mp hs)

noncomputable section

lemma relabel_run_outside {ι : Type} (e : ι ↪ ℕ) (bank : Fin r → ℂ) (W : List (ShearCode ι r))
    (v : ℕ → ℂ) (q : ℕ) (hq : ∀ i, q≠e i) :
    runShears ((W.map (relabelCode e)).map (ShearCode.eval bank)) v q=v q := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
    simp only [List.map_cons,runShears_cons]
    rw [ih]
    exact Shear.act_other _ _ (hq s.dst)

theorem replayLayers_outside {n a H delta : ℕ} (D : DAG r n a) (bank : Fin r → ℂ)
    (hD : DepthBound D H) (hdelta : 2≤delta) (huse : ∀ v, physicalUseCount D v≤delta)
    (v : ℕ → ℂ) (q : ℕ) (hq : ∀ i, q≠replayEmbedding n D.size a i) :
    runShears ((replayLayers D H delta).flatten.map (ShearCode.eval bank)) v q=v q := by
  rw [replayLayers_action D bank hD hdelta huse]
  exact relabel_run_outside _ bank _ v q hq

/-- The paper's Toeplitz-cross recurrence supplies the rank-three action; no
matrix-action certificate is assumed. Preparation remains a separate phase. -/
theorem toeplitz_replayLayers_matrix (k s a e i₀ j₀ : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k) (h g : ℕ → ℂ) (hi : s ≤ i₀) (hj : j₀+e ≤ s)
    (X : ℕ → ℂ) :
    let M := fun i j => OAI.ExactFourier.ToeplitzLayers.cross s h g (i₀+i) (j₀+j)
    let v := fun i => -h (i₀+i-s)
    let w := fun j => g (s-(j₀+j))
    runShears ((replayLayers (crossDAG k a e (by omega) (by omega)) (8*k+6) 6).flatten.map
        (ShearCode.eval (sharedBank k (rankKernels k a e M v w)))) X ∘
        replayEmbedding e (crossDAG k a e (by omega) (by omega)).size a =
      Sum.elim (Sum.elim (fun i : Fin e => X i.val)
        (fun j : Fin (crossDAG k a e (by omega) (by omega)).size => X (e+1+j.val)))
        (fun j : Fin a => X (e+1+(crossDAG k a e (by omega) (by omega)).size+j.val) +
          Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (fun i => X i.val) j) := by
  dsimp only
  exact cross_replayLayers_matrix k a e ha he hsize _ _ _
    (OAI.ExactFourier.ToeplitzLayers.cross_interior s a e i₀ j₀ h g hi hj) X

end

end ExactFourierCircuits.UniformDAGLayers
