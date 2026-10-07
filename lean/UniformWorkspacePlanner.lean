import UniformToeplitzCrossDAG
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

namespace ExactFourierCircuits.UniformWorkspacePlanner

/-- Minimal no-alias power-of-two exponent for the printed cross topology. -/
def exponent (a e : ℕ) : ℕ := Nat.clog 2 (2*(a+e))

def gateCount (a e : ℕ) : ℕ :=
  6*UniformConvolutionDAG.total (exponent a e)+2*a

def chunkCount (s b : ℕ) : ℕ := (s+b-1)/b
def chunkSizes (s b : ℕ) : List ℕ :=
  (List.range (chunkCount s b)).map (fun j => min b (s-j*b))

def allFits (v b : ℕ) : Bool :=
  (chunkSizes (v-v/2) b).all fun a =>
    (chunkSizes (v/2) b).all fun e => decide (gateCount a e+a+e≤ v)

def candidates (v : ℕ) : Finset ℕ :=
  (Finset.range (v+1)).filter fun b => 0<b ∧ allFits v b=true

/-- The search uses only printed integer topology counts. Zero selects fallback. -/
def selected (v : ℕ) : ℕ := (candidates v).sup id

theorem chunkSizes_length (s b : ℕ) : (chunkSizes s b).length=chunkCount s b := by
  simp [chunkSizes]

theorem chunk_le {s b a : ℕ} (ha : a∈chunkSizes s b) : a≤ b := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
  exact min_le_left _ _

theorem chunk_pos {s b a : ℕ} (hb : 0<b) (ha : a∈chunkSizes s b) : 0<a := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  have hjb : (j+1)*b≤ s+b-1 := Nat.mul_le_of_le_div b (j+1) (s+b-1) (by
    exact Nat.succ_le_of_lt (List.mem_range.mp hj))
  rw [Nat.add_mul,Nat.one_mul] at hjb
  have hsub : s+b-1+1=s+b := Nat.sub_add_cancel (by omega)
  have hjlt : j*b<s := by omega
  exact lt_min hb (by omega)

theorem no_alias (a e : ℕ) : 2*(a+e)≤2^exponent a e :=
  Nat.le_pow_clog (by decide) _

theorem gateCount_eq (a e : ℕ) :
    gateCount a e=6*(3*exponent a e*2^exponent a e+2*2^exponent a e)+2*a := by
  have h := (UniformConvolutionDAG.records_length (exponent a e)).symm.trans
    (UniformConvolutionDAG.gate_count (exponent a e))
  rw [gateCount,h]

def printedCross (a e : ℕ) :=
  UniformToeplitzCrossDAG.crossDAG (exponent a e) a e
    (by rw [UniformRadixTwoDAG.width_eq];have h:=no_alias a e;omega)
    (by rw [UniformRadixTwoDAG.width_eq];have h:=no_alias a e;omega)

theorem printedCross_size (a e : ℕ) : (printedCross a e).size=gateCount a e := by
  rw [gateCount_eq]
  exact UniformToeplitzCrossDAG.crossDAG_size _ _ _ _ _

theorem printedCross_depth (a e : ℕ) :
    UniformToeplitzCrossDAG.DepthBound (printedCross a e) (8*exponent a e+6) :=
  UniformToeplitzCrossDAG.crossDAG_depth _ _ _ _ _

theorem printedCross_fanout (a e port : ℕ) :
    UniformToeplitzCrossDAG.physicalUseCount (printedCross a e) port≤6 :=
  UniformToeplitzCrossDAG.crossDAG_physicalFanout _ _ _ _ _ _

theorem gateCount_one : gateCount 1 1=194 := by
  have h : exponent 1 1=2 := Nat.clog_pow 2 2 (by decide)
  rw [gateCount_eq,h]
  norm_num

theorem selected_le (v : ℕ) : selected v≤ v := by
  apply Finset.sup_le
  intro b hb
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  exact Nat.le_of_lt_succ h

theorem candidate_le_selected {v b : ℕ} (hb : b∈candidates v) : b≤ selected v :=
  Finset.le_sup (f:=id) hb

theorem selected_candidate {v : ℕ} (hv : 0<selected v) : selected v∈candidates v := by
  have hne : (candidates v).Nonempty := by
    by_contra h
    have he : candidates v=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [selected,he] at hv
  have h := Finset.sup_mem_of_nonempty (f:=id) hne
  simpa only [selected,Set.image_id,Finset.mem_coe] using h

theorem selected_fit {v : ℕ} (hv : 0<selected v)
    {a e : ℕ} (ha : a∈chunkSizes (v-v/2) (selected v))
    (he : e∈chunkSizes (v/2) (selected v)) : gateCount a e+a+e≤ v := by
  have h := (Finset.mem_filter.mp (selected_candidate hv)).2.2
  simp only [allFits,List.all_eq_true,decide_eq_true_eq] at h
  exact h a ha e he

theorem exponent_bound {v a e : ℕ} (ha : a≤ v) (he : e≤ v) :
    exponent a e≤ Nat.clog 2 v+2 := by
  apply Nat.clog_le_of_le_pow
  have hv := Nat.le_pow_clog (by decide : 1<2) v
  rw [pow_add]
  norm_num
  omega

theorem width_bound {a e : ℕ} (hs : 0<a+e) : 2^exponent a e≤4*(a+e) := by
  have h := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<2*(a+e) by omega)
  simp only [Nat.pred_eq_sub_one] at h
  have hp := Nat.clog_pos (by decide : 1<2) (show 1<2*(a+e) by omega)
  have heq : exponent a e=(exponent a e-1)+1 := by dsimp [exponent];omega
  rw [heq,pow_succ]
  change 2^(Nat.clog 2 (2*(a+e))-1)*2≤4*(a+e)
  nlinarith

def denominator (v : ℕ) : ℕ := 1024*(Nat.clog 2 v+1)
def sufficient (v : ℕ) : ℕ := v/denominator v

theorem denominator_pos (v : ℕ) : 0<denominator v := by dsimp [denominator];positivity

theorem sufficient_le (v : ℕ) : sufficient v≤ v := Nat.div_le_self _ _

theorem small_pair_fit {v b a e : ℕ} (hb : b≤ sufficient v) (ha : a≤ b) (he : e≤ b)
    (hs : 0<a+e) : gateCount a e+a+e≤ v := by
  have hmul : b*denominator v≤ v :=
    (Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self _ _)
  have hbv := hb.trans (sufficient_le v)
  have hk := exponent_bound (ha.trans hbv) (he.trans hbv)
  have hw := width_bound hs
  have hN : 2^exponent a e≤8*b := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hk) hN
  have hsmall : gateCount a e+a+e≤ b*denominator v := by
    rw [gateCount_eq]
    dsimp [denominator]
    nlinarith
  exact hsmall.trans hmul

theorem sufficient_candidate {v : ℕ} (hv : 0<sufficient v) : sufficient v∈candidates v := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have h:=sufficient_le v;omega),hv,?_⟩
  simp only [allFits,List.all_eq_true,decide_eq_true_eq]
  intro a ha e he
  exact small_pair_fit (le_refl _) (chunk_le ha) (chunk_le he)
    (by have h:=chunk_pos hv ha;omega)

theorem selected_ge_sufficient (v : ℕ) : sufficient v≤ selected v := by
  by_cases h : 0<sufficient v
  · exact candidate_le_selected (sufficient_candidate h)
  · omega

theorem unit_candidate {v : ℕ} (hv : 196≤ v) : 1∈candidates v := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by decide,?_⟩
  simp only [allFits,List.all_eq_true,decide_eq_true_eq]
  intro a ha e he
  have ha1 : a=1 := by have := chunk_pos (by decide : 0<1) ha;have := chunk_le ha;omega
  have he1 : e=1 := by have := chunk_pos (by decide : 0<1) he;have := chunk_le he;omega
  rw [ha1,he1,gateCount_one]
  omega

theorem fallback_below_196 {v : ℕ} (hv : selected v=0) : v<196 := by
  by_contra h
  have hsel := candidate_le_selected (unit_candidate (by omega : 196≤ v))
  omega

theorem power_dominates (k : ℕ) (hk : 16≤ k) : 2048*(k+2)≤2^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

/-- An explicit absolute threshold; the direct fallback cannot occur above it. -/
theorem sufficient_large {v : ℕ} (hv : 2^17≤ v) : 2*denominator v≤ v := by
  have hk : 17≤ Nat.clog 2 v := by
    have h := Nat.clog_mono_right 2 hv
    simpa only [Nat.clog_pow 2 17 (by decide)] using h
  have hpow := power_dominates (Nat.clog 2 v-1) (by omega)
  have hlow := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<v by norm_num at hv;omega)
  simp only [Nat.pred_eq_sub_one] at hlow
  have he : Nat.clog 2 v-1+2=Nat.clog 2 v+1 := by omega
  rw [he] at hpow
  calc
    2*denominator v=2048*(Nat.clog 2 v+1) := by unfold denominator;ring
    _ ≤ 2^(Nat.clog 2 v-1) := hpow
    _ ≤ v := hlow.le

theorem sufficient_positive {v : ℕ} (hv : denominator v≤ v) : 0<sufficient v :=
  Nat.div_pos hv (denominator_pos v)

theorem fallback_bounded {v : ℕ} (hv : selected v=0) : v<2^17 := by
  by_contra h
  have hl := sufficient_large (by omega : 2^17≤ v)
  have hp := sufficient_positive (by omega : denominator v≤ v)
  have hs := selected_ge_sufficient v
  omega

theorem sufficient_half {v : ℕ} (hv : 2*denominator v≤ v) :
    v≤2*denominator v*sufficient v := by
  have hd := denominator_pos v
  have hb : 1≤ sufficient v := sufficient_positive (by omega)
  have hrem := Nat.mod_lt v hd
  have heq := Nat.mod_add_div v (denominator v)
  change v≤2*denominator v*(v/denominator v)
  dsimp [sufficient] at hb
  nlinarith

theorem selected_chunkCount {v : ℕ} (hv : 2*denominator v≤ v) {s : ℕ} (hs : s≤ v) :
    chunkCount s (selected v)≤2*denominator v+1 := by
  have hpos := sufficient_positive (by omega : denominator v≤ v)
  have hsel := selected_ge_sufficient v
  have hhalf := sufficient_half hv
  have hmul : v≤2*denominator v*selected v :=
    hhalf.trans (Nat.mul_le_mul_left _ hsel)
  have hb : 0<selected v := by omega
  dsimp [chunkCount]
  apply (Nat.div_le_iff_le_mul_add_pred hb).2
  have hp : (2*denominator v+1)*selected v=2*denominator v*selected v+selected v := by ring
  rw [Nat.mul_comm (selected v) (2*denominator v+1),hp]
  omega

theorem large_chunkCount {v : ℕ} (hv : 2^17≤ v) {s : ℕ} (hs : s≤ v) :
    (chunkSizes s (selected v)).length≤2048*(Nat.clog 2 v+1)+1 := by
  rw [chunkSizes_length]
  calc
    chunkCount s (selected v)≤ 2*denominator v+1 := selected_chunkCount (sufficient_large hv) hs
    _ = _ := by unfold denominator;ring

/-- Literal complement scan. Borrowing never leaves the parent width. -/
def available {v : ℕ} (source target : Finset (Fin v)) : Finset (Fin v) :=
  Finset.univ\(source∪target)

def availableList {v : ℕ} (source target : Finset (Fin v)) : List (Fin v) :=
  (List.finRange v).filter (fun i => decide (i∉source∪target))

theorem availableList_nodup {v : ℕ} (source target : Finset (Fin v)) :
    (availableList source target).Nodup := (List.nodup_finRange v).filter _

theorem availableList_toFinset {v : ℕ} (source target : Finset (Fin v)) :
    (availableList source target).toFinset=available source target := by
  ext i
  simp [availableList,available]

theorem availableList_length {v : ℕ} (source target : Finset (Fin v)) :
    (availableList source target).length=(available source target).card := by
  rw [←availableList_toFinset source target]
  exact (List.toFinset_card_of_nodup (availableList_nodup source target)).symm

def borrowed {v : ℕ} (source target : Finset (Fin v)) (g : ℕ) : List (Fin v) :=
  (availableList source target).take g

theorem available_card {v a e : ℕ} (source target : Finset (Fin v))
    (hd : Disjoint source target) (hs : source.card=e) (ht : target.card=a) :
    (available source target).card=v-(a+e) := by
  rw [available,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin,
    Finset.card_union_of_disjoint hd,hs,ht,Nat.add_comm e a]

theorem borrowed_length {v : ℕ} (source target : Finset (Fin v)) (g : ℕ)
    (hg : g≤ (available source target).card) : (borrowed source target g).length=g := by
  simp [borrowed,List.length_take,availableList_length,min_eq_left hg]

theorem borrowed_nodup {v : ℕ} (source target : Finset (Fin v)) (g : ℕ) :
    (borrowed source target g).Nodup :=
  (availableList_nodup source target).take

theorem borrowed_avoids {v : ℕ} (source target : Finset (Fin v)) (g : ℕ)
    {i : Fin v} (hi : i∈borrowed source target g) : i∉source ∧ i∉target := by
  have ha : i∈available source target := by
    rw [←availableList_toFinset source target]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take hi)
  have h := (Finset.mem_sdiff.mp ha).2
  exact ⟨fun hs => h (Finset.mem_union_left _ hs),fun ht => h (Finset.mem_union_right _ ht)⟩

def borrowedEmbedding {v : ℕ} (source target : Finset (Fin v)) (g : ℕ)
    (hg : g≤ (available source target).card) : Fin g ↪ Fin v where
  toFun i := (borrowed source target g).get ⟨i.val,by rw [borrowed_length source target g hg];exact i.isLt⟩
  inj' i j h := Fin.ext (congrArg (fun z : Fin (borrowed source target g).length => z.val)
    ((borrowed_nodup source target g).injective_get h))

theorem borrowedEmbedding_avoids {v : ℕ} (source target : Finset (Fin v)) (g : ℕ)
    (hg : g≤ (available source target).card) (i : Fin g) :
    borrowedEmbedding source target g hg i∉source ∧ borrowedEmbedding source target g hg i∉target :=
  borrowed_avoids source target g (List.get_mem _ _)

/-- The measured integer fit yields an actual injective assignment of every
printed gate to a distinct coordinate outside its source and target chunks. -/
theorem selected_borrowing {v a e : ℕ} (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source target : Finset (Fin v)) (hd : Disjoint source target)
    (hs : source.card=e) (ht : target.card=a) :
    (borrowed source target (gateCount a e)).length=gateCount a e ∧
      (borrowed source target (gateCount a e)).Nodup ∧
      ∀ i∈borrowed source target (gateCount a e), i∉source ∧ i∉target := by
  have hfit := selected_fit hv ha he
  have hg : gateCount a e≤ (available source target).card := by
    rw [available_card source target hd hs ht]
    omega
  exact ⟨borrowed_length source target _ hg,borrowed_nodup source target _,
    fun _ hi => borrowed_avoids source target _ hi⟩

end ExactFourierCircuits.UniformWorkspacePlanner
