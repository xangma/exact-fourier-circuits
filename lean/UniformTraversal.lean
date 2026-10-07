import Mathlib

set_option autoImplicit false

namespace ExactFourierCircuits.UniformTraversal
open scoped BigOperators

/-- Counts every digit prefix, including the empty prefix and each leaf. -/
def nodeCount : List ℕ → ℕ
  | [] => 1
  | r :: rs => 1 + r * nodeCount rs

def prefixCounts : List ℕ → List ℕ
  | [] => [1]
  | r :: rs => 1 :: (prefixCounts rs).map (fun n => r * n)

theorem nodeCount_eq_prefix_sum (rs : List ℕ) : nodeCount rs = (prefixCounts rs).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [nodeCount, prefixCounts, List.sum_cons, ih]
    congr 1
    simpa only [List.map_id, id_eq] using (List.sum_map_mul_left (prefixCounts rs) id r).symm

theorem nodeCount_lt_twice_product (rs : List ℕ) (hr : ∀ r ∈ rs, 2 ≤ r) :
    nodeCount rs < 2 * rs.prod := by
  induction rs with
  | nil => norm_num [nodeCount]
  | cons r rs ih =>
    have htwo : 2 ≤ r := hr r (by simp)
    have ht : nodeCount rs + 1 ≤ 2 * rs.prod := by
      have hi := ih (fun q hq => hr q (by simp [hq]))
      omega
    change 1 + r * nodeCount rs < 2 * (r * rs.prod)
    calc
      _ < r + r * nodeCount rs := Nat.add_lt_add_right (by omega) _
      _ = r * (nodeCount rs + 1) := by ring
      _ ≤ r * (2 * rs.prod) := Nat.mul_le_mul_left r ht
      _ = _ := by ring

theorem nodeCount_mono {bs rs : List ℕ} (hb : List.Forall₂ (fun b r => b ≤ r) bs rs) :
    nodeCount bs ≤ nodeCount rs := by
  induction hb with
  | nil => rfl
  | @cons b r bs rs hbr htail ih =>
    simp only [nodeCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul hbr ih) 1

/-- Block axes may have only one block: only the digit radices need be at least two. -/
theorem block_prefix_bound {bs rs : List ℕ}
    (hb : List.Forall₂ (fun b r => b ≤ r) bs rs) (hr : ∀ r ∈ rs, 2 ≤ r) :
    nodeCount bs < 2 * rs.prod :=
  lt_of_le_of_lt (nodeCount_mono hb) (nodeCount_lt_twice_product rs hr)

theorem prefix_product_mono {bs rs : List ℕ}
    (hb : List.Forall₂ (fun b r => b ≤ r) bs rs) (k : ℕ) :
    (bs.take k).prod ≤ (rs.take k).prod := by
  induction hb generalizing k with
  | nil => simp
  | @cons b r bs rs hbr htail ih =>
    cases k with
    | zero => simp
    | succ k => simpa using Nat.mul_le_mul hbr (ih k)

/-- Each layer stores its finite table and updates a fixed-size running state. -/
structure Layer (α : Type*) where
  radix : ℕ
  advance : Fin radix → α → α

def radices {α : Type*} (ls : List (Layer α)) : List ℕ := ls.map Layer.radix

def Choices {α : Type*} : List (Layer α) → Type
  | [] => Unit
  | l :: ls => Fin l.radix × Choices ls

def follow {α : Type*} : (ls : List (Layer α)) → Choices ls → α → α
  | [], _, s => s
  | l :: ls, (a, ds), s => follow ls ds (l.advance a s)

structure Acc (α : Type*) where
  output : List α
  visits : ℕ

/-- Depth first traversal with a cons accumulator: no digit-prefix list is copied.
    Each leaf is consed once; a final reversal may restore lexicographic order. -/
def traverse {α : Type*} : List (Layer α) → α → Acc α → Acc α
  | [], s, acc => ⟨s :: acc.output, acc.visits + 1⟩
  | l :: ls, s, acc =>
      (List.finRange l.radix).foldl (fun a d => traverse ls (l.advance d s) a)
        ⟨acc.output, acc.visits + 1⟩

theorem foldl_measure {α β : Type*} (xs : List α) (step : β → α → β)
    (measure : β → ℕ) (cost : ℕ)
    (hs : ∀ s a, measure (step s a) = measure s + cost) (s : β) :
    measure (xs.foldl step s) = measure s + xs.length * cost := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih => rw [List.foldl_cons, ih, hs]; simp only [List.length_cons]; ring

theorem traverse_visits {α : Type*} (ls : List (Layer α)) (s : α) (acc : Acc α) :
    (traverse ls s acc).visits = acc.visits + nodeCount (radices ls) := by
  induction ls generalizing s acc with
  | nil => rfl
  | cons l ls ih =>
    rw [traverse, foldl_measure _ _ Acc.visits (nodeCount (radices ls))
      (fun a d => ih (l.advance d s) a)]
    simp only [List.length_finRange]
    change (acc.visits + 1) + l.radix * nodeCount (radices ls) =
      acc.visits + (1 + l.radix * nodeCount (radices ls))
    omega

theorem traverse_length {α : Type*} (ls : List (Layer α)) (s : α) (acc : Acc α) :
    (traverse ls s acc).output.length = acc.output.length + (radices ls).prod := by
  induction ls generalizing s acc with
  | nil => simp [traverse, radices]
  | cons l ls ih =>
    rw [traverse, foldl_measure _ _ (fun a : Acc α => a.output.length) (radices ls).prod
      (fun a d => ih (l.advance d s) a)]
    simp [radices]

theorem foldl_output_mem {α β : Type*} (xs : List α) (step : Acc β → α → Acc β)
    (P : α → β → Prop)
    (hs : ∀ s a y, y ∈ (step s a).output ↔ y ∈ s.output ∨ P a y)
    (s : Acc β) (y : β) :
    y ∈ (xs.foldl step s).output ↔ y ∈ s.output ∨ ∃ a ∈ xs, P a y := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, ih, hs]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    tauto

/-- The accumulator traversal returns exactly the states obtained by following digit tuples. -/
theorem traverse_output_mem {α : Type*} (ls : List (Layer α)) (s y : α) (acc : Acc α) :
    y ∈ (traverse ls s acc).output ↔ y ∈ acc.output ∨ ∃ ds : Choices ls, follow ls ds s = y := by
  induction ls generalizing s y acc with
  | nil => simp [traverse, Choices, follow, eq_comm, or_comm]
  | cons l ls ih =>
    rw [traverse, foldl_output_mem _ _
      (fun a y => ∃ ds : Choices ls, follow ls ds (l.advance a s) = y)
      (fun acc a y => ih (l.advance a s) y acc)]
    simp only [List.mem_finRange, true_and]
    simp only [Choices, follow, Prod.exists]

def run {α : Type*} (ls : List (Layer α)) (s : α) : Acc α := traverse ls s ⟨[], 0⟩

theorem run_visits {α : Type*} (ls : List (Layer α)) (s : α) :
    (run ls s).visits = nodeCount (radices ls) := by
  simpa [run] using traverse_visits ls s ⟨[], 0⟩

theorem run_length {α : Type*} (ls : List (Layer α)) (s : α) :
    (run ls s).output.length = (radices ls).prod := by
  simpa [run] using traverse_length ls s ⟨[], 0⟩

theorem run_output_mem {α : Type*} (ls : List (Layer α)) (s y : α) :
    y ∈ (run ls s).output ↔ ∃ ds : Choices ls, follow ls ds s = y := by
  simpa [run] using traverse_output_mem ls s y ⟨[], 0⟩

theorem run_linear_prefix_bound {α : Type*} (ls : List (Layer α)) (s : α)
    (hr : ∀ r ∈ radices ls, 2 ≤ r) : (run ls s).visits < 2 * (radices ls).prod := by
  rw [run_visits]
  exact nodeCount_lt_twice_product _ hr

def addressLayer (r : ℕ) : Layer ℕ := ⟨r, fun a I => I * r + a.val⟩
def addressLayers (rs : List ℕ) : List (Layer ℕ) := rs.map addressLayer

theorem address_radices (rs : List ℕ) : radices (addressLayers rs) = rs := by
  simp only [radices, addressLayers, List.map_map]
  change rs.map id = rs
  exact List.map_id rs

def encode : (rs : List ℕ) → Choices (addressLayers rs) → ℕ
  | [], _ => 0
  | _ :: rs, (a, ds) => a.val * rs.prod + encode rs ds

theorem follow_address (rs : List ℕ) (ds : Choices (addressLayers rs)) (I : ℕ) :
    follow (addressLayers rs) ds I = I * rs.prod + encode rs ds := by
  induction rs generalizing I with
  | nil => change I = I * 1 + 0; omega
  | cons r rs ih =>
    rcases ds with ⟨a, ds⟩
    exact (ih ds (I * r + a.val)).trans (by
      change (I * r + a.val) * rs.prod + encode rs ds =
        I * (r * rs.prod) + (a.val * rs.prod + encode rs ds)
      ring)

theorem encode_bound (rs : List ℕ) (ds : Choices (addressLayers rs)) : encode rs ds < rs.prod := by
  induction rs with
  | nil => simp [encode]
  | cons r rs ih =>
    rcases ds with ⟨a, ds⟩
    have ht := ih ds
    have ha : a.val < r := a.isLt
    change a.val * rs.prod + encode rs ds < r * rs.prod
    calc
      _ < (a.val + 1) * rs.prod := by nlinarith
      _ ≤ r * rs.prod := Nat.mul_le_mul_right _ (by omega)

theorem address_bounds (rs : List ℕ) (ds : Choices (addressLayers rs)) (I : ℕ) :
    I * rs.prod ≤ follow (addressLayers rs) ds I ∧
      follow (addressLayers rs) ds I < (I + 1) * rs.prod := by
  rw [follow_address]
  have h := encode_bound rs ds
  constructor <;> nlinarith

theorem generated_address_bound (rs : List ℕ) (j : ℕ)
    (hj : j ∈ (run (addressLayers rs) 0).output) : j < rs.prod := by
  obtain ⟨ds, rfl⟩ := (run_output_mem _ _ _).mp hj
  simpa [follow_address] using encode_bound rs ds

theorem generated_address_count (rs : List ℕ) :
    (run (addressLayers rs) 0).output.length = rs.prod := by
  rw [run_length, address_radices]

theorem generated_address_work (rs : List ℕ) (hr : ∀ r ∈ rs, 2 ≤ r) :
    (run (addressLayers rs) 0).visits < 2 * rs.prod := by
  rw [run_visits, address_radices]
  exact nodeCount_lt_twice_product rs hr

theorem tail_product_positive (r p : ℕ) (i : Fin (r * p)) : 0 < p := by
  by_contra hp
  have hz : p = 0 := by omega
  have hi := i.isLt
  simp [hz] at hi

def quotientDigit (r p : ℕ) (i : Fin (r * p)) : Fin r :=
  ⟨i.val / p, (Nat.div_lt_iff_lt_mul (tail_product_positive r p i)).2 i.isLt⟩

def remainderDigit (r p : ℕ) (i : Fin (r * p)) : Fin p :=
  ⟨i.val % p, Nat.mod_lt _ (tail_product_positive r p i)⟩

/-- Reference inverse address arithmetic; the traversal does not call this at each leaf. -/
def decode : (rs : List ℕ) → Fin rs.prod → Choices (addressLayers rs)
  | [], _ => ()
  | r :: rs, i => (quotientDigit r rs.prod i, decode rs (remainderDigit r rs.prod i))

theorem encode_decode (rs : List ℕ) (i : Fin rs.prod) : encode rs (decode rs i) = i.val := by
  induction rs with
  | nil => have hi := i.isLt; simp only [List.prod_nil] at hi; simp [encode]; omega
  | cons r rs ih =>
    change (i.val / rs.prod) * rs.prod + encode rs (decode rs (remainderDigit r rs.prod i)) = i.val
    rw [ih]
    change (i.val / rs.prod) * rs.prod + i.val % rs.prod = i.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val rs.prod

theorem generated_address_complete (rs : List ℕ) (i : Fin rs.prod) :
    i.val ∈ (run (addressLayers rs) 0).output := by
  apply (run_output_mem _ _ _).mpr
  refine ⟨decode rs i, ?_⟩
  rw [follow_address, encode_decode]
  simp

theorem generated_addresses_finset (rs : List ℕ) :
    (run (addressLayers rs) 0).output.toFinset = Finset.range rs.prod := by
  ext j
  simp only [List.mem_toFinset, Finset.mem_range]
  exact ⟨generated_address_bound rs j, fun hj => generated_address_complete rs ⟨j, hj⟩⟩

/-- Every mixed-radix array address is generated exactly once. -/
theorem generated_addresses_nodup (rs : List ℕ) : (run (addressLayers rs) 0).output.Nodup := by
  have hc : (run (addressLayers rs) 0).output.toFinset.card = (run (addressLayers rs) 0).output.length := by
    rw [generated_addresses_finset, Finset.card_range, generated_address_count]
  exact (Multiset.toFinset_card_eq_card_iff_nodup
    (m := ((run (addressLayers rs) 0).output : Multiset ℕ))).mp hc

structure PackingState where
  start : ℕ
  width : ℕ
  offset : ℕ
  original : ℕ

def initialPacking : PackingState := ⟨0, 1, 0, 0⟩

/-- The suffix stride and local digit/block information are prepared once in local tables. -/
structure PackingDigit where
  radix : ℕ
  suffix : ℕ
  preceding : ℕ
  blockWidth : ℕ
  position : ℕ
  originalDigit : ℕ

def packingStep (d : PackingDigit) (s : PackingState) : PackingState :=
  ⟨s.start + s.width * d.preceding * d.suffix, s.width * d.blockWidth,
    s.offset * d.blockWidth + d.position, s.original * d.radix + d.originalDigit⟩

def packingFollow : List PackingDigit → PackingState → PackingState
  | [], s => s
  | d :: ds, s => packingFollow ds (packingStep d s)

def blockProduct (ds : List PackingDigit) : ℕ := (ds.map PackingDigit.blockWidth).prod
def digitProduct (ds : List PackingDigit) : ℕ := (ds.map PackingDigit.radix).prod
def startContribution : List PackingDigit → ℕ
  | [] => 0
  | d :: ds => d.preceding * d.suffix + d.blockWidth * startContribution ds
def withinAddress : List PackingDigit → ℕ
  | [] => 0
  | d :: ds => d.position * blockProduct ds + withinAddress ds
def originalAddress : List PackingDigit → ℕ
  | [] => 0
  | d :: ds => d.originalDigit * digitProduct ds + originalAddress ds

/-- Exact closed forms for all four constant-size state updates in the paper. -/
theorem packingFollow_formulas (ds : List PackingDigit) (s : PackingState) :
    (packingFollow ds s).start = s.start + s.width * startContribution ds ∧
    (packingFollow ds s).width = s.width * blockProduct ds ∧
    (packingFollow ds s).offset = s.offset * blockProduct ds + withinAddress ds ∧
    (packingFollow ds s).original = s.original * digitProduct ds + originalAddress ds := by
  induction ds generalizing s with
  | nil => simp [packingFollow, startContribution, withinAddress, originalAddress, blockProduct, digitProduct]
  | cons d ds ih =>
    obtain ⟨hS, hQ, ho, hI⟩ := ih (packingStep d s)
    simp only [packingFollow]
    rw [hS, hQ, ho, hI]
    simp only [packingStep, startContribution, withinAddress, originalAddress,
      blockProduct, digitProduct, List.map_cons, List.prod_cons]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

theorem initialPacking_formulas (ds : List PackingDigit) :
    (packingFollow ds initialPacking).start = startContribution ds ∧
    (packingFollow ds initialPacking).width = blockProduct ds ∧
    (packingFollow ds initialPacking).offset = withinAddress ds ∧
    (packingFollow ds initialPacking).original = originalAddress ds := by
  simpa [initialPacking] using packingFollow_formulas ds initialPacking

def startSummands : List PackingDigit → List ℕ
  | [] => []
  | d :: ds => d.preceding * d.suffix :: (startSummands ds).map (fun n => d.blockWidth * n)

/-- The sector start is the paper's sum of prefix widths times preceding-block strides. -/
theorem startContribution_eq_sum (ds : List PackingDigit) : startContribution ds = (startSummands ds).sum := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [startContribution, startSummands, List.sum_cons, ih]
    congr 1
    simpa only [List.map_id, id_eq] using
      (List.sum_map_mul_left (startSummands ds) id d.blockWidth).symm

def ValidPacking : List PackingDigit → Prop
  | [] => True
  | d :: ds => d.suffix = digitProduct ds ∧ d.preceding + d.blockWidth ≤ d.radix ∧
      d.position < d.blockWidth ∧ d.originalDigit < d.radix ∧ ValidPacking ds

theorem withinAddress_bound (ds : List PackingDigit) (hv : ValidPacking ds) :
    withinAddress ds < blockProduct ds := by
  induction ds with
  | nil => simp [withinAddress, blockProduct]
  | cons d ds ih =>
    obtain ⟨_, _, ht, _, htail⟩ := hv
    have hi := ih htail
    change d.position * blockProduct ds + withinAddress ds < d.blockWidth * blockProduct ds
    calc
      _ < (d.position + 1) * blockProduct ds := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem originalAddress_bound (ds : List PackingDigit) (hv : ValidPacking ds) :
    originalAddress ds < digitProduct ds := by
  induction ds with
  | nil => simp [originalAddress, digitProduct]
  | cons d ds ih =>
    obtain ⟨_, _, _, ha, htail⟩ := hv
    have hi := ih htail
    change d.originalDigit * digitProduct ds + originalAddress ds < d.radix * digitProduct ds
    calc
      _ < (d.originalDigit + 1) * digitProduct ds := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem sector_fits (ds : List PackingDigit) (hv : ValidPacking ds) :
    startContribution ds + blockProduct ds ≤ digitProduct ds := by
  induction ds with
  | nil => simp [startContribution, blockProduct, digitProduct]
  | cons d ds ih =>
    obtain ⟨hsuffix, hpq, _, _, htail⟩ := hv
    have ht := ih htail
    change (d.preceding * d.suffix + d.blockWidth * startContribution ds) +
      d.blockWidth * blockProduct ds ≤ d.radix * digitProduct ds
    rw [hsuffix]
    calc
      _ = d.preceding * digitProduct ds +
          d.blockWidth * (startContribution ds + blockProduct ds) := by ring
      _ ≤ d.preceding * digitProduct ds + d.blockWidth * digitProduct ds :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
      _ = (d.preceding + d.blockWidth) * digitProduct ds := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hpq

theorem packed_address_bound (ds : List PackingDigit) (hv : ValidPacking ds) :
    (packingFollow ds initialPacking).start + (packingFollow ds initialPacking).offset < digitProduct ds := by
  rw [(initialPacking_formulas ds).1, (initialPacking_formulas ds).2.2.1]
  have hf := sector_fits ds hv
  have ho := withinAddress_bound ds hv
  omega

/-- This invariant is maintained at internal prefixes, before the remaining axes are visited. -/
theorem packingStep_remaining_bound (d : PackingDigit) (s : PackingState) (R : ℕ)
    (hs : s.start + s.width * (d.radix * d.suffix) ≤ R)
    (hd : d.preceding + d.blockWidth ≤ d.radix) :
    (packingStep d s).start + (packingStep d s).width * d.suffix ≤ R := by
  calc
    _ = s.start + s.width * ((d.preceding + d.blockWidth) * d.suffix) := by
      simp only [packingStep]; ring
    _ ≤ s.start + s.width * (d.radix * d.suffix) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hd)) _
    _ ≤ R := hs

theorem packingStep_offset_bound (d : PackingDigit) (s : PackingState)
    (hs : s.offset < s.width) (hd : d.position < d.blockWidth) :
    (packingStep d s).offset < (packingStep d s).width := by
  change s.offset * d.blockWidth + d.position < s.width * d.blockWidth
  calc
    _ < (s.offset + 1) * d.blockWidth := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem packingStep_original_bound (d : PackingDigit) (s : PackingState) (P : ℕ)
    (hs : s.original < P) (hd : d.originalDigit < d.radix) :
    (packingStep d s).original < P * d.radix := by
  change s.original * d.radix + d.originalDigit < P * d.radix
  calc
    _ < (s.original + 1) * d.radix := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem packing_state_word_bounds (s : PackingState) (R remaining originalPrefix : ℕ)
    (hr : 0 < remaining) (hp : originalPrefix ≤ R)
    (hfit : s.start + s.width * remaining ≤ R)
    (ho : s.offset < s.width) (hI : s.original < originalPrefix) :
    s.start ≤ R ∧ s.width ≤ R ∧ s.offset < R ∧ s.original < R := by
  have hw : s.width ≤ s.width * remaining := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s.width (show 1 ≤ remaining by omega)
  omega

def blockBefore (widths : List ℕ) (b : Fin widths.length) : ℕ := (widths.take b.val).sum

theorem block_end_le_sum (widths : List ℕ) (b : Fin widths.length) :
    blockBefore widths b + widths.get b ≤ widths.sum := by
  induction widths with
  | nil => exact Fin.elim0 b
  | cons q widths ih =>
    refine Fin.cases ?_ (fun b => ?_) b
    · change 0 + q ≤ q + widths.sum
      omega
    · change (q + (widths.take b.val).sum) + widths.get b ≤ q + widths.sum
      have hi := ih b
      unfold blockBefore at hi
      omega

theorem block_count_le_sum (widths : List ℕ) (hq : ∀ q ∈ widths, 1 ≤ q) :
    widths.length ≤ widths.sum := by
  induction widths with
  | nil => simp
  | cons q widths ih =>
    have hhead := hq q (by simp)
    have htail := ih (fun a ha => hq a (by simp [ha]))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem block_partition_radices (axes : List (List ℕ))
    (hq : ∀ widths ∈ axes, ∀ q ∈ widths, 1 ≤ q) :
    List.Forall₂ (fun b r => b ≤ r) (axes.map List.length) (axes.map List.sum) := by
  induction axes with
  | nil => exact .nil
  | cons widths axes ih =>
    exact .cons (block_count_le_sum widths (hq widths (by simp)))
      (ih (fun w hw => hq w (by simp [hw])))

/-- Actual positive block partitions give the charged block-choice bound, including singleton axes. -/
theorem block_partition_prefix_bound (axes : List (List ℕ))
    (hq : ∀ widths ∈ axes, ∀ q ∈ widths, 1 ≤ q)
    (hr : ∀ r ∈ axes.map List.sum, 2 ≤ r) :
    nodeCount (axes.map List.length) < 2 * (axes.map List.sum).prod :=
  block_prefix_bound (block_partition_radices axes hq) hr

theorem run_block_partition_bound {α : Type*} (ls : List (Layer α)) (s : α)
    (axes : List (List ℕ)) (hl : radices ls = axes.map List.length)
    (hq : ∀ widths ∈ axes, ∀ q ∈ widths, 1 ≤ q)
    (hr : ∀ r ∈ axes.map List.sum, 2 ≤ r) :
    (run ls s).visits < 2 * (axes.map List.sum).prod := by
  rw [run_visits, hl]
  exact block_partition_prefix_bound axes hq hr

/-- An arbitrary local permutation permits nonconsecutive original coordinates in a block. -/
def blockDigit (widths : List ℕ) (b : Fin widths.length) (t : Fin (widths.get b))
    (suffix : ℕ) (π : Equiv.Perm (Fin widths.sum)) : PackingDigit :=
  ⟨widths.sum, suffix, blockBefore widths b, widths.get b, t.val,
    (π ⟨blockBefore widths b + t.val,
      lt_of_lt_of_le (Nat.add_lt_add_left t.isLt _) (block_end_le_sum widths b)⟩).val⟩

theorem blockDigit_valid (widths : List ℕ) (b : Fin widths.length) (t : Fin (widths.get b))
    (suffix : ℕ) (π : Equiv.Perm (Fin widths.sum)) :
    (blockDigit widths b t suffix π).preceding + (blockDigit widths b t suffix π).blockWidth ≤
        (blockDigit widths b t suffix π).radix ∧
      (blockDigit widths b t suffix π).position < (blockDigit widths b t suffix π).blockWidth ∧
      (blockDigit widths b t suffix π).originalDigit < (blockDigit widths b t suffix π).radix :=
  ⟨block_end_le_sum widths b, t.isLt, (π _).isLt⟩

theorem blockProduct_pow_two (ds : List PackingDigit)
    (hq : ∀ d ∈ ds, d.blockWidth = 1 ∨ d.blockWidth = 2) :
    blockProduct ds = 2 ^ (ds.countP (fun d => d.blockWidth == 2)) := by
  induction ds with
  | nil => simp [blockProduct]
  | cons d ds ih =>
    have ht := ih (fun a ha => hq a (by simp [ha]))
    have hd := hq d (by simp)
    rcases hd with h | h <;>
      simp [blockProduct, h, ← ht, pow_succ, Nat.mul_comm]

theorem pair_sector_width (ds : List PackingDigit)
    (hq : ∀ d ∈ ds, d.blockWidth = 1 ∨ d.blockWidth = 2) :
    (packingFollow ds initialPacking).width = 2 ^ (ds.countP (fun d => d.blockWidth == 2)) :=
  (initialPacking_formulas ds).2.1.trans (blockProduct_pow_two ds hq)

end ExactFourierCircuits.UniformTraversal
