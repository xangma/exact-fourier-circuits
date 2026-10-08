import UniformTensorMonomialMachine
import UniformColoring
import UniformRadixInstructionMachine
import UniformSectorPackingMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingAxisTableMachine
open UniformMachine UniformColoring
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Nat840 = axis radix,841 = pair count,842 = three-word ordered-pair rows,
843 = forward permutation,844 = widths,845 = fresh marker bank,846 = four-word axis row.
Scratch is Nat850..861. The coefficient word of each input row is ignored. -/
def boot : List Op := [.literal 850 0,.literal 851 1,.literal 852 2,
  .literal 853 3,.literal 854 0]
def clear : List Op := [.add 857 845 854,.putNat 857 850,.add 854 854 851]
def pairStart : List Op := [.literal 854 0,.literal 855 0,.literal 856 0]
def pairBody : List Op := [.mul 857 854 853,.add 857 842 857,.getNat 858 857,
  .add 857 857 851,.getNat 859 857,.add 857 843 855,.putNat 857 858,
  .add 857 857 851,.putNat 857 859,.add 857 845 858,.putNat 857 851,
  .add 857 845 859,.putNat 857 851,.add 857 844 856,.putNat 857 852,
  .add 854 854 851,.add 855 855 852,.add 856 856 851]
def singletonStart : List Op := [.literal 860 0]
def singletonRead : List Op := [.add 857 845 860,.getNat 861 857]
def singletonBody : List Op := [.add 857 843 855,.putNat 857 860,
  .add 857 844 856,.putNat 857 851,.add 855 855 851,.add 856 856 851]
def advance : List Op := [.add 860 860 851]
def finish : List Op := [.add 857 846 850,.putNat 857 856,
  .add 857 857 851,.putNat 857 844,.add 857 857 851,.putNat 857 840,
  .add 857 857 851,.putNat 857 843]
def program : Program := boot.map Op.code ++ [.branchLT 854 840 6 10] ++
  clear.map Op.code ++ [.jump 5] ++ pairStart.map Op.code ++
  [.branchLT 854 841 14 33] ++ pairBody.map Op.code ++ [.jump 13] ++
  singletonStart.map Op.code ++ [.branchLT 860 840 35 46] ++
  singletonRead.map Op.code ++ [.branchLT 861 851 38 44] ++
  singletonBody.map Op.code ++ advance.map Op.code ++ [.jump 34] ++
  finish.map Op.code ++ [.halt]
theorem program_length : program.length = 55 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem clear_code : BlockAt clear program 6 := by
  intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem pairStart_code : BlockAt pairStart program 10 := by
  intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem pairBody_code : BlockAt pairBody program 14 := by
  intro i hi;change i < 18 at hi;interval_cases i <;> rfl
theorem singletonStart_code : BlockAt singletonStart program 33 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem singletonRead_code : BlockAt singletonRead program 35 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem singletonBody_code : BlockAt singletonBody program 38 := by
  intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advance program 44 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem finish_code : BlockAt finish program 46 := by
  intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem clear_at : program[5]?=some (.branchLT 854 840 6 10) := rfl
theorem clear_jump : program[9]?=some (.jump 5) := rfl
theorem pair_at : program[13]?=some (.branchLT 854 841 14 33) := rfl
theorem pair_jump : program[32]?=some (.jump 13) := rfl
theorem singleton_at : program[34]?=some (.branchLT 860 840 35 46) := rfl
theorem used_at : program[37]?=some (.branchLT 861 851 38 44) := rfl
theorem singleton_jump : program[45]?=some (.jump 34) := rfl
theorem halt_at : program[54]?=some .halt := rfl

def paired {M : ℕ} (E : Fin M→Edge) : List ℕ :=
  (List.finRange M).flatMap (fun i=>[(E i).left,(E i).right])
def singletons {M : ℕ} (r : ℕ) (E : Fin M→Edge) : List ℕ :=
  (List.range r).filter (fun j=>decide (j∉paired E))
def ordered {M : ℕ} (r : ℕ) (E : Fin M→Edge) := paired E ++ singletons r E
def widths (r M : ℕ) := List.replicate M 2 ++ List.replicate (r-2*M) 1
def Matching {M : ℕ} (E : Fin M→Edge) : Prop :=
  ∀i j,i ≠ j→¬Conflict (E i) (E j)
def InRange {M : ℕ} (r : ℕ) (E : Fin M→Edge) : Prop :=
  ∀i,(E i).left < r ∧ (E i).right < r

theorem paired_length {M : ℕ} (E : Fin M→Edge) : (paired E).length = 2*M := by
  simp [paired,List.length_flatMap,List.map_const',Nat.mul_comm]
theorem paired_mem {M : ℕ} (E : Fin M→Edge) (j : ℕ) :
    j∈paired E ↔ ∃i,j = (E i).left ∨ j = (E i).right := by simp [paired]
theorem singleton_mem {M : ℕ} (r : ℕ) (E : Fin M→Edge) (j : ℕ) :
    j∈singletons r E ↔ j < r ∧ j∉paired E := by simp [singletons]
theorem ordered_mem {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hr:InRange r E) (j : ℕ) :
    j∈ordered r E ↔ j < r := by
  simp only [ordered,List.mem_append,singleton_mem]
  constructor
  · rintro (h|h)
    · obtain ⟨i,h|h⟩:=(paired_mem E j).mp h
      · exact h ▸ (hr i).1
      · exact h ▸ (hr i).2
    · exact h.1
  · intro hj
    by_cases h:j∈paired E
    · exact Or.inl h
    · exact Or.inr ⟨hj,h⟩
theorem paired_nodup {M : ℕ} (E : Fin M→Edge) (hm:Matching E) : (paired E).Nodup := by
  unfold paired
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _=>by simp [(E i).different],?_⟩
  apply (List.nodup_finRange M).imp
  intro i j hij a hi hj
  have hn:=hm i j hij
  simp only [List.mem_cons] at hi hj
  rcases hi with hi|hi <;> rcases hj with hj|hj
  all_goals simp_all [Conflict,Incident,eq_comm]
theorem ordered_nodup {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) :
    (ordered r E).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨paired_nodup E hm,(List.nodup_range).filter _,?_⟩
  intro j hj k hk he
  subst k
  exact ((singleton_mem r E j).mp hk).2 hj
theorem ordered_perm {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) : (ordered r E).Perm (List.range r) := by
  apply (List.perm_ext_iff_of_nodup (ordered_nodup r E hm) List.nodup_range).mpr
  intro j
  rw [ordered_mem r E hr,List.mem_range]
theorem matching_capacity {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) : 2*M ≤ r := by
  have h: (ordered r E).length = r := by simpa using (ordered_perm r E hm hr).length_eq
  simp only [ordered,List.length_append,paired_length] at h
  omega
theorem singletons_length {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) : (singletons r E).length = r-2*M := by
  have h: (ordered r E).length = r := by simpa using (ordered_perm r E hm hr).length_eq
  simp only [ordered,List.length_append,paired_length] at h
  omega
theorem widths_length (r M : ℕ) (h:2*M ≤ r) : (widths r M).length = r-M := by
  simp only [widths,List.length_append,List.length_replicate]
  omega
theorem widths_sum (r M : ℕ) (h:2*M ≤ r) : (widths r M).sum = r := by
  simp only [widths,List.sum_append,List.sum_replicate,Nat.nsmul_eq_mul]
  omega
theorem widths_one_two (r M : ℕ) : ∀q∈widths r M,q = 1 ∨ q = 2 := by
  intro q h
  simp only [widths,List.mem_append,List.mem_replicate] at h
  rcases h with h|h
  · exact Or.inr h.2
  · exact Or.inl h.2
def runtime (r M : ℕ) := 17*r+8*M+21
theorem runtime_linear (r M : ℕ) (h:2*M ≤ r) : runtime r M ≤ 21*r+21 := by
  unfold runtime
  omega

theorem ordered_length {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) : (ordered r E).length = r := by
  simpa using (ordered_perm r E hm hr).length_eq
def forward {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (i : Fin r) : Fin r :=
  let hi : i.val < (ordered r E).length := by rw [ordered_length r E hm hr];exact i.isLt
  ⟨(ordered r E)[i.val]'hi,(ordered_mem r E hr _).mp (List.getElem_mem hi)⟩
def inverse {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (i : Fin r) : Fin r :=
  ⟨(ordered r E).idxOf i.val,by
    have h : (ordered r E).idxOf i.val < (ordered r E).length :=
      List.idxOf_lt_length_iff.mpr ((ordered_mem r E hr _).mpr i.isLt)
    simpa only [ordered_length r E hm hr] using h⟩
theorem forward_inverse {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (i : Fin r) :
    forward r E hm hr (inverse r E hm hr i) = i := by
  apply Fin.ext
  exact List.getElem_idxOf (by
    rw [ordered_length r E hm hr]
    exact (inverse r E hm hr i).isLt)
theorem inverse_forward {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (i : Fin r) :
    inverse r E hm hr (forward r E hm hr i) = i := by
  apply Fin.ext
  have hi : i.val < (ordered r E).length := by rw [ordered_length r E hm hr];exact i.isLt
  have hx : (ordered r E).idxOf ((ordered r E)[i.val]'hi) < (ordered r E).length :=
    List.idxOf_lt_length_iff.mpr (List.getElem_mem hi)
  exact (ordered_nodup r E hm).getElem_inj_iff.mp (List.getElem_idxOf hx)
/-- Explicit list lookup and idxOf inverse; no finite-equivalence choice is used. -/
def originalPermutation {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) : Equiv.Perm (Fin r) :=
  ⟨forward r E hm hr,inverse r E hm hr,inverse_forward r E hm hr,forward_inverse r E hm hr⟩
def geometry {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (hpos:2 ≤ r) : UniformSectorPacking.Axis :=
  let hcap:=matching_capacity r E hm hr
  let hsum:=widths_sum r M hcap
  ⟨widths r M,widths_one_two r M,by rw [hsum];exact hpos,
    ((finCongr hsum).trans (originalPermutation r E hm hr)).trans (finCongr hsum).symm⟩
theorem geometry_permutation {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (hpos:2 ≤ r) (i : Fin (geometry r E hm hr hpos).widths.sum) :
    ((geometry r E hm hr hpos).originalPermutation i).val=
      (ordered r E)[i.val]'(by
        rw [ordered_length r E hm hr]
        have hi:=i.isLt
        change i.val < (widths r M).sum at hi
        simpa [widths_sum r M (matching_capacity r E hm hr)] using hi) := rfl

noncomputable section
structure Header (r M T P W U A : ℕ) (s : State) : Prop where
  radix : s.natReg 840 = r
  count : s.natReg 841 = M
  source : s.natReg 842 = T
  permutation : s.natReg 843 = P
  widths : s.natReg 844 = W
  markers : s.natReg 845 = U
  row : s.natReg 846 = A
structure Fixed (r M T P W U A : ℕ) (s : State) : Prop where
  header : Header r M T P W U A s
  zero : s.natReg 850 = 0
  one : s.natReg 851 = 1
  two : s.natReg 852 = 2
  three : s.natReg 853 = 3
structure ClearCursor (r M T P W U A i : ℕ) (s : State) : Prop where
  fixed : Fixed r M T P W U A s
  pc : s.pc = 5
  index : s.natReg 854 = i
def MarkerZero (U i : ℕ) (s : State) : Prop :=
  ∀ (j : ℕ), j < i → s.natHeap (U+j) = some 0
def Frame (s u : State) : Prop := u.scalarHeap = s.scalarHeap ∧
  u.scalarReg = s.scalarReg ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧
  (∀q,(q < 850 ∨ 862 ≤ q)→u.natReg q = s.natReg q)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun q hq=>(h'.2.2.2.2 q hq).trans (h.2.2.2.2 q hq)⟩
theorem Frame.saved {s u : State} (h:Frame s u) :
    ∀q,100 ≤ q→q ≤ 106→u.natReg q = s.natReg q := by
  intro q _ hq
  exact h.2.2.2.2 q (Or.inl (by omega))
theorem branch_runs (p : Program) (B n a b yes no : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:p[s.pc]?=some (.branchLT a b yes no)) (hs:WordBound B s)
    (hy:yes ≤ B) (hn:no ≤ B) :
    BoundedRuns p n x B s 1 (setPC s (if s.natReg a < s.natReg b then yes else no)) :=
  UniformRadixInstructionMachine.branch_runs p n B a b yes no x s hs hy hn hc
theorem jump_runs (p : Program) (B n target : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:p[s.pc]?=some (.jump target)) (hs:WordBound B s) (ht:target ≤ B) :
    BoundedRuns p n x B s 1 (setPC s target) :=
  UniformRadixInstructionMachine.jump_runs p n B target x s hs ht hc
theorem Fixed.withPC {r M T P W U A : ℕ} {s : State}
    (h:Fixed r M T P W U A s) (pc : ℕ) : Fixed r M T P W U A (setPC s pc) :=
  ⟨⟨h.header.radix,h.header.count,h.header.source,h.header.permutation,
    h.header.widths,h.header.markers,h.header.row⟩,h.zero,h.one,h.two,h.three⟩
def clearStep (s : State) := setPC (applyBlock clear (setPC s 6)) 5
theorem boot_cursor {r M T P W U A : ℕ} {s : State}
    (h:Header r M T P W U A s) (hp:s.pc = 0) :
    ClearCursor r M T P W U A 0 (applyBlock boot s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_⟩
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next,hp,
    h.radix,h.count,h.source,h.permutation,h.widths,h.markers,h.row]
theorem boot_frame (s : State) : Frame s (applyBlock boot s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
theorem clearStep_heap {r M T P W U A i : ℕ} {s : State}
    (h:ClearCursor r M T P W U A i s) :
    (clearStep s).natHeap = Function.update s.natHeap (U+i) (some 0) := by
  simp [clearStep,clear,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.markers,h.index,h.fixed.zero,h.fixed.one]
theorem clearStep_cursor {r M T P W U A i : ℕ} {s : State}
    (h:ClearCursor r M T P W U A i s) :
    ClearCursor r M T P W U A (i+1) (clearStep s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_⟩
  all_goals simp [clearStep,clear,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.radix,h.fixed.header.count,h.fixed.header.source,
    h.fixed.header.permutation,h.fixed.header.widths,h.fixed.header.markers,
    h.fixed.header.row,h.index,h.fixed.zero,h.fixed.one,h.fixed.two,h.fixed.three]
theorem clearStep_frame (s : State) : Frame s (clearStep s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [clearStep,clear,applyBlock,Op.apply,setPC,writeNat,next]
theorem clearStep_zero {r M T P W U A i : ℕ} {s : State}
    (h:ClearCursor r M T P W U A i s) (hz:MarkerZero U i s) :
    MarkerZero U (i+1) (clearStep s) := by
  intro j hj
  rw [clearStep_heap h]
  by_cases he:j = i
  · simp [he]
  · rw [Function.update_of_ne (by omega)]
    exact hz j (by omega)
theorem clearStep_bounded {r M T P W U A i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:ClearCursor r M T P W U A i s) (hi:i < r)
    (hU:U+r ≤ B) (hB:55 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (clearStep s) := by
  have first:=branch_runs program B n 854 840 6 10 x s
    (by rw [h.pc];exact clear_at) hs (by omega) (by omega)
  have cmp:s.natReg 854 < s.natReg 840:=by rw [h.index,h.fixed.header.radix];exact hi
  simp only [cmp,ite_true] at first
  let v:=setPC s 6
  have hr:readable clear v:=by simp [readable,clear,Op.readable]
  have pk:peak clear v ≤ B:=by
    simp [peak,clear,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.index,h.fixed.header.markers,h.fixed.zero,h.fixed.one]
    omega
  have body:=block_runs clear program 6 n B x v clear_code rfl first.final_bound
    (by change 6+3 ≤ B;omega) hr pk
  have pc:(applyBlock clear v).pc = 9:=by
    rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:=jump_runs program B n 5 x (applyBlock clear v)
    (by rw [pc];exact clear_jump) body.final_bound (by omega)
  simpa only [show clear.length = 3 from rfl,clearStep,v,Nat.add_assoc] using
    first.trans (body.trans last)

theorem clear_loop (remaining B n : ℕ) (x : Fin n→ℂ)
    {r M T P W U A i : ℕ} (s : State) (h:ClearCursor r M T P W U A i s)
    (hi:i+remaining = r) (hz:MarkerZero U i s) (hU:U+r ≤ B) (hB:55 ≤ B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*remaining) u ∧ ClearCursor r M T P W U A r u ∧
    MarkerZero U r u ∧ (∀a,(a < U ∨ U+r ≤ a)→u.natHeap a = s.natHeap a) ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i = r:=by omega
    subst i
    exact ⟨s,by simpa using BoundedRuns.refl hs,h,hz,fun _ _=>rfl,frame_refl s⟩
  | succ rem ih =>
    have il:i < r:=by omega
    have run:=clearStep_bounded B n x s h il hU hB hs
    obtain ⟨u,ru,uc,uz,uo,uf⟩:=ih (clearStep s) (clearStep_cursor h) (by omega)
      (clearStep_zero h hz) run.final_bound
    refine ⟨u,?_,uc,uz,?_,frame_trans (clearStep_frame s) uf⟩
    · convert run.trans ru using 1;omega
    · intro a ha
      rw [uo a ha,clearStep_heap h,Function.update_of_ne (by omega)]

/-- The full marker reset is executed from arbitrary dirty heaps. -/
theorem initialized (r M T P W U A B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Header r M T P W U A s) (hp:s.pc = 0) (hU:U+r ≤ B) (hB:55 ≤ B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*r+6) u ∧ u.pc = 10 ∧
    Fixed r M T P W U A u ∧ MarkerZero U r u ∧
    (∀a,(a < U ∨ U+r ≤ a)→u.natHeap a = s.natHeap a) ∧ Frame s u := by
  have br:readable boot s:=by simp [readable,boot,Op.readable]
  have pk:peak boot s ≤ B:=by simp [peak,boot,Op.peak];omega
  have start:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+5 ≤ B;omega) br pk
  obtain ⟨v,rv,vc,vz,vo,vf⟩:=clear_loop r B n x (applyBlock boot s)
    (boot_cursor h hp) (by omega) (by intro j hj;omega) hU hB start.final_bound
  have last:=branch_runs program B n 854 840 6 10 x v
    (by rw [vc.pc];exact clear_at) rv.final_bound (by omega) (by omega)
  have cmp:¬v.natReg 854 < v.natReg 840:=by rw [vc.index,vc.fixed.header.radix];omega
  simp only [cmp,ite_false] at last
  refine ⟨setPC v 10,?_,rfl,vc.fixed.withPC 10,vz,?_,?_⟩
  · convert start.trans (rv.trans last) using 1
    change 5*r+6 = 5+(5*r+1)
    omega
  · intro a ha
    exact vo a ha
  · exact frame_trans (boot_frame s) (frame_trans vf ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩)

structure PairCursor (r M T P W U A i : ℕ) (s : State) : Prop where
  fixed : Fixed r M T P W U A s
  pc : s.pc = 13
  index : s.natReg 854 = i
  permutationCount : s.natReg 855 = 2*i
  blockCount : s.natReg 856 = i
def Edges {M : ℕ} (E : Fin M→Edge) (T : ℕ) (s : State) : Prop :=
  ∀i:Fin M,s.natHeap (T+3*i.val) = some (E i).left ∧
    s.natHeap (T+3*i.val+1) = some (E i).right
def PairBank {M : ℕ} (E : Fin M→Edge) (P i : ℕ) (s : State) : Prop :=
  ∀j:Fin M,j.val < i→s.natHeap (P+2*j.val) = some (E j).left ∧
    s.natHeap (P+2*j.val+1) = some (E j).right
def PairWidths (W i : ℕ) (s : State) : Prop := ∀ (j : ℕ), j < i → s.natHeap (W+j) = some 2
def Visited {M : ℕ} (E : Fin M→Edge) (i v : ℕ) : Prop :=
  ∃j:Fin M,j.val < i ∧ ((E j).left = v ∨ (E j).right = v)
instance instDecidableVisited {M : ℕ} (E : Fin M→Edge) (i v : ℕ) : Decidable (Visited E i v) :=
  inferInstanceAs (Decidable (∃j:Fin M,j.val < i ∧ ((E j).left = v ∨ (E j).right = v)))
def Markers {M : ℕ} (E : Fin M→Edge) (U r i : ℕ) (s : State) : Prop :=
  ∀ (v : ℕ), v < r → s.natHeap (U+v) = some (if Visited E i v then 1 else 0)
def pairStep (s : State) := setPC (applyBlock pairBody (setPC s 14)) 13
theorem pairStart_cursor {r M T P W U A : ℕ} {s : State}
    (h:Fixed r M T P W U A s) (hp:s.pc = 10) :
    PairCursor r M T P W U A 0 (applyBlock pairStart s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals simp [pairStart,applyBlock,Op.apply,writeNat,next,hp,
    h.header.radix,h.header.count,h.header.source,h.header.permutation,
    h.header.widths,h.header.markers,h.header.row,h.zero,h.one,h.two,h.three]
theorem pairStart_frame (s : State) : Frame s (applyBlock pairStart s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [pairStart,applyBlock,Op.apply,writeNat,next]
theorem pairStep_cursor {r M T P W U A i : ℕ} {s : State}
    (h:PairCursor r M T P W U A i s) :
    PairCursor r M T P W U A (i+1) (pairStep s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_,?_,?_⟩
  all_goals simp [pairStep,pairBody,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.radix,h.fixed.header.count,h.fixed.header.source,
    h.fixed.header.permutation,h.fixed.header.widths,h.fixed.header.markers,
    h.fixed.header.row,h.fixed.zero,h.fixed.one,h.fixed.two,h.fixed.three,
    h.index,h.permutationCount,h.blockCount,Nat.mul_add,Nat.add_assoc]
theorem pairStep_frame (s : State) : Frame s (pairStep s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [pairStep,pairBody,applyBlock,Op.apply,setPC,writeNat,next]
theorem pairStep_heap {r M T P W U A i : ℕ} {s : State}
    (E : Fin M→Edge) (hi:i < M) (h:PairCursor r M T P W U A i s) (src:Edges E T s) :
    (pairStep s).natHeap = Function.update
      (Function.update (Function.update (Function.update (Function.update s.natHeap
        (P+2*i) (some (E ⟨i,hi⟩).left)) (P+2*i+1) (some (E ⟨i,hi⟩).right))
        (U+(E ⟨i,hi⟩).left) (some 1)) (U+(E ⟨i,hi⟩).right) (some 1)) (W+i) (some 2) := by
  have hl: s.natHeap (T+3*i) = some (E ⟨i,hi⟩).left := (src ⟨i,hi⟩).1
  have hr: s.natHeap (T+3*i+1) = some (E ⟨i,hi⟩).right := (src ⟨i,hi⟩).2
  simp only [Nat.add_assoc] at hr
  simp [pairStep,pairBody,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.source,h.fixed.header.permutation,h.fixed.header.widths,
    h.fixed.header.markers,h.index,h.permutationCount,h.blockCount,
    h.fixed.one,h.fixed.two,h.fixed.three,Nat.add_assoc,Nat.mul_comm i 3,hl,hr]
theorem pairStep_bounded {r M T P W U A i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (h:PairCursor r M T P W U A i s) (hi:i < M)
    (src:Edges E T s) (hr:InRange r E) (hcap:2*M ≤ r)
    (hT:T+3*M ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ B)
    (hB:55 ≤ B) (hs:WordBound B s) : BoundedRuns program n x B s 20 (pairStep s) := by
  have first:=branch_runs program B n 854 841 14 33 x s
    (by rw [h.pc];exact pair_at) hs (by omega) (by omega)
  have cmp:s.natReg 854 < s.natReg 841:=by rw [h.index,h.fixed.header.count];exact hi
  simp only [cmp,ite_true] at first
  let v:=setPC s 14
  have hl: s.natHeap (T+3*i) = some (E ⟨i,hi⟩).left := (src ⟨i,hi⟩).1
  have hj: s.natHeap (T+3*i+1) = some (E ⟨i,hi⟩).right := (src ⟨i,hi⟩).2
  simp only [Nat.add_assoc] at hj
  have hleft: (E ⟨i,hi⟩).left < r := (hr ⟨i,hi⟩).1
  have hright: (E ⟨i,hi⟩).right < r := (hr ⟨i,hi⟩).2
  have rd:readable pairBody v:=by
    simp [readable,pairBody,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.source,h.index,h.fixed.one,h.fixed.three,Nat.add_assoc,Nat.mul_comm i 3,hl,hj]
  have pk:peak pairBody v ≤ B:=by
    simp [peak,pairBody,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.source,h.fixed.header.permutation,h.fixed.header.widths,
      h.fixed.header.markers,h.index,h.permutationCount,h.blockCount,
      h.fixed.one,h.fixed.two,h.fixed.three,Nat.add_assoc,Nat.mul_comm i 3,hl,hj]
    omega
  have body:=block_runs pairBody program 14 n B x v pairBody_code rfl first.final_bound
    (by change 14+18 ≤ B;omega) rd pk
  have pc:(applyBlock pairBody v).pc = 32:=by
    rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:=jump_runs program B n 13 x (applyBlock pairBody v)
    (by rw [pc];exact pair_jump) body.final_bound (by omega)
  simpa only [show pairBody.length = 18 from rfl,pairStep,v,Nat.add_assoc] using
    first.trans (body.trans last)

def Bank (P : ℕ) (values : List ℕ) (s : State) : Prop :=
  ∀(j : ℕ)(hj:j < values.length),s.natHeap (P+j) = some (values[j]'hj)
def pairedPrefix {M : ℕ} (E : Fin M→Edge) (i : ℕ) : List ℕ :=
  ((List.finRange M).take i).flatMap (fun j=>[(E j).left,(E j).right])
theorem pairedPrefix_zero {M : ℕ} (E : Fin M→Edge) : pairedPrefix E 0=[] := rfl
theorem pairedPrefix_end {M : ℕ} (E : Fin M→Edge) : pairedPrefix E M = paired E := by
  unfold pairedPrefix paired
  rw [List.take_of_length_le (by simp)]
theorem pairedPrefix_length {M : ℕ} (E : Fin M→Edge) (i : ℕ) (hi:i ≤ M) :
    (pairedPrefix E i).length = 2*i := by
  simp [pairedPrefix,List.length_flatMap,List.map_const',Nat.mul_comm,hi]
theorem pairedPrefix_succ {M : ℕ} (E : Fin M→Edge) (i : ℕ) (hi:i < M) :
    pairedPrefix E (i+1) = pairedPrefix E i++[(E ⟨i,hi⟩).left,(E ⟨i,hi⟩).right] := by
  simp only [pairedPrefix,List.take_succ_eq_append_getElem (show i < (List.finRange M).length by simpa using hi),List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getElem_finRange]
  congr 3

theorem pairBank_prefix {M P i : ℕ} (E : Fin M→Edge) (s : State)
    (hi:i ≤ M) (h:PairBank E P i s) : Bank P (pairedPrefix E i) s := by
  induction i with
  | zero => simp [Bank,pairedPrefix]
  | succ i ih =>
    have il:i < M:=by omega
    have bank:=ih (by omega) (by intro j hj;exact h j (by omega))
    intro j hj
    simp only [pairedPrefix_succ E i il] at hj ⊢
    by_cases jl:j < (pairedPrefix E i).length
    · simpa only [List.getElem_append_left jl] using bank j jl
    · have len:=pairedPrefix_length E i (by omega)
      have el:=h ⟨i,il⟩ (by simp)
      have hr:j-2*i < 2:=by simp only [List.length_append,List.length_cons,List.length_nil,len] at hj;omega
      interval_cases z:j-2*i
      · have he:j = 2*i:=by omega
        simpa [he,len] using el.1
      · have he:j = 2*i+1:=by omega
        simpa [he,len,Nat.add_assoc] using el.2

theorem pairWidths_bank (W i : ℕ) (s : State) (h:PairWidths W i s) :
    Bank W (List.replicate i 2) s := by
  intro j hj
  simpa using h j (by simpa using hj)

def Outside (P W U A r : ℕ) (s u : State) : Prop :=
  ∀a,(a < P ∨ P+r ≤ a)→(a < W ∨ W+r ≤ a)→(a < U ∨ U+r ≤ a)→(a < A ∨ A+4 ≤ a)→
    u.natHeap a = s.natHeap a
theorem outside_trans {P W U A r : ℕ} {s u v : State}
    (h:Outside P W U A r s u) (h':Outside P W U A r u v) : Outside P W U A r s v :=
  fun a hp hw hu ha=>(h' a hp hw hu ha).trans (h a hp hw hu ha)

theorem visited_zero {M : ℕ} (E : Fin M→Edge) (v : ℕ) : ¬Visited E 0 v := by
  rintro ⟨j,hj,_⟩;omega
theorem visited_succ {M : ℕ} (E : Fin M→Edge) (i v : ℕ) (hi:i < M) :
    Visited E (i+1) v ↔ Visited E i v ∨ (E ⟨i,hi⟩).left = v ∨ (E ⟨i,hi⟩).right = v := by
  constructor
  · rintro ⟨j,hj,hv⟩
    by_cases he:j.val = i
    · have je:j=⟨i,hi⟩:=Fin.ext he
      subst j;exact Or.inr hv
    · exact Or.inl ⟨j,by omega,hv⟩
  · rintro (h|h|h)
    · obtain ⟨j,hj,hv⟩:=h;exact ⟨j,by omega,hv⟩
    · exact ⟨⟨i,hi⟩,by simp,Or.inl h⟩
    · exact ⟨⟨i,hi⟩,by simp,Or.inr h⟩
theorem visited_end {M : ℕ} (E : Fin M→Edge) (v : ℕ) : Visited E M v ↔ v∈paired E := by
  simp only [Visited,paired_mem]
  constructor
  · rintro ⟨j,_,hv⟩;exact ⟨j,hv.imp Eq.symm Eq.symm⟩
  · rintro ⟨j,hv⟩;exact ⟨j,j.isLt,hv.imp Eq.symm Eq.symm⟩

theorem pairStep_banks {r M T P W U A i : ℕ} (E : Fin M→Edge) (s : State)
    (h:PairCursor r M T P W U A i s) (hi:i < M) (src:Edges E T s) (hr:InRange r E)
    (hcap:2*M ≤ r) (hP:P+r ≤ W) (hW:W+r ≤ U)
    (hp:PairBank E P i s) (hw:PairWidths W i s) (hu:Markers E U r i s) :
    PairBank E P (i+1) (pairStep s) ∧ PairWidths W (i+1) (pairStep s) ∧
    Markers E U r (i+1) (pairStep s) := by
  have heap:=pairStep_heap E hi h src
  have hl: (E ⟨i,hi⟩).left < r:=(hr ⟨i,hi⟩).1
  have hj: (E ⟨i,hi⟩).right < r:=(hr ⟨i,hi⟩).2
  refine ⟨?_,?_,?_⟩
  · intro j jh
    rw [heap]
    by_cases je:j.val = i
    · have he:j=⟨i,hi⟩:=Fin.ext je
      subst j;simp (disch:=omega)
    · have old:=hp j (by omega)
      simp (disch:=omega) [old.1,old.2]
  · intro j jh
    rw [heap]
    by_cases je:j = i
    · subst j;simp
    · simp (disch:=omega) [hw j (by omega)]
  · intro v vr
    rw [heap]
    by_cases vl:v = (E ⟨i,hi⟩).left
    · subst v
      have une : U+(E ⟨i,hi⟩).left ≠ U+(E ⟨i,hi⟩).right := by
        have hd := (E ⟨i,hi⟩).different;omega
      simp (disch:=omega) [visited_succ]
    · by_cases vj:v = (E ⟨i,hi⟩).right
      · subst v;simp (disch:=omega) [visited_succ]
      · have old:=hu v vr
        have vl' : (E ⟨i,hi⟩).left ≠ v := Ne.symm vl
        have vj' : (E ⟨i,hi⟩).right ≠ v := Ne.symm vj
        simp (disch:=omega) [vl',vj',visited_succ,old]

theorem pairStep_outside {r M T P W U A i : ℕ} (E : Fin M→Edge) (s : State)
    (h:PairCursor r M T P W U A i s) (hi:i < M) (src:Edges E T s) (hr:InRange r E)
    (hcap:2*M ≤ r) : Outside P W U A r s (pairStep s) := by
  intro a hp hw hu _
  have hl: (E ⟨i,hi⟩).left < r:=(hr ⟨i,hi⟩).1
  have hj: (E ⟨i,hi⟩).right < r:=(hr ⟨i,hi⟩).2
  rw [pairStep_heap E hi h src]
  simp (disch:=omega)

theorem edges_transport {M r T P W U A : ℕ} {E : Fin M→Edge} {s u : State}
    (src:Edges E T s) (out:Outside P W U A r s u)
    (hT:T+3*M ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) : Edges E T u := by
  intro i
  rw [out (T+3*i.val) (by omega) (by omega) (by omega) (by omega),
    out (T+3*i.val+1) (by omega) (by omega) (by omega) (by omega)]
  exact src i

theorem pair_loop {r M T P W U A i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (h:PairCursor r M T P W U A i s) (hi:i+remaining = M)
    (src:Edges E T s) (hr:InRange r E) (hcap:2*M ≤ r)
    (hT:T+3*M ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) (hA:A+4 ≤ B)
    (hp:PairBank E P i s) (hw:PairWidths W i s) (hu:Markers E U r i s)
    (hB:55 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (20*remaining) u ∧ PairCursor r M T P W U A M u ∧
    PairBank E P M u ∧ PairWidths W M u ∧ Markers E U r M u ∧
    Outside P W U A r s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i = M:=by omega
    subst i
    exact ⟨s,.refl hs,h,hp,hw,hu,fun _ _ _ _ _=>rfl,frame_refl s⟩
  | succ rem ih =>
    have il:i < M:=by omega
    have run:=pairStep_bounded B n x E s h il src hr hcap hT hP hW (by omega) hB hs
    obtain ⟨pb,pw,pm⟩:=pairStep_banks E s h il src hr hcap hP hW hp hw hu
    have out:=pairStep_outside E s h il src hr hcap
    obtain ⟨u,ru,uc,up,uw,um,uo,uf⟩:=ih (i:=i+1) (pairStep s) (pairStep_cursor h)
      (by omega) (edges_transport src out hT hP hW hU) pb pw pm run.final_bound
    refine ⟨u,?_,uc,up,uw,um,outside_trans out uo,frame_trans (pairStep_frame s) uf⟩
    convert run.trans ru using 1;omega

def singletonPrefix {M : ℕ} (E : Fin M→Edge) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun j=>decide (j∉paired E))
theorem singletonPrefix_zero {M : ℕ} (E : Fin M→Edge) : singletonPrefix E 0=[] := rfl
theorem singletonPrefix_end {M : ℕ} (r : ℕ) (E : Fin M→Edge) :
    singletonPrefix E r=singletons r E := rfl
theorem singletonPrefix_succ {M : ℕ} (E : Fin M→Edge) (i : ℕ) :
    singletonPrefix E (i+1)=singletonPrefix E i++(if i∉paired E then [i] else []) := by
  simp only [singletonPrefix,List.range_succ,List.filter_append,List.filter_cons,List.filter_nil]
  split_ifs <;> simp_all

theorem singletonPrefix_le {M : ℕ} (r : ℕ) (E : Fin M→Edge) (i : ℕ) (hi:i ≤ r) :
    (singletonPrefix E i).length ≤ (singletons r E).length :=
  (List.Sublist.filter _ (List.range_sublist.mpr hi)).length_le

def permutationPrefix {M : ℕ} (E : Fin M→Edge) (i : ℕ) := paired E++singletonPrefix E i
def widthPrefix {M : ℕ} (E : Fin M→Edge) (i : ℕ) :=
  List.replicate M 2++List.replicate (singletonPrefix E i).length 1

theorem prefix_lengths {M : ℕ} (E : Fin M→Edge) (i : ℕ) :
    (permutationPrefix E i).length=2*M+(singletonPrefix E i).length ∧
    (widthPrefix E i).length=M+(singletonPrefix E i).length := by
  simp [permutationPrefix,widthPrefix,paired_length]
theorem prefix_capacity {M : ℕ} (r : ℕ) (E : Fin M→Edge) (i : ℕ)
    (hi:i ≤ r) (hm:Matching E) (hr:InRange r E) :
    2*M+(singletonPrefix E i).length ≤ r := by
  have h:=singletonPrefix_le r E i hi
  have hc:=matching_capacity r E hm hr
  rw [singletons_length r E hm hr] at h
  omega

theorem bank_heap {P : ℕ} {vs : List ℕ} {s u : State} (h:Bank P vs s)
    (heap:u.natHeap=s.natHeap) : Bank P vs u := by simpa only [Bank,heap] using h

theorem bank_append_write {P Q : ℕ} {vs ws : List ℕ} {s u : State} (v w : ℕ)
    (hp:Bank P vs s) (hw:Bank Q ws s) (hQ:P+vs.length+1 ≤ Q)
    (heap:u.natHeap=Function.update (Function.update s.natHeap
      (P+vs.length) (some v)) (Q+ws.length) (some w)) :
    Bank P (vs++[v]) u ∧ Bank Q (ws++[w]) u := by
  constructor
  · intro j hj
    rw [heap]
    by_cases jl:j < vs.length
    · simp (disch:=omega) [List.getElem_append_left jl,hp j jl]
    · have je:j=vs.length:=by simp only [List.length_append,List.length_cons,List.length_nil] at hj;omega
      subst j;simp (disch:=omega)
  · intro j hj
    rw [heap]
    by_cases jl:j < ws.length
    · simp (disch:=omega) [List.getElem_append_left jl,hw j jl]
    · have je:j=ws.length:=by simp only [List.length_append,List.length_cons,List.length_nil] at hj;omega
      subst j;simp

structure SingletonCursor {M : ℕ} (r T P W U A : ℕ) (E : Fin M→Edge) (i : ℕ)
    (s : State) : Prop where
  fixed : Fixed r M T P W U A s
  pc : s.pc=34
  index : s.natReg 860=i
  permutationCount : s.natReg 855=2*M+(singletonPrefix E i).length
  blockCount : s.natReg 856=M+(singletonPrefix E i).length

def singletonStep (unused : Bool) (s : State) : State :=
  let v:=applyBlock singletonRead (setPC s 35)
  let w:=if unused then applyBlock singletonBody (setPC v 38) else setPC v 44
  setPC (applyBlock advance w) 34

theorem singletonStart_cursor {r M T P W U A : ℕ} {E : Fin M→Edge} {s : State}
    (h:PairCursor r M T P W U A M s) :
    SingletonCursor r T P W U A E 0 (applyBlock singletonStart (setPC s 33)) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals simp [singletonStart,applyBlock,Op.apply,writeNat,next,setPC,singletonPrefix,
    h.fixed.header.radix,h.fixed.header.count,h.fixed.header.source,h.fixed.header.permutation,
    h.fixed.header.widths,h.fixed.header.markers,h.fixed.header.row,
    h.fixed.zero,h.fixed.one,h.fixed.two,h.fixed.three,h.permutationCount,h.blockCount]
theorem singletonStart_frame (s : State) :
    Frame s (applyBlock singletonStart (setPC s 33)) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq;simp (disch:=omega) [singletonStart,applyBlock,Op.apply,writeNat,next,setPC]

theorem singletonStep_frame (unused : Bool) (s : State) : Frame s (singletonStep unused s) := by
  cases unused <;> refine ⟨rfl,rfl,rfl,rfl,?_⟩ <;> intro q hq <;>
    simp (disch:=omega) [singletonStep,singletonRead,singletonBody,advance,applyBlock,
      Op.apply,writeNat,next,setPC]
theorem singletonStep_cursor {r M T P W U A i : ℕ} {E : Fin M→Edge} {s : State}
    (h:SingletonCursor r T P W U A E i s) :
    SingletonCursor r T P W U A E (i+1) (singletonStep (decide (i∉paired E)) s) := by
  by_cases hu:i∉paired E
  all_goals
    refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    all_goals simp [singletonStep,singletonRead,singletonBody,advance,applyBlock,Op.apply,
      writeNat,next,setPC,hu,singletonPrefix_succ,
      h.fixed.header.radix,h.fixed.header.count,h.fixed.header.source,h.fixed.header.permutation,
      h.fixed.header.widths,h.fixed.header.markers,h.fixed.header.row,
      h.fixed.zero,h.fixed.one,h.fixed.two,h.fixed.three,h.index,h.permutationCount,h.blockCount,
      Nat.add_assoc]
theorem singletonStep_heap {r M T P W U A i : ℕ} {E : Fin M→Edge} {s : State}
    (h:SingletonCursor r T P W U A E i s) :
    (singletonStep (decide (i∉paired E)) s).natHeap =
    if i∉paired E then Function.update (Function.update s.natHeap
      (P+(permutationPrefix E i).length) (some i)) (W+(widthPrefix E i).length) (some 1)
    else s.natHeap := by
  by_cases hu:i∉paired E <;>
    simp [singletonStep,singletonRead,singletonBody,advance,applyBlock,Op.apply,
      writeNat,next,setPC,hu,h.fixed.header.permutation,h.fixed.header.widths,
      h.index,h.fixed.one,h.permutationCount,h.blockCount,prefix_lengths]

theorem singletonStep_banks {r M T P W U A i : ℕ} {E : Fin M→Edge} {s : State}
    (h:SingletonCursor r T P W U A E i s) (hi:i < r) (hm:Matching E) (hr:InRange r E)
    (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A)
    (hp:Bank P (permutationPrefix E i) s) (hw:Bank W (widthPrefix E i) s)
    (hu:Markers E U r M s) :
    Bank P (permutationPrefix E (i+1)) (singletonStep (decide (i∉paired E)) s) ∧
    Bank W (widthPrefix E (i+1)) (singletonStep (decide (i∉paired E)) s) ∧
    Markers E U r M (singletonStep (decide (i∉paired E)) s) ∧
    Outside P W U A r s (singletonStep (decide (i∉paired E)) s) := by
  have hc:=prefix_capacity r E (i+1) (by omega) hm hr
  have hl:=prefix_lengths E i
  have heap:=singletonStep_heap h
  by_cases unused:i∉paired E
  · have heap := heap.trans (ite_eq_left unused)
    have hlen:(singletonPrefix E (i+1)).length=(singletonPrefix E i).length+1 := by
      simp [singletonPrefix_succ,unused]
    have pb:=bank_append_write i 1 hp hw (by omega) heap
    have pnext:permutationPrefix E (i+1)=permutationPrefix E i++[i] := by
      simp [permutationPrefix,singletonPrefix_succ,unused,List.append_assoc]
    have wnext:widthPrefix E (i+1)=widthPrefix E i++[1] := by
      simp [widthPrefix,hlen,List.replicate_add,List.append_assoc]
    refine ⟨by simpa only [pnext] using pb.1,by simpa only [wnext] using pb.2,?_,?_⟩
    · intro v hv;rw [heap];simp (disch:=omega) [hu v hv]
    · intro a pa wa _ _;rw [heap];simp (disch:=omega)
  · have heap := heap.trans (ite_eq_right unused)
    have pnext:permutationPrefix E (i+1)=permutationPrefix E i := by
      simp [permutationPrefix,singletonPrefix_succ,unused]
    have wnext:widthPrefix E (i+1)=widthPrefix E i := by
      simp [widthPrefix,singletonPrefix_succ,unused]
    refine ⟨by simpa only [pnext] using bank_heap hp heap,
      by simpa only [wnext] using bank_heap hw heap,?_,?_⟩
    · simpa only [Markers,heap] using hu
    · intro a _ _ _ _;rw [heap]

theorem singletonStep_bounded {r M T P W U A i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (h:SingletonCursor r T P W U A E i s)
    (hi:i < r) (hm:Matching E) (hr:InRange r E)
    (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) (hA:A+4 ≤ B)
    (hu:Markers E U r M s) (hB:55 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s (if i∉paired E then 12 else 6)
      (singletonStep (decide (i∉paired E)) s) := by
  have first:=branch_runs program B n 860 840 35 46 x s
    (by rw [h.pc];exact singleton_at) hs (by omega) (by omega)
  have cmp:s.natReg 860 < s.natReg 840:=by rw [h.index,h.fixed.header.radix];exact hi
  simp only [cmp,ite_true] at first
  let v:=applyBlock singletonRead (setPC s 35)
  have marker:s.natHeap (U+i)=some (if i∈paired E then 1 else 0) := by
    simpa only [visited_end] using hu i hi
  have rd:readable singletonRead (setPC s 35):=by
    simp [readable,singletonRead,Op.readable,Op.apply,setPC,writeNat,next,
      h.fixed.header.markers,h.index,marker]
  have pk:peak singletonRead (setPC s 35) ≤ B:=by
    simp [peak,singletonRead,Op.peak,Op.apply,setPC,writeNat,next,
      h.fixed.header.markers,h.index,marker]
    split_ifs <;> omega
  have read:=block_runs singletonRead program 35 n B x (setPC s 35)
    singletonRead_code rfl first.final_bound (by change 35+2 ≤ B;omega) rd pk
  have vp:v.pc=37:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have val:v.natReg 861=(if i∈paired E then 1 else 0):=by
    simp [v,singletonRead,applyBlock,Op.apply,setPC,writeNat,next,
      h.fixed.header.markers,h.index,marker]
  have one:v.natReg 851=1:=by
    simp [v,singletonRead,applyBlock,Op.apply,setPC,writeNat,next,h.fixed.one]
  have used:=branch_runs program B n 861 851 38 44 x v
    (by rw [vp];exact used_at) read.final_bound (by omega) (by omega)
  by_cases unused:i∉paired E
  · have c:v.natReg 861 < v.natReg 851:=by simp [val,one,unused]
    simp only [c,ite_true] at used
    have hc:=prefix_capacity r E (i+1) (by omega) hm hr
    have hlen:(singletonPrefix E (i+1)).length=(singletonPrefix E i).length+1 := by
      simp [singletonPrefix_succ,unused]
    have br:readable singletonBody (setPC v 38):=by simp [readable,singletonBody,Op.readable]
    have bp:peak singletonBody (setPC v 38) ≤ B:=by
      simp [peak,singletonBody,Op.peak,Op.apply,v,singletonRead,applyBlock,setPC,
        writeNat,next,h.fixed.header.permutation,h.fixed.header.widths,
        h.permutationCount,h.blockCount,h.fixed.one,h.index]
      omega
    have body:=block_runs singletonBody program 38 n B x (setPC v 38)
      singletonBody_code rfl used.final_bound (by change 38+6 ≤ B;omega) br bp
    let w:=applyBlock singletonBody (setPC v 38)
    have wp:w.pc=44:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have ar:readable advance w:=by simp [readable,advance,Op.readable]
    have ap:peak advance w ≤ B:=by
      simp [peak,advance,Op.peak,Op.apply,w,singletonBody,v,singletonRead,
        applyBlock,setPC,writeNat,next,h.index,h.fixed.one];omega
    have arun:=block_runs advance program 44 n B x w advance_code wp body.final_bound
      (by change 44+1 ≤ B;omega) ar ap
    have endpc:(applyBlock advance w).pc=45:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
    have last:=jump_runs program B n 34 x (applyBlock advance w)
      (by rw [endpc];exact singleton_jump) arun.final_bound (by omega)
    simpa [unused,singletonStep,v,w,
      show singletonRead.length=2 from rfl,show singletonBody.length=6 from rfl,
      show advance.length=1 from rfl] using
      first.trans (read.trans (used.trans (body.trans (arun.trans last))))
  · have c:¬v.natReg 861 < v.natReg 851:=by simp [val,one,unused]
    simp only [c,ite_false] at used
    let w:=setPC v 44
    have ar:readable advance w:=by simp [readable,advance,Op.readable]
    have ap:peak advance w ≤ B:=by
      simp [peak,advance,Op.peak,Op.apply,w,v,singletonRead,
        applyBlock,setPC,writeNat,next,h.index,h.fixed.one];omega
    have arun:=block_runs advance program 44 n B x w advance_code rfl used.final_bound
      (by change 44+1 ≤ B;omega) ar ap
    have endpc:(applyBlock advance w).pc=45:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have last:=jump_runs program B n 34 x (applyBlock advance w)
      (by rw [endpc];exact singleton_jump) arun.final_bound (by omega)
    simpa [unused,singletonStep,v,w,
      show singletonRead.length=2 from rfl,show advance.length=1 from rfl] using
      first.trans (read.trans (used.trans (arun.trans last)))

theorem singleton_loop {r M T P W U A i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (h:SingletonCursor r T P W U A E i s)
    (hi:i+remaining=r) (hm:Matching E) (hr:InRange r E)
    (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) (hA:A+4 ≤ B)
    (hp:Bank P (permutationPrefix E i) s) (hw:Bank W (widthPrefix E i) s)
    (hu:Markers E U r M s) (hB:55 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s
      (6*remaining+6*((singletons r E).length-(singletonPrefix E i).length)) u ∧
    SingletonCursor r T P W U A E r u ∧ Bank P (ordered r E) u ∧
    Bank W (widths r M) u ∧ Markers E U r M u ∧ Outside P W U A r s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have eq:i=r:=by omega
    subst i
    refine ⟨s,?_,h,hp,?_,hu,fun _ _ _ _ _=>rfl,frame_refl s⟩
    · simpa only [singletonPrefix_end,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using BoundedRuns.refl hs
    · simpa only [widthPrefix,singletonPrefix_end,singletons_length r E hm hr,widths] using hw
  | succ rem ih =>
    have il:i < r:=by omega
    have run:=singletonStep_bounded B n x E s h il hm hr hP hW hU hA hu hB hs
    obtain ⟨pb,pw,pm,out⟩:=singletonStep_banks h il hm hr hP hW hU hp hw hu
    obtain ⟨u,ru,uc,up,uw,um,uo,uf⟩:=ih (i:=i+1)
      (singletonStep (decide (i∉paired E)) s) (singletonStep_cursor h) (by omega)
      pb pw pm run.final_bound
    refine ⟨u,?_,uc,up,uw,um,outside_trans out uo,
      frame_trans (singletonStep_frame _ s) uf⟩
    convert run.trans ru using 1
    have bound:=singletonPrefix_le r E (i+1) (by omega)
    by_cases unused:i∉paired E
    · have len:(singletonPrefix E (i+1)).length=(singletonPrefix E i).length+1:=by
        simp [singletonPrefix_succ,unused]
      simp [unused];omega
    · have len:(singletonPrefix E (i+1)).length=(singletonPrefix E i).length:=by
        simp [singletonPrefix_succ,unused]
      simp [unused];omega

def AxisRow (A r M W P : ℕ) (s : State) : Prop :=
  s.natHeap A=some (r-M) ∧ s.natHeap (A+1)=some W ∧
  s.natHeap (A+2)=some r ∧ s.natHeap (A+3)=some P

def finished (s : State) := applyBlock finish (setPC s 46)
theorem finished_pc (s : State) : (finished s).pc=54 := by
  rw [finished,UniformTensorMonomialMachine.applyBlock_pc];rfl

theorem finished_frame (s : State) : Frame s (finished s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq;simp (disch:=omega) [finished,finish,applyBlock,Op.apply,setPC,writeNat,next]

theorem finished_heap {r M T P W U A : ℕ} {E : Fin M→Edge} {s : State}
    (h:SingletonCursor r T P W U A E r s) (hm:Matching E) (hr:InRange r E) :
    (finished s).natHeap=Function.update (Function.update (Function.update
      (Function.update s.natHeap A (some (r-M))) (A+1) (some W)) (A+2) (some r)) (A+3) (some P) := by
  have cap:=matching_capacity r E hm hr
  have count:M+(singletonPrefix E r).length=r-M:=by
    rw [singletonPrefix_end,singletons_length r E hm hr];omega
  simp [finished,finish,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.row,h.fixed.header.radix,h.fixed.header.widths,h.fixed.header.permutation,
    h.fixed.zero,h.fixed.one,h.blockCount,count,Nat.add_assoc]

theorem finished_banks {r M T P W U A : ℕ} {E : Fin M→Edge} {s : State}
    (h:SingletonCursor r T P W U A E r s) (hm:Matching E) (hr:InRange r E)
    (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A)
    (hp:Bank P (ordered r E) s) (hw:Bank W (widths r M) s) (hu:Markers E U r M s) :
    Bank P (ordered r E) (finished s) ∧ Bank W (widths r M) (finished s) ∧
    Markers E U r M (finished s) ∧ AxisRow A r M W P (finished s) ∧
    Outside P W U A r s (finished s) := by
  have heap:=finished_heap h hm hr
  have cap:=matching_capacity r E hm hr
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j hj
    have jl:j < r:=by simpa only [ordered_length r E hm hr] using hj
    rw [heap];simp (disch:=omega) [hp j hj]
  · intro j hj
    have jl:j < r-M:=by simpa only [widths_length r M cap] using hj
    rw [heap];simp (disch:=omega) [hw j hj]
  · intro v hv;rw [heap];simp (disch:=omega) [hu v hv]
  · unfold AxisRow;rw [heap];simp
  · intro a _ _ _ ha;rw [heap];simp (disch:=omega)

theorem finished_bounded {r M T P W U A : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (h:SingletonCursor r T P W U A E r s)
    (hm:Matching E) (hr:InRange r E) (hA:A+4 ≤ B) (hB:55 ≤ B) (hs:WordBound B s) :
    BoundedExecution program n x B s 10 (finished s) := by
  have first:=branch_runs program B n 860 840 35 46 x s
    (by rw [h.pc];exact singleton_at) hs (by omega) (by omega)
  have cmp:¬s.natReg 860 < s.natReg 840:=by rw [h.index,h.fixed.header.radix];omega
  simp only [cmp,ite_false] at first
  have rB:r ≤ B:=by simpa only [h.fixed.header.radix] using hs.2.1 840
  have wB:W ≤ B:=by simpa only [h.fixed.header.widths] using hs.2.1 844
  have pB:P ≤ B:=by simpa only [h.fixed.header.permutation] using hs.2.1 843
  have cap:=matching_capacity r E hm hr
  have count:M+(singletonPrefix E r).length=r-M:=by
    rw [singletonPrefix_end,singletons_length r E hm hr];omega
  have rd:readable finish (setPC s 46):=by simp [readable,finish,Op.readable]
  have pk:peak finish (setPC s 46) ≤ B:=by
    simp [peak,finish,Op.peak,Op.apply,setPC,writeNat,next,
      h.fixed.header.row,h.fixed.header.radix,h.fixed.header.widths,h.fixed.header.permutation,
      h.fixed.zero,h.fixed.one,h.blockCount,count,Nat.add_assoc]
    constructor <;> omega
  have body:=block_runs finish program 46 n B x (setPC s 46) finish_code rfl first.final_bound
    (by change 46+8 ≤ B;omega) rd pk
  have halt:step program n x (finished s)=.halted (finished s):=by
    simp only [step,finished_pc,halt_at]
  simpa only [show finish.length=8 from rfl,finished] using
    first.executes (body.executes (BoundedExecution.halt body.final_bound halt))

/-- Literal initialized conversion of actual matching rows. Dirty marker, permutation,
width and axis-header banks are overwritten by charged instructions. -/
theorem execution (r M T P W U A B n : ℕ) (x : Fin n→ℂ) (E : Fin M→Edge) (s : State)
    (header:Header r M T P W U A s) (pc:s.pc=0) (src:Edges E T s)
    (hm:Matching E) (hr:InRange r E)
    (hT:T+3*M ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) (hA:A+4 ≤ B)
    (hB:55 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime r M) u ∧ u.pc=54 ∧
    Header r M T P W U A u ∧ Bank P (ordered r E) u ∧ Bank W (widths r M) u ∧
    Markers E U r M u ∧ AxisRow A r M W P u ∧ Edges E T u ∧
    Outside P W U A r s u ∧ Frame s u := by
  have cap:=matching_capacity r E hm hr
  obtain ⟨v,rv,vpc,vfix,vzero,vo,vf⟩:=initialized r M T P W U A B n x s
    header pc (by omega) hB hs
  have vsrc:Edges E T v:=by
    intro j
    rw [vo (T+3*j.val) (by omega),vo (T+3*j.val+1) (by omega)]
    exact src j
  have psread:readable pairStart v:=by simp [readable,pairStart,Op.readable]
  have pspeak:peak pairStart v ≤ B:=by simp [peak,pairStart,Op.peak]
  have start:=block_runs pairStart program 10 n B x v pairStart_code vpc rv.final_bound
    (by change 10+3 ≤ B;omega) psread pspeak
  let v':=applyBlock pairStart v
  have vmark:Markers E U r 0 v':=by
    intro j hj
    simpa only [v',pairStart,applyBlock,Op.apply,writeNat,next,visited_zero,ite_false]
      using vzero j hj
  obtain ⟨w,rw,wc,wp,ww,wm,wo,wf⟩:=pair_loop M B n x E v'
    (pairStart_cursor vfix vpc) (by omega) vsrc hr cap hT hP hW hU hA
    (by intro j hj;omega) (by intro j hj;omega) vmark hB start.final_bound
  have exit:=branch_runs program B n 854 841 14 33 x w
    (by rw [wc.pc];exact pair_at) rw.final_bound (by omega) (by omega)
  have cmp:¬w.natReg 854 < w.natReg 841:=by rw [wc.index,wc.fixed.header.count];omega
  simp only [cmp,ite_false] at exit
  have sr:readable singletonStart (setPC w 33):=by simp [readable,singletonStart,Op.readable]
  have sp:peak singletonStart (setPC w 33) ≤ B:=by simp [peak,singletonStart,Op.peak]
  have single:=block_runs singletonStart program 33 n B x (setPC w 33)
    singletonStart_code rfl exit.final_bound (by change 33+1 ≤ B;omega) sr sp
  let z:=applyBlock singletonStart (setPC w 33)
  have zp:Bank P (permutationPrefix E 0) z:=by
    simpa only [permutationPrefix,singletonPrefix_zero,List.append_nil,pairedPrefix_end]
      using bank_heap (pairBank_prefix E w (by omega) wp) (show z.natHeap=w.natHeap from rfl)
  have zw:Bank W (widthPrefix E 0) z:=by
    simpa only [widthPrefix,singletonPrefix_zero,List.length_nil,List.replicate_zero,List.append_nil]
      using bank_heap (pairWidths_bank W M w ww) (show z.natHeap=w.natHeap from rfl)
  obtain ⟨u,ru,uc,up,uw,um,uo,uf⟩:=singleton_loop r B n x E z
    (singletonStart_cursor wc) (by omega) hm hr hP hW hU hA zp zw wm hB single.final_bound
  have last:=finished_bounded B n x E u uc hm hr hA hB ru.final_bound
  obtain ⟨fp,fw,fm,fa,fo⟩:=finished_banks uc hm hr hP hW hU up uw um
  have framed:Frame s (finished u):=
    frame_trans vf (frame_trans (pairStart_frame v) (frame_trans wf
      (frame_trans (singletonStart_frame w) (frame_trans uf (finished_frame u)))))
  have outside:Outside P W U A r s (finished u):=by
    apply outside_trans (s:=s) (u:=v')
    · intro a _ _ ha _;exact vo a ha
    · exact outside_trans wo (outside_trans (s:=w) (u:=z)
        (fun _ _ _ _ _=>rfl) (outside_trans uo fo))
  refine ⟨finished u,?_,finished_pc u,?_,fp,fw,fm,fa,
    edges_transport src outside hT hP hW hU,outside,framed⟩
  · convert rv.executes (start.executes (rw.executes (exit.executes
      (single.executes (ru.executes last)))) ) using 1
    simp only [runtime,show pairStart.length=3 from rfl,show singletonStart.length=1 from rfl,
      singletonPrefix_zero,List.length_nil,Nat.sub_zero,singletons_length r E hm hr]
    omega
  · exact ⟨(framed.2.2.2.2 840 (Or.inl (by omega))).trans header.radix,
      (framed.2.2.2.2 841 (Or.inl (by omega))).trans header.count,
      (framed.2.2.2.2 842 (Or.inl (by omega))).trans header.source,
      (framed.2.2.2.2 843 (Or.inl (by omega))).trans header.permutation,
      (framed.2.2.2.2 844 (Or.inl (by omega))).trans header.widths,
      (framed.2.2.2.2 845 (Or.inl (by omega))).trans header.markers,
      (framed.2.2.2.2 846 (Or.inl (by omega))).trans header.row⟩

def physicalAxis {M : ℕ} (r W P : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (hpos:2 ≤ r) : UniformSectorPackingMachine.PhysicalAxis :=
  ⟨geometry r E hm hr hpos,W,P⟩

/-- The produced four-word row, widths and forward entries use the concrete ordered
matching permutation expected by the sector-packing interpreter. -/
theorem physical_axis {r M W P A : ℕ} (E : Fin M→Edge) (s : State)
    (hm:Matching E) (hr:InRange r E) (hpos:2 ≤ r)
    (row:AxisRow A r M W P s) (wp:Bank P (ordered r E) s) (ww:Bank W (widths r M) s) :
    UniformSectorPackingMachine.Rows [physicalAxis r W P E hm hr hpos] 0 A s ∧
    UniformSectorPackingMachine.Widths [physicalAxis r W P E hm hr hpos] s ∧
    UniformSectorPackingMachine.Permutations [physicalAxis r W P E hm hr hpos] s := by
  have cap:=matching_capacity r E hm hr
  refine ⟨?_,?_,?_⟩
  · change s.natHeap A=some (widths r M).length ∧ s.natHeap (A+1)=some W ∧
      s.natHeap (A+2)=some (widths r M).sum ∧ s.natHeap (A+3)=some P ∧ True
    rw [widths_length r M cap,widths_sum r M cap]
    exact ⟨row.1,row.2.1,row.2.2.1,row.2.2.2,True.intro⟩
  · intro a ha j
    have eq:a=physicalAxis r W P E hm hr hpos:=by simpa using ha
    subst a
    exact ww j.val j.isLt
  · intro a ha j
    have eq:a=physicalAxis r W P E hm hr hpos:=by simpa using ha
    subst a
    simp only [physicalAxis] at j ⊢
    change s.natHeap (P+j.val)=some ((geometry r E hm hr hpos).originalPermutation j).val
    rw [geometry_permutation]
    exact wp j.val (by
      rw [ordered_length r E hm hr]
      have jl:=j.isLt
      change j.val < (widths r M).sum at jl
      simpa only [widths_sum r M cap] using jl)

theorem execution_axis (r M T P W U A B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (s : State) (header:Header r M T P W U A s) (pc:s.pc=0)
    (src:Edges E T s) (hm:Matching E) (hr:InRange r E) (hpos:2 ≤ r)
    (hT:T+3*M ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ U) (hU:U+r ≤ A) (hA:A+4 ≤ B)
    (hB:55 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime r M) u ∧ runtime r M ≤ 21*r+21 ∧ u.pc=54 ∧
    UniformSectorPackingMachine.Rows [physicalAxis r W P E hm hr hpos] 0 A u ∧
    UniformSectorPackingMachine.Widths [physicalAxis r W P E hm hr hpos] u ∧
    UniformSectorPackingMachine.Permutations [physicalAxis r W P E hm hr hpos] u ∧
    Header r M T P W U A u ∧ Edges E T u ∧ Outside P W U A r s u ∧ Frame s u := by
  obtain ⟨u,run,upc,uh,wp,ww,_marker,row,src',out,fr⟩:=
    execution r M T P W U A B n x E s header pc src hm hr hT hP hW hU hA hB hs
  obtain ⟨rows,widths',perm⟩:=physical_axis E u hm hr hpos row wp ww
  exact ⟨u,run,runtime_linear r M (matching_capacity r E hm hr),upc,rows,widths',perm,
    uh,src',out,fr⟩

end
end ExactFourierCircuits.UniformMatchingAxisTableMachine
