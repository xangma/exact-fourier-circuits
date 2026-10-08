import UniformTensorMonomialMachine
import UniformColoring
import UniformRadixInstructionMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGreedyColorMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformColoring

/-- Nat800 = count,801 = three-word endpoint rows,802 = fresh color bank,
803 = fresh palette scratch. Only Nat810..823 are scratch. Palette11 is the
sentinel color; its scratch cell is allocated but never read by selection. -/
def boot : List Op := [.literal 810 0,.literal 811 1,.literal 812 3,
  .literal 813 11,.literal 814 0]
def clearStart : List Op := [.literal 816 0]
def clearBody : List Op := [.add 817 803 816,.putNat 817 810,.add 816 816 811]
def current : List Op := [.mul 817 814 812,.add 817 801 817,.getNat 818 817,
  .add 817 817 811,.getNat 819 817,.literal 815 0]
def previous : List Op := [.mul 817 815 812,.add 817 801 817,.getNat 820 817,
  .add 817 817 811,.getNat 821 817]
def advance : List Op := [.add 815 815 811]
def mark : List Op := [.add 817 802 815,.getNat 822 817,.add 817 803 822,.putNat 817 811]
def chooseStart : List Op := [.literal 816 0]
def chooseRead : List Op := [.add 817 803 816,.getNat 823 817]
def chooseNext : List Op := [.add 816 816 811]
def commit : List Op := [.add 817 802 814,.putNat 817 816,.add 814 814 811]
def program : Program := boot.map Op.code ++ [.branchLT 814 800 6 50] ++
  clearStart.map Op.code ++ [.branchLT 816 813 8 12] ++ clearBody.map Op.code ++
  [.jump 7] ++ current.map Op.code ++ [.branchLT 815 814 19 39] ++
  previous.map Op.code ++
  [.branchLT 820 818 26 25,.branchLT 818 820 26 34,
   .branchLT 820 819 28 27,.branchLT 819 820 28 34,
   .branchLT 821 818 30 29,.branchLT 818 821 30 34,
   .branchLT 821 819 32 31,.branchLT 819 821 32 34] ++
  advance.map Op.code ++ [.jump 18] ++ mark.map Op.code ++ [.jump 32] ++
  chooseStart.map Op.code ++ [.branchLT 816 813 41 46] ++ chooseRead.map Op.code ++
  [.branchLT 823 811 46 44] ++ chooseNext.map Op.code ++ [.jump 40] ++
  commit.map Op.code ++ [.jump 5,.halt]
theorem program_length : program.length = 51 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem clearStart_code : BlockAt clearStart program 6 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem clearBody_code : BlockAt clearBody program 8 := by
  intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem current_code : BlockAt current program 12 := by
  intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem previous_code : BlockAt previous program 19 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advance program 32 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem mark_code : BlockAt mark program 34 := by
  intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem chooseStart_code : BlockAt chooseStart program 39 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem chooseRead_code : BlockAt chooseRead program 41 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem chooseNext_code : BlockAt chooseNext program 44 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem commit_code : BlockAt commit program 46 := by
  intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem outer_at : program[5]?=some (.branchLT 814 800 6 50) := rfl
theorem clear_at : program[7]?=some (.branchLT 816 813 8 12) := rfl
theorem clear_jump : program[11]?=some (.jump 7) := rfl
theorem scan_at : program[18]?=some (.branchLT 815 814 19 39) := rfl
theorem scan_jump : program[33]?=some (.jump 18) := rfl
theorem mark_jump : program[38]?=some (.jump 32) := rfl
theorem choose_at : program[40]?=some (.branchLT 816 813 41 46) := rfl
theorem available_at : program[43]?=some (.branchLT 823 811 46 44) := rfl
theorem choose_jump : program[45]?=some (.jump 40) := rfl
theorem outer_jump : program[49]?=some (.jump 5) := rfl
theorem halt_at : program[50]?=some .halt := rfl
def runtimeBudget (M : ℕ) := 200*(M+1)^2

noncomputable section
structure Header (M T C U : ℕ) (s : State) : Prop where
  count : s.natReg 800 = M
  rows : s.natReg 801 = T
  colors : s.natReg 802 = C
  palette : s.natReg 803 = U
structure Fixed (M T C U : ℕ) (s : State) : Prop where
  header : Header M T C U s
  zero : s.natReg 810 = 0
  one : s.natReg 811 = 1
  three : s.natReg 812 = 3
  limit : s.natReg 813 = 11
def Edges {M : ℕ} (E : Fin M→Edge) (T : ℕ) (s : State) : Prop :=
  ∀i:Fin M,s.natHeap (T+3*i.val) = some (E i).left ∧
    s.natHeap (T+3*i.val+1) = some (E i).right
def Colors {M : ℕ} (E : Fin M→Edge) (C j : ℕ) (s : State) : Prop :=
  ∀i:Fin M,i.val < j→s.natHeap (C+i.val) = some (greedy E 11 j i.val)
def Frame (s u : State) : Prop := u.scalarHeap = s.scalarHeap ∧
  u.scalarReg = s.scalarReg ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧
  (∀r,(r < 810 ∨ 824 ≤ r)→u.natReg r = s.natReg r)
def Outside (C M U : ℕ) (s u : State) : Prop :=
  ∀a,(a < C ∨ C+M ≤ a)→(a < U ∨ U+12 ≤ a)→u.natHeap a = s.natHeap a
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

/-- No degree assumption is needed for termination: exhausted palettes return 11. -/
theorem firstFree_le (K : ℕ) (used : Finset ℕ) : firstFree K used ≤ K := by
  cases hf:(List.range K).find? (fun c=>decide (c∉used)) with
  | none => simp only [firstFree,hf,Option.getD_none,le_refl]
  | some c =>
    have hm:=List.mem_of_find?_eq_some hf
    simp only [firstFree,hf,Option.getD_some]
    exact Nat.le_of_lt (List.mem_range.mp hm)

theorem greedy_le {M : ℕ} (E : Fin M→Edge) (j i : ℕ) : greedy E 11 j i ≤ 11 := by
  induction j with
  | zero => simp [greedy]
  | succ j ih =>
    by_cases hj:j < M
    · rw [greedy_next E 11 j hj]
      by_cases he:i = j
      · subst i;simpa using firstFree_le 11 (earlierColors E ⟨j,hj⟩ (greedy E 11 j))
      · simpa [he] using ih
    · simpa [greedy,hj] using ih

theorem firstFree_of_prefix (used : Finset ℕ) (c : ℕ) (hc:c ≤ 11)
    (hp:∀a,a < c→a∈used) (ha:c < 11→c∉used) : firstFree 11 used = c := by
  by_cases hl:c < 11
  · have hf:(List.range 11).find? (fun a=>decide (a∉used)) = some c:=by
      simp only [List.find?_range_eq_some]
      exact ⟨by simp [ha hl],by simpa using hl,fun a hac=>by simp [hp a hac]⟩
    simp only [firstFree,hf,Option.getD_some]
  · have he:c = 11:=by omega
    have hf:(List.range 11).find? (fun a=>decide (a∉used)) = none:=by
      apply List.find?_eq_none.mpr
      intro a ham;simp [hp a (by have hm:=List.mem_range.mp ham;omega)]
    simp only [firstFree,hf,Option.getD_none,he]

def scanned {M : ℕ} (E : Fin M→Edge) (here : Fin M) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun h:Fin M=>h.val < i ∧ Conflict (E here) (E h))).image
    (fun h=>greedy E 11 here.val h.val)
theorem scanned_zero {M : ℕ} (E : Fin M→Edge) (here : Fin M) : scanned E here 0=∅ := by
  simp [scanned]
theorem scanned_end {M : ℕ} (E : Fin M→Edge) (here : Fin M) :
    scanned E here here.val = earlierColors E here (greedy E 11 here.val) := rfl

theorem scanned_succ {M : ℕ} (E : Fin M→Edge) (here : Fin M) (i : ℕ) (hi:i < M) :
    scanned E here (i+1) = if Conflict (E here) (E ⟨i,hi⟩) then
      insert (greedy E 11 here.val i) (scanned E here i) else scanned E here i := by
  classical
  have hf:(Finset.univ.filter (fun h:Fin M=>h.val < i+1 ∧ Conflict (E here) (E h)))=
      if Conflict (E here) (E ⟨i,hi⟩) then
        insert ⟨i,hi⟩ (Finset.univ.filter (fun h:Fin M=>h.val < i ∧ Conflict (E here) (E h)))
      else Finset.univ.filter (fun h:Fin M=>h.val < i ∧ Conflict (E here) (E h)):=by
    ext h
    by_cases he:h.val = i
    · have hh:h=⟨i,hi⟩:=Fin.ext he
      subst h;split <;> simp_all
    · have hn:h≠⟨i,hi⟩:=by intro hh;exact he (congrArg Fin.val hh)
      have hl:h.val < i+1 ↔ h.val < i:=by omega
      split <;> simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and,hn,false_or] <;> rw [hl]
  unfold scanned
  rw [hf]
  split <;> simp

/-- A straight-line block is scratch-only and integer-only. -/
def Allowed : Op→Prop
  | .literal r _ | .add r _ _ | .sub r _ _ | .mul r _ _ | .getNat r _ => 810 ≤ r ∧ r < 824
  | .putNat _ _ => True
  | _ => False

theorem op_frame (o : Op) (s : State) (h:Allowed o) : Frame s (o.apply s) := by
  cases o <;> simp only [Allowed] at h
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [Op.apply,writeNat,next]

theorem block_frame (b : List Op) (s : State) (h:∀o∈b,Allowed o) : Frame s (applyBlock b s) := by
  induction b generalizing s with
  | nil => exact frame_refl s
  | cons o b ih =>
    exact frame_trans (op_frame o s (h o (by simp)))
      (ih (o.apply s) (by intro v hv;exact h v (by simp [hv])))

theorem frame_setPC (s : State) (pc : ℕ) : Frame s (setPC s pc) :=
  ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

theorem branch_bounded (a b yes no B n : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:program[s.pc]?=some (.branchLT a b yes no))
    (hy:yes ≤ B) (hn:no ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 1 (setPC s (if s.natReg a < s.natReg b then yes else no)) := by
  exact .next hs (by simp [step,hc,setPC])
    (.refl (changePC_bound B s _ hs (by split <;> assumption)))

theorem jump_bounded (pc B n : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:program[s.pc]?=some (.jump pc)) (hp:pc ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 1 (setPC s pc) :=
  .next hs (by simp [step,hc,setPC]) (.refl (changePC_bound B s pc hs hp))

theorem outside_trans {C M U : ℕ} {s u v : State}
    (h:Outside C M U s u) (h':Outside C M U u v) : Outside C M U s v :=
  fun a ha hu=>(h' a ha hu).trans (h a ha hu)
theorem edges_transport {M T C U : ℕ} {E : Fin M→Edge} {s u : State}
    (h:Edges E T s) (hout:Outside C M U s u) (hT:T+3*M ≤ C) (hC:C+M ≤ U) : Edges E T u := by
  intro i
  rw [hout (T+3*i.val) (by omega) (by omega),hout (T+3*i.val+1) (by omega) (by omega)]
  exact h i

theorem colors_palette_transport {M C U j : ℕ} {E : Fin M→Edge} {s u : State}
    (h:Colors E C j s) (hout:∀a,a < U ∨ U+12 ≤ a→u.natHeap a = s.natHeap a)
    (hC:C+M ≤ U) : Colors E C j u := by
  intro i hi
  rw [hout (C+i.val) (by omega)]
  exact h i hi

structure OuterCursor (M T C U j : ℕ) (s : State) : Prop where
  fixed : Fixed M T C U s
  pc : s.pc = 5
  index : s.natReg 814 = j
structure ClearCursor (M T C U j c : ℕ) (s : State) : Prop where
  fixed : Fixed M T C U s
  pc : s.pc = 7
  index : s.natReg 814 = j
  color : s.natReg 816 = c

def Palette (U : ℕ) (used : Finset ℕ) (s : State) : Prop :=
  ∀c,c < 11→s.natHeap (U+c) = some (if c∈used then 1 else 0)
def Zeros (U c : ℕ) (s : State) : Prop := ∀a,a < c→s.natHeap (U+a) = some 0

def clearStep (s : State) := setPC (applyBlock clearBody (setPC s 8)) 7

theorem clearStep_cursor {M T C U j c : ℕ} {s : State} (h:ClearCursor M T C U j c s) :
    ClearCursor M T C U j (c+1) (clearStep s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_,?_⟩
  all_goals simp [clearStep,clearBody,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,h.color]

theorem clearStep_heap {M T C U j c : ℕ} {s : State} (h:ClearCursor M T C U j c s) :
    (clearStep s).natHeap = Function.update s.natHeap (U+c) (some 0) := by
  simp [clearStep,clearBody,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.palette,h.fixed.zero,h.fixed.one,h.color]

theorem clearStep_frame (s : State) : Frame s (clearStep s) := by
  exact frame_trans (frame_setPC s 8) (frame_trans
    (block_frame clearBody _ (by simp [clearBody,Allowed])) (frame_setPC _ 7))

theorem clearStep_bounded {M T C U j c : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:ClearCursor M T C U j c s) (hc:c < 11)
    (hB:51 ≤ B) (hU:U+12 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (clearStep s) := by
  let v:=setPC s 8
  have enter:BoundedRuns program n x B s 1 v:=by
    simpa [h.pc,clear_at,h.color,h.fixed.limit,hc,v] using
      branch_bounded 816 813 8 12 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have run:=block_runs clearBody program 8 n B x v clearBody_code rfl enter.final_bound
    (by change 8+3 ≤ B;omega) (by simp [readable,clearBody,Op.readable])
    (by simp [peak,clearBody,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.palette,h.fixed.zero,h.fixed.one,h.color];omega)
  have ipc:(applyBlock clearBody v).pc = 11:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:=jump_bounded 7 B n x (applyBlock clearBody v) (by rw [ipc];rfl)
    (by omega) run.final_bound
  exact enter.trans (run.trans last)

theorem clear_loop {M T C U j c : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:ClearCursor M T C U j c s) (hc:c+remaining = 11)
    (hz:Zeros U c s) (hB:51 ≤ B) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*remaining) u ∧ ClearCursor M T C U j 11 u ∧
    Palette U ∅ u ∧ (∀a,a < U ∨ U+12 ≤ a→u.natHeap a = s.natHeap a) ∧ Frame s u := by
  induction remaining generalizing c s with
  | zero =>
    have he:c = 11:=by omega
    subst c
    exact ⟨s,.refl hs,h,by simpa [Palette,Zeros] using hz,fun _ _=>rfl,frame_refl s⟩
  | succ r ih =>
    have run:=clearStep_bounded B n x s h (by omega) hB hU hs
    have hh:=clearStep_heap h
    have nz:Zeros U (c+1) (clearStep s):=by
      intro a ha;rw [hh]
      by_cases he:a = c
      · subst a;simp
      · simp (disch:=omega) [hz a (by omega)]
    obtain ⟨u,ru,cu,pu,ou,fu⟩:=ih (c:=c+1) (clearStep s) (clearStep_cursor h)
      (by omega) nz run.final_bound
    refine ⟨u,?_,cu,pu,?_,frame_trans (clearStep_frame s) fu⟩
    · convert run.trans ru using 1;omega
    · intro a ha;rw [ou a ha,hh];simp (disch:=omega)

def testLeft (i : ℕ) := if i < 2 then 820 else 821
def testRight (i : ℕ) := if i%2 = 0 then 818 else 819
def matchesFrom (s : State) : ℕ→ℕ→Prop
  | _,0=>False
  | i,r+1=>s.natReg (testLeft i) = s.natReg (testRight i) ∨ matchesFrom s (i+1) r

instance matchesFrom_decidable (s : State) (i r : ℕ) : Decidable (matchesFrom s i r) := by
  induction r generalizing i with
  | zero => unfold matchesFrom;infer_instance
  | succ r ih => unfold matchesFrom;exact instDecidableOr

theorem matches_pc (s : State) (pc i r : ℕ) : matchesFrom (setPC s pc) i r = matchesFrom s i r := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih => simp only [matchesFrom,ih];rfl

theorem test_code (i : ℕ) (hi:i < 4) :
    program[24+2*i]?=some (.branchLT (testLeft i) (testRight i) (26+2*i) (25+2*i)) ∧
    program[25+2*i]?=some (.branchLT (testRight i) (testLeft i) (26+2*i) 34) := by
  interval_cases i <;> exact ⟨rfl,rfl⟩

/-- Equality is physically tested with one or two integer comparisons. -/
theorem eqTest_bounded (i B n : ℕ) (x : Fin n→ℂ) (s : State) (hi:i < 4)
    (hp:s.pc = 24+2*i) (hB:51 ≤ B) (hs:WordBound B s) : ∃t,
    t ≤ 2 ∧ BoundedRuns program n x B s t
      (setPC s (if s.natReg (testLeft i) = s.natReg (testRight i) then 34 else 26+2*i)) := by
  classical
  obtain ⟨c0,c1⟩:=test_code i hi
  have run:=branch_bounded (testLeft i) (testRight i) (26+2*i) (25+2*i) B n x s
    (by rw [hp];exact c0) (by omega) (by omega) hs
  by_cases hl:s.natReg (testLeft i) < s.natReg (testRight i)
  · have he:s.natReg (testLeft i) ≠ s.natReg (testRight i):=by omega
    exact ⟨1,by omega,by simpa [hl,he] using run⟩
  · have ent:BoundedRuns program n x B s 1 (setPC s (25+2*i)):=by simpa [hl] using run
    have run1:=branch_bounded (testRight i) (testLeft i) (26+2*i) 34 B n x
      (setPC s (25+2*i)) c1 (by omega) (by omega) ent.final_bound
    refine ⟨2,by omega,?_⟩
    by_cases he:s.natReg (testLeft i) = s.natReg (testRight i)
    · have hn:¬s.natReg (testRight i) < s.natReg (testLeft i):=by omega
      simpa [setPC,he,hn] using ent.trans run1
    · have hg:s.natReg (testRight i) < s.natReg (testLeft i):=by omega
      simpa [setPC,he,hg] using ent.trans run1

theorem tests_bounded (i remaining B n : ℕ) (x : Fin n→ℂ) (s : State)
    (hi:i+remaining = 4) (hp:s.pc = 24+2*i) (hB:51 ≤ B) (hs:WordBound B s) : ∃t,
    t ≤ 2*remaining ∧ BoundedRuns program n x B s t
      (setPC s (if matchesFrom s i remaining then 34 else 32)) := by
  classical
  induction remaining generalizing i s with
  | zero =>
    have ii:i = 4:=by omega
    have he:setPC s 32 = s:=by simp only [setPC];cases s;simp_all
    exact ⟨0,by omega,by simpa [matchesFrom,he] using BoundedRuns.refl hs⟩
  | succ r ih =>
    obtain ⟨t,ht,run⟩:=eqTest_bounded i B n x s (by omega) hp hB hs
    by_cases he:s.natReg (testLeft i) = s.natReg (testRight i)
    · exact ⟨t,by omega,by simpa [matchesFrom,he] using run⟩
    · have ent:BoundedRuns program n x B s t (setPC s (26+2*i)):=by simpa [he] using run
      obtain ⟨v,hv,tail⟩:=ih (i+1) (setPC s (26+2*i)) (by omega)
        (by simp [setPC];omega) ent.final_bound
      refine ⟨t+v,by omega,?_⟩
      have tr:=ent.trans tail
      simp only [matches_pc] at tr
      simpa [matchesFrom,he,setPC] using tr

structure ScanCursor {M : ℕ} (T C U : ℕ) (E : Fin M→Edge) (here : Fin M) (i : ℕ)
    (s : State) : Prop where
  fixed : Fixed M T C U s
  pc : s.pc = 18
  index : s.natReg 814 = here.val
  previous : s.natReg 815 = i
  left : s.natReg 818 = (E here).left
  right : s.natReg 819 = (E here).right

theorem startup (M T C U B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Header M T C U s) (hp:s.pc = 0) (hB:51 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (applyBlock boot s) ∧
    OuterCursor M T C U 0 (applyBlock boot s) ∧
    (applyBlock boot s).natHeap = s.natHeap ∧ Frame s (applyBlock boot s) := by
  refine ⟨block_runs boot program 0 n B x s boot_code hp hs (by change 0+5 ≤ B;omega)
    (by simp [readable,boot,Op.readable]) (by simp [peak,boot,Op.peak];omega),?_,rfl,?_⟩
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals simp [boot,applyBlock,Op.apply,writeNat,next,hp,
      h.count,h.rows,h.colors,h.palette]
  · exact block_frame boot s (by simp [boot,Allowed])

theorem clear_begin {M T C U j : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:OuterCursor M T C U j s) (hj:j < M) (hB:51 ≤ B) (hs:WordBound B s) :
    ∃u,BoundedRuns program n x B s 2 u ∧ ClearCursor M T C U j 0 u ∧
    u.natHeap = s.natHeap ∧ Frame s u := by
  let v:=setPC s 6
  have ent:BoundedRuns program n x B s 1 v:=by
    simpa [h.index,h.fixed.header.count,hj,v] using
      branch_bounded 814 800 6 50 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have run:=block_runs clearStart program 6 n B x v clearStart_code rfl ent.final_bound
    (by change 6+1 ≤ B;omega) (by simp [readable,clearStart,Op.readable])
    (by simp [peak,clearStart,Op.peak])
  refine ⟨applyBlock clearStart v,ent.trans run,?_,rfl,?_⟩
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_⟩
    all_goals simp [v,clearStart,applyBlock,Op.apply,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index]
  · exact frame_trans (frame_setPC s 6) (block_frame clearStart _ (by simp [clearStart,Allowed]))

theorem current_begin {M T C U j : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (E : Fin M→Edge) (h:ClearCursor M T C U j 11 s) (hj:j < M) (hed:Edges E T s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) :
    ∃u,BoundedRuns program n x B s 7 u ∧ ScanCursor T C U E ⟨j,hj⟩ 0 u ∧
    u.natHeap = s.natHeap ∧ Frame s u := by
  let v:=setPC s 12
  have ent:BoundedRuns program n x B s 1 v:=by
    simpa [h.color,h.fixed.limit,v] using
      branch_bounded 816 813 8 12 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have he0:=hed ⟨j,hj⟩
  have he:s.natHeap (T+j*3) = some (E ⟨j,hj⟩).left ∧
      s.natHeap (T+j*3+1) = some (E ⟨j,hj⟩).right:=by simpa [Nat.mul_comm] using he0
  have bl:(E ⟨j,hj⟩).left ≤ B:=(hs.2.2.1 _ _ he.1).2
  have br:(E ⟨j,hj⟩).right ≤ B:=(hs.2.2.1 _ _ he.2).2
  have run:=block_runs current program 12 n B x v current_code rfl ent.final_bound
    (by change 12+6 ≤ B;omega)
    (by simp [readable,current,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.rows,h.fixed.three,h.fixed.one,h.index,he.1,he.2])
    (by simp [peak,current,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.rows,h.fixed.three,h.fixed.one,h.index,he.1,he.2];omega)
  refine ⟨applyBlock current v,ent.trans run,?_,rfl,?_⟩
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
    all_goals simp [current,applyBlock,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,he.1,he.2]
  · exact frame_trans (frame_setPC s 12) (block_frame current _ (by simp [current,Allowed]))

def scanStep {M : ℕ} (E : Fin M→Edge) (here prior : Fin M) (s : State) :=
  let p:=applyBlock previous (setPC s 19)
  let tested:=setPC p (if Conflict (E here) (E prior) then 34 else 32)
  let marked:=if Conflict (E here) (E prior) then setPC (applyBlock mark tested) 32 else tested
  setPC (applyBlock advance marked) 18

theorem scanStep_cursor {M T C U i : ℕ} {E : Fin M→Edge} {here : Fin M} {s : State}
    (h:ScanCursor T C U E here i s) (hi:i < M) :
    ScanCursor T C U E here (i+1) (scanStep E here ⟨i,hi⟩ s) := by
  unfold scanStep
  split
  all_goals refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_⟩
  all_goals simp [previous,mark,advance,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,h.previous,h.left,h.right]

theorem scanStep_frame {M : ℕ} (E : Fin M→Edge) (here prior : Fin M) (s : State) :
    Frame s (scanStep E here prior s) := by
  unfold scanStep
  split
  · exact frame_trans (frame_setPC s 19) (frame_trans
      (block_frame previous _ (by simp [previous,Allowed])) (frame_trans (frame_setPC _ 34)
      (frame_trans (block_frame mark _ (by simp [mark,Allowed])) (frame_trans (frame_setPC _ 32)
      (frame_trans (block_frame advance _ (by simp [advance,Allowed])) (frame_setPC _ 18))))))
  · exact frame_trans (frame_setPC s 19) (frame_trans
      (block_frame previous _ (by simp [previous,Allowed])) (frame_trans (frame_setPC _ 32)
      (frame_trans (block_frame advance _ (by simp [advance,Allowed])) (frame_setPC _ 18))))

theorem scanStep_heap {M T C U i : ℕ} {E : Fin M→Edge} {here : Fin M} {s : State}
    (h:ScanCursor T C U E here i s) (hi:i < here.val) (hc:Colors E C here.val s) :
    (scanStep E here ⟨i,by omega⟩ s).natHeap=
      if Conflict (E here) (E ⟨i,by omega⟩) then
        Function.update s.natHeap (U+greedy E 11 here.val i) (some 1) else s.natHeap := by
  have hh:=hc ⟨i,by omega⟩ hi
  unfold scanStep
  split <;> simp [previous,mark,advance,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.colors,h.fixed.header.palette,h.fixed.one,h.previous, *]

theorem scanStep_palette {M T C U i : ℕ} {E : Fin M→Edge} {here : Fin M} {s : State}
    (h:ScanCursor T C U E here i s) (hi:i < here.val) (hc:Colors E C here.val s)
    (hp:Palette U (scanned E here i) s) :
    Palette U (scanned E here (i+1)) (scanStep E here ⟨i,by omega⟩ s) := by
  classical
  intro c hcl
  rw [scanStep_heap h hi hc,scanned_succ E here i (by omega)]
  split
  · by_cases he:c = greedy E 11 here.val i
    · subst c;simp
    · simp [he,hp c hcl]
  · exact hp c hcl

theorem scanStep_outside {M T C U i : ℕ} {E : Fin M→Edge} {here : Fin M} {s : State}
    (h:ScanCursor T C U E here i s) (hi:i < here.val) (hc:Colors E C here.val s) :
    ∀a,a < U ∨ U+12 ≤ a→(scanStep E here ⟨i,by omega⟩ s).natHeap a = s.natHeap a := by
  intro a ha
  have hcol:=greedy_le E here.val i
  rw [scanStep_heap h hi hc]
  split <;> simp (disch:=omega)

theorem scanStep_bounded {M T C U i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (E : Fin M→Edge) (here : Fin M) (h:ScanCursor T C U E here i s)
    (hi:i < here.val) (hed:Edges E T s) (hc:Colors E C here.val s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) :
    ∃t,t ≤ 21 ∧ BoundedRuns program n x B s t (scanStep E here ⟨i,by omega⟩ s) := by
  classical
  let prior:Fin M:=⟨i,by omega⟩
  let v:=setPC s 19
  have ent:BoundedRuns program n x B s 1 v:=by
    simpa [h.previous,h.index,hi,v] using
      branch_bounded 815 814 19 39 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have he0:=hed prior
  have he:s.natHeap (T+i*3) = some (E prior).left ∧
      s.natHeap (T+i*3+1) = some (E prior).right:=by simpa [prior,Nat.mul_comm] using he0
  have bl: (E prior).left ≤ B:=(hs.2.2.1 _ _ he.1).2
  have br: (E prior).right ≤ B:=(hs.2.2.1 _ _ he.2).2
  have rp:=block_runs previous program 19 n B x v previous_code rfl ent.final_bound
    (by change 19+5 ≤ B;omega)
    (by simp [readable,previous,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.rows,h.fixed.three,h.fixed.one,h.previous,he.1,he.2])
    (by simp [peak,previous,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.rows,h.fixed.three,h.fixed.one,h.previous,he.1,he.2];omega)
  let p:=applyBlock previous v
  have ppc:p.pc = 24:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have hm:matchesFrom p 0 4 ↔ Conflict (E here) (E prior):=by
    simp [matchesFrom,testLeft,testRight,p,previous,applyBlock,Op.apply,v,setPC,
      writeNat,next,h.fixed.header.rows,h.fixed.three,h.fixed.one,h.previous,
      h.left,h.right,he.1,he.2,Conflict,Incident]
    tauto
  obtain ⟨tt,htt,rt⟩:=tests_bounded 0 4 B n x p rfl ppc hB rp.final_bound
  let tested:=setPC p (if Conflict (E here) (E prior) then 34 else 32)
  have rtest:BoundedRuns program n x B p tt tested:=by simpa [tested,hm] using rt
  let marked:=if Conflict (E here) (E prior) then setPC (applyBlock mark tested) 32 else tested
  have rm:∃tm,tm ≤ 5 ∧ BoundedRuns program n x B tested tm marked:=by
    by_cases hd:Conflict (E here) (E prior)
    · have hh:=hc prior hi
      have hcol:=greedy_le E here.val i
      have run:=block_runs mark program 34 n B x tested mark_code (by simp [tested,hd,setPC])
        rtest.final_bound (by change 34+4 ≤ B;omega)
        (by simp [readable,mark,Op.readable,Op.apply,tested,p,previous,applyBlock,v,setPC,
          writeNat,next,h.fixed.header.colors,h.fixed.one,h.previous,hh,prior])
        (by simp [peak,mark,Op.peak,Op.apply,tested,p,previous,applyBlock,v,setPC,
          writeNat,next,h.fixed.header.colors,h.fixed.header.palette,h.fixed.one,h.previous,hh,prior];omega)
      have mpc:(applyBlock mark tested).pc = 38:=by
        rw [UniformTensorMonomialMachine.applyBlock_pc];simp [tested,hd,setPC];rfl
      have jump:=jump_bounded 32 B n x (applyBlock mark tested) (by rw [mpc];rfl)
        (by omega) run.final_bound
      exact ⟨5,by omega,by simpa [marked,hd,mark] using run.trans jump⟩
    · exact ⟨0,by omega,by simpa [marked,hd] using BoundedRuns.refl rtest.final_bound⟩
  obtain ⟨tm,htm,rmark⟩:=rm
  have mpc:marked.pc = 32:=by
    dsimp [marked];split <;> simp_all [setPC,tested]
  have mi:marked.natReg 815 = i:=by
    dsimp [marked];split <;> simp [mark,tested,p,previous,applyBlock,v,setPC,Op.apply,writeNat,next,h.previous]
  have mo:marked.natReg 811 = 1:=by
    dsimp [marked];split <;> simp [mark,tested,p,previous,applyBlock,v,setPC,Op.apply,writeNat,next,h.fixed.one]
  have ra:=block_runs advance program 32 n B x marked advance_code mpc rmark.final_bound
    (by change 32+1 ≤ B;omega) (by simp [readable,advance,Op.readable])
    (by simp [peak,advance,Op.peak,mi,mo];omega)
  have apc:(applyBlock advance marked).pc = 33:=by rw [UniformTensorMonomialMachine.applyBlock_pc,mpc];rfl
  have jump:=jump_bounded 18 B n x (applyBlock advance marked) (by rw [apc];rfl)
    (by omega) ra.final_bound
  refine ⟨1+5+tt+tm+2,by omega,?_⟩
  have tr:=ent.trans (rp.trans (rtest.trans (rmark.trans (ra.trans jump))))
  change BoundedRuns program n x B s (1+(5+(tt+(tm+(1+1)))))
    (scanStep E here ⟨i,by omega⟩ s) at tr
  convert tr using 1;omega

theorem scan_loop {M T C U i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (E : Fin M→Edge) (here : Fin M) (h:ScanCursor T C U E here i s)
    (hi:i+remaining = here.val) (hed:Edges E T s) (hc:Colors E C here.val s)
    (hp:Palette U (scanned E here i) s) (hB:51 ≤ B)
    (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ 21*remaining ∧ BoundedRuns program n x B s t u ∧
    ScanCursor T C U E here here.val u ∧ Palette U (scanned E here here.val) u ∧
    (∀a,a < U ∨ U+12 ≤ a→u.natHeap a = s.natHeap a) ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i = here.val:=by omega
    subst i
    exact ⟨0,s,by omega,.refl hs,h,hp,fun _ _=>rfl,frame_refl s⟩
  | succ r ih =>
    have il:i < here.val:=by omega
    obtain ⟨t,ht,run⟩:=scanStep_bounded B n x s E here h il hed hc hB hT hC hU hs
    have out:=scanStep_outside h il hc
    have ned:Edges E T (scanStep E here ⟨i,by omega⟩ s):=by
      intro q
      rw [out (T+3*q.val) (by omega),out (T+3*q.val+1) (by omega)]
      exact hed q
    have ncs:=colors_palette_transport hc out hC
    obtain ⟨v,u,hv,ru,cu,pu,ou,fu⟩:=ih (i:=i+1) (scanStep E here ⟨i,by omega⟩ s)
      (scanStep_cursor h (by omega)) (by omega) ned ncs (scanStep_palette h il hc hp) run.final_bound
    exact ⟨t+v,u,by omega,run.trans ru,cu,pu,
      fun a ha=>(ou a ha).trans (out a ha),frame_trans (scanStep_frame E here _ s) fu⟩

structure ChoiceCursor (M T C U j pc c : ℕ) (s : State) : Prop where
  fixed : Fixed M T C U s
  pc : s.pc = pc
  index : s.natReg 814 = j
  color : s.natReg 816 = c

theorem choose_begin {M T C U : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (E : Fin M→Edge) (here : Fin M) (h:ScanCursor T C U E here here.val s)
    (hB:51 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 2 u ∧ ChoiceCursor M T C U here.val 40 0 u ∧
    u.natHeap = s.natHeap ∧ Frame s u := by
  let v:=setPC s 39
  have ent:BoundedRuns program n x B s 1 v:=by
    simpa [h.previous,h.index,v] using
      branch_bounded 815 814 19 39 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have run:=block_runs chooseStart program 39 n B x v chooseStart_code rfl ent.final_bound
    (by change 39+1 ≤ B;omega) (by simp [readable,chooseStart,Op.readable])
    (by simp [peak,chooseStart,Op.peak])
  refine ⟨applyBlock chooseStart v,ent.trans run,?_,rfl,?_⟩
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,?_⟩
    all_goals simp [chooseStart,applyBlock,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index]
  · exact frame_trans (frame_setPC s 39) (block_frame chooseStart _ (by simp [chooseStart,Allowed]))

def inspected (used : Finset ℕ) (c : ℕ) (s : State) :=
  setPC (applyBlock chooseRead (setPC s 41)) (if c∈used then 44 else 46)

theorem inspect_bounded {M T C U j c : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (used : Finset ℕ) (h:ChoiceCursor M T C U j 40 c s) (hc:c < 11)
    (hp:Palette U used s) (hB:51 ≤ B) (hU:U+12 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 4 (inspected used c s) ∧
    ChoiceCursor M T C U j (if c∈used then 44 else 46) c (inspected used c s) ∧
    (inspected used c s).natHeap = s.natHeap ∧ Frame s (inspected used c s) := by
  classical
  let v:=setPC s 41
  have ent:BoundedRuns program n x B s 1 v:=by
    simpa [h.color,h.fixed.limit,hc,v] using
      branch_bounded 816 813 41 46 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
  have hh:=hp c hc
  have run:=block_runs chooseRead program 41 n B x v chooseRead_code rfl ent.final_bound
    (by change 41+2 ≤ B;omega)
    (by simp [readable,chooseRead,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.palette,h.color,hh])
    (by simp [peak,chooseRead,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.palette,h.color,hh];split <;> omega)
  have ipc:(applyBlock chooseRead v).pc = 43:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:=branch_bounded 823 811 46 44 B n x (applyBlock chooseRead v)
    (by rw [ipc];rfl) (by omega) (by omega) run.final_bound
  refine ⟨?_,?_,rfl,?_⟩
  · by_cases hu:c∈used
    all_goals simpa [inspected,v,chooseRead,applyBlock,Op.apply,setPC,writeNat,next,
      h.fixed.header.palette,h.fixed.one,h.color,hh,hu] using ent.trans (run.trans last)
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_,?_⟩
    all_goals simp [inspected,chooseRead,applyBlock,Op.apply,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,h.color]
  · exact frame_trans (frame_setPC s 41) (frame_trans
      (block_frame chooseRead _ (by simp [chooseRead,Allowed])) (frame_setPC _ _))

def choiceNext (s : State) := setPC (applyBlock chooseNext s) 40

theorem choiceNext_bounded {M T C U j c : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:ChoiceCursor M T C U j 44 c s) (hc:c < 11) (hB:51 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 2 (choiceNext s) ∧
    ChoiceCursor M T C U j 40 (c+1) (choiceNext s) ∧
    (choiceNext s).natHeap = s.natHeap ∧ Frame s (choiceNext s) := by
  have run:=block_runs chooseNext program 44 n B x s chooseNext_code h.pc hs
    (by change 44+1 ≤ B;omega) (by simp [readable,chooseNext,Op.readable])
    (by simp [peak,chooseNext,Op.peak,h.color,h.fixed.one];omega)
  have ipc:(applyBlock chooseNext s).pc = 45:=by rw [UniformTensorMonomialMachine.applyBlock_pc,h.pc];rfl
  have last:=jump_bounded 40 B n x (applyBlock chooseNext s) (by rw [ipc];rfl)
    (by omega) run.final_bound
  refine ⟨run.trans last,?_,rfl,?_⟩
  · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_,?_⟩
    all_goals simp [choiceNext,chooseNext,applyBlock,Op.apply,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,h.color]
  · exact frame_trans (block_frame chooseNext _ (by simp [chooseNext,Allowed])) (frame_setPC _ 40)

/-- Cell U+11 can be marked but is never loaded by this loop. -/
theorem choose_loop {M T C U j c : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (used : Finset ℕ) (h:ChoiceCursor M T C U j 40 c s)
    (hc:c+remaining = 11) (hp:Palette U used s) (pre:∀a,a < c→a∈used)
    (hB:51 ≤ B) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ 6*remaining+1 ∧ BoundedRuns program n x B s t u ∧
    ChoiceCursor M T C U j 46 (firstFree 11 used) u ∧ u.natHeap = s.natHeap ∧ Frame s u := by
  classical
  induction remaining generalizing c s with
  | zero =>
    have he:c = 11:=by omega
    subst c
    have free:firstFree 11 used = 11:=firstFree_of_prefix used 11 le_rfl pre (by omega)
    let u:=setPC s 46
    have run:BoundedRuns program n x B s 1 u:=by
      simpa [h.color,h.fixed.limit,u] using
        branch_bounded 816 813 41 46 B n x s (by rw [h.pc];rfl) (by omega) (by omega) hs
    refine ⟨1,u,by omega,run,?_,rfl,frame_setPC s 46⟩
    exact ⟨⟨⟨h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette⟩,
      h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit⟩,rfl,h.index,
      by simpa [free,u,setPC] using h.color⟩
  | succ r ih =>
    have cl:c < 11:=by omega
    obtain ⟨run,cur,heap,frame⟩:=inspect_bounded B n x s used h cl hp hB hU hs
    by_cases hu:c∈used
    · have ncur:ChoiceCursor M T C U j 44 c (inspected used c s):=by simpa [hu] using cur
      obtain ⟨nr,nc,nh,nf⟩:=choiceNext_bounded B n x _ ncur cl hB run.final_bound
      have nextPre:∀a,a < c+1→a∈used:=by intro a ha;by_cases he:a = c;simpa [he] using hu;exact pre a (by omega)
      have nextPal:Palette U used (choiceNext (inspected used c s)):=by
        intro a ha;rw [nh,heap];exact hp a ha
      obtain ⟨t,u,ht,ru,cu,uh,uf⟩:=ih (c:=c+1) _ nc (by omega) nextPal nextPre nr.final_bound
      exact ⟨4+2+t,u,by omega,by simpa only [←Nat.add_assoc] using run.trans (nr.trans ru),cu,uh.trans (nh.trans heap),
        frame_trans frame (frame_trans nf uf)⟩
    · have free:firstFree 11 used = c:=firstFree_of_prefix used c (by omega) pre (by intro _;exact hu)
      refine ⟨4,inspected used c s,by omega,run,?_,heap,frame⟩
      simpa [hu,free] using cur

def committed (s : State) := setPC (applyBlock commit s) 5

theorem commit_cursor {M T C U j c : ℕ} {s : State} (h:ChoiceCursor M T C U j 46 c s) :
    OuterCursor M T C U (j+1) (committed s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,rfl,?_⟩
  all_goals simp [committed,commit,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.rows,h.fixed.header.colors,h.fixed.header.palette,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.fixed.limit,h.index,h.color]

theorem commit_heap {M T C U j c : ℕ} {s : State} (h:ChoiceCursor M T C U j 46 c s) :
    (committed s).natHeap = Function.update s.natHeap (C+j) (some c) := by
  simp [committed,commit,applyBlock,Op.apply,setPC,writeNat,next,h.fixed.header.colors,h.index,h.color]

theorem commit_frame (s : State) : Frame s (committed s) :=
  frame_trans (block_frame commit s (by simp [commit,Allowed])) (frame_setPC _ 5)

theorem commit_bounded {M T C U j c : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:ChoiceCursor M T C U j 46 c s) (hj:j < M) (hc:c ≤ 11)
    (hB:51 ≤ B) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 4 (committed s) := by
  have run:=block_runs commit program 46 n B x s commit_code h.pc hs
    (by change 46+3 ≤ B;omega) (by simp [readable,commit,Op.readable])
    (by simp [peak,commit,Op.peak,Op.apply,writeNat,next,
      h.fixed.header.colors,h.index,h.color,h.fixed.one];omega)
  have ipc:(applyBlock commit s).pc = 49:=by rw [UniformTensorMonomialMachine.applyBlock_pc,h.pc];rfl
  exact run.trans (jump_bounded 5 B n x _ (by rw [ipc];rfl) (by omega) run.final_bound)

theorem commit_colors {M T C U : ℕ} {E : Fin M→Edge} {here : Fin M} {s : State}
    (h:ChoiceCursor M T C U here.val 46
      (firstFree 11 (earlierColors E here (greedy E 11 here.val))) s)
    (hc:Colors E C here.val s) : Colors E C (here.val+1) (committed s) := by
  intro i hi
  rw [commit_heap h,greedy_next E 11 here.val here.isLt]
  by_cases he:i.val = here.val
  · simp [he]
  · simp (disch:=omega) [hc i (by omega)]

/-- A full row starts with an internally cleared palette and uses only the
    original endpoints and earlier physically written colors. -/
theorem one_row {M T C U : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (E : Fin M→Edge) (here : Fin M) (h:OuterCursor M T C U here.val s)
    (hed:Edges E T s) (colors:Colors E C here.val s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ 150+21*here.val ∧ BoundedRuns program n x B s t u ∧
    OuterCursor M T C U (here.val+1) u ∧ Colors E C (here.val+1) u ∧
    Outside C M U s u ∧ Frame s u := by
  obtain ⟨v,r0,c0,h0,f0⟩:=clear_begin B n x s h here.isLt hB hs
  obtain ⟨w,r1,c1,p1,o1,f1⟩:=clear_loop 11 B n x v c0 rfl
    (by intro a ha;omega) hB hU r0.final_bound
  have ed1:Edges E T w:=by
    intro i
    rw [o1 (T+3*i.val) (by omega),o1 (T+3*i.val+1) (by omega),h0]
    exact hed i
  have colors1:Colors E C here.val w:=by
    intro i hi;rw [o1 (C+i.val) (by omega),h0];exact colors i hi
  obtain ⟨p,r2,c2,h2,f2⟩:=current_begin B n x w E c1 here.isLt ed1 hB hT hC hU r1.final_bound
  have ed2:Edges E T p:=by intro i;rw [h2];exact ed1 i
  have colors2:Colors E C here.val p:=by intro i hi;rw [h2];exact colors1 i hi
  have pal2:Palette U (scanned E here 0) p:=by intro a ha;rw [h2,scanned_zero];exact p1 a ha
  obtain ⟨ts,z,hts,r3,c3,p3,o3,f3⟩:=scan_loop here.val B n x p E here c2 (by omega) ed2 colors2
    pal2 hB hT hC hU r2.final_bound
  have colors3:=colors_palette_transport colors2 o3 hC
  obtain ⟨q,r4,c4,h4,f4⟩:=choose_begin B n x z E here c3 hB r3.final_bound
  have pal4:Palette U (scanned E here here.val) q:=by intro a ha;rw [h4];exact p3 a ha
  obtain ⟨tc,u,htc,r5,c5,h5,f5⟩:=choose_loop 11 B n x q (scanned E here here.val) c4 rfl
    pal4 (by intro a ha;omega) hB hU r4.final_bound
  have colors5:Colors E C here.val u:=by intro i hi;rw [h5,h4];exact colors3 i hi
  have c5':ChoiceCursor M T C U here.val 46
      (firstFree 11 (earlierColors E here (greedy E 11 here.val))) u:=by simpa [scanned_end] using c5
  have r6:=commit_bounded B n x u c5' here.isLt (firstFree_le _ _) hB hC hU r5.final_bound
  refine ⟨2+55+7+ts+2+tc+4,committed u,by omega,?_,commit_cursor c5',commit_colors c5' colors5,?_,?_⟩
  · have run:=r0.trans (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))))
    simpa only [Nat.add_assoc] using run
  · intro a ha hu
    rw [commit_heap c5']
    simp only [Function.update_apply]
    rw [ite_eq_right (by omega),h5,h4,o3 a hu,h2,o1 a hu,h0]
  · exact frame_trans f0 (frame_trans f1 (frame_trans f2
      (frame_trans f3 (frame_trans f4 (frame_trans f5 (commit_frame u))))))

theorem outer_loop {M T C U j : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (E : Fin M→Edge) (h:OuterCursor M T C U j s) (hj:j+remaining = M)
    (hed:Edges E T s) (colors:Colors E C j s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ remaining*(150+21*M) ∧ BoundedRuns program n x B s t u ∧
    OuterCursor M T C U M u ∧ Colors E C M u ∧ Outside C M U s u ∧ Frame s u := by
  induction remaining generalizing j s with
  | zero =>
    have he:j = M:=by omega
    subst j
    exact ⟨0,s,by omega,.refl hs,h,colors,fun _ _ _=>rfl,frame_refl s⟩
  | succ r ih =>
    let here:Fin M:=⟨j,by omega⟩
    obtain ⟨t,u,ht,ru,cu,cs,ou,fu⟩:=one_row B n x s E here h hed colors hB hT hC hU hs
    obtain ⟨v,w,hv,rw,cw,sw,ow,fw⟩:=ih (j:=j+1) u cu (by omega)
      (edges_transport hed ou hT hC) cs ru.final_bound
    refine ⟨t+v,w,?_,ru.trans rw,cw,sw,outside_trans ou ow,frame_trans fu fw⟩
    have he:here.val = j:=rfl
    rw [he] at ht
    have jl:j ≤ M:=by omega
    nlinarith

/-- Universal initialized physical greedy coloring, including halt. -/
theorem execution (M T C U B n : ℕ) (x : Fin n→ℂ) (s : State) (E : Fin M→Edge)
    (h:Header M T C U s) (hp:s.pc = 0) (hed:Edges E T s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ runtimeBudget M ∧ BoundedExecution program n x B s t u ∧ u.pc = 50 ∧
    Header M T C U u ∧ Colors E C M u ∧ (∀i:Fin M,greedy E 11 M i.val ≤ 11) ∧
    Edges E T u ∧ Outside C M U s u ∧ Frame s u := by
  obtain ⟨r0,c0,h0,f0⟩:=startup M T C U B n x s h hp hB hs
  have ed0:Edges E T (applyBlock boot s):=by intro i;rw [h0];exact hed i
  obtain ⟨t,w,ht,rw,cw,cs,ow,fw⟩:=outer_loop M B n x (applyBlock boot s) E c0 (by omega) ed0
    (by intro i hi;omega) hB hT hC hU r0.final_bound
  let u:=setPC w 50
  have last:BoundedRuns program n x B w 1 u:=by
    simpa [cw.index,cw.fixed.header.count,u] using
      branch_bounded 814 800 6 50 B n x w (by rw [cw.pc];rfl) (by omega) (by omega) rw.final_bound
  have halted:step program n x u=.halted u:=by simp [step,u,setPC,halt_at]
  have run:BoundedExecution program n x B s (5+t+2) u:=by
    have rr:=r0.trans (rw.trans last)
    have re:=rr.executes (BoundedExecution.halt last.final_bound halted)
    simpa only [boot,List.length_cons,List.length_nil,Nat.add_assoc] using re
  have out:Outside C M U s u:=by intro a ha hu;exact (ow a ha hu).trans (congrFun h0 a)
  refine ⟨5+t+2,u,?_,run,rfl,?_,?_,fun i=>greedy_le E M i.val,
    edges_transport hed out hT hC,out,?_⟩
  · unfold runtimeBudget;nlinarith
  · exact ⟨cw.fixed.header.count,cw.fixed.header.rows,cw.fixed.header.colors,cw.fixed.header.palette⟩
  · simpa [Colors,u,setPC] using cs
  · exact frame_trans f0 (frame_trans fw (frame_setPC w 50))

/-- Degree-six is a separate local graph hypothesis; it is never needed
    to execute the integer program. -/
theorem execution_degree_six (M T C U B n : ℕ) (x : Fin n→ℂ) (s : State)
    (E : Fin M→Edge) (hd:DegreeBound E 6)
    (h:Header M T C U s) (hp:s.pc = 0) (hed:Edges E T s)
    (hB:51 ≤ B) (hT:T+3*M ≤ C) (hC:C+M ≤ U) (hU:U+12 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ runtimeBudget M ∧ BoundedExecution program n x B s t u ∧ u.pc = 50 ∧
    Header M T C U u ∧ (∀i:Fin M,u.natHeap (C+i.val) = some (coloring E 6 i)) ∧
    (∀i:Fin M,coloring E 6 i < 11) ∧
    (∀i j:Fin M,i ≠ j→coloring E 6 i = coloring E 6 j→¬Conflict (E i) (E j)) ∧
    Edges E T u ∧ Outside C M U s u ∧ Frame s u := by
  obtain ⟨t,u,ht,run,pc,header,colors,_,edges,out,frame⟩:=
    execution M T C U B n x s E h hp hed hB hT hC hU hs
  refine ⟨t,u,ht,run,pc,header,?_,?_,?_,edges,out,frame⟩
  · intro i;simpa [coloring] using colors i i.isLt
  · intro i;exact coloring_bound E hd (by omega) i
  · intro i j hn hc;exact same_color_disjoint E hd (by omega) i j hn hc


theorem frame_saved {s u : State} (h:Frame s u) (r : ℕ) (hr:100≤r ∧ r≤106) :
    u.natReg r=s.natReg r := h.2.2.2.2 r (by omega)

end
end ExactFourierCircuits.UniformGreedyColorMachine
