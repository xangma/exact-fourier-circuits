import UniformTensorMonomialMachine
import UniformRadixInstructionMachine
import UniformColoring
import UniformInPlaceMachine
import UniformGreedyColorMachine
import UniformMatchingAxisTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformColorLayerTableMachine
open UniformMachine UniformColoring
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Nat880=count,881=actual three-word rows,882=actual color bank,
883=selected color,884=fresh output rows,885=fresh original-ordinal bank.
Scratch is Nat890..899; Nat894 returns the derived selected count. -/
def boot : List Op := [.literal 890 0,.literal 891 1,.literal 892 3,
  .literal 893 0,.literal 894 0]
def read : List Op := [.add 895 882 893,.getNat 896 895]
def copy : List Op := [.mul 897 893 892,.add 897 881 897,
  .mul 898 894 892,.add 898 884 898,
  .getNat 899 897,.putNat 898 899,.add 897 897 891,.add 898 898 891,
  .getNat 899 897,.putNat 898 899,.add 897 897 891,.add 898 898 891,
  .getNat 899 897,.putNat 898 899,.add 895 885 894,.putNat 895 893,
  .add 894 894 891]
def tick : List Op := [.add 893 893 891]
def program : Program := boot.map Op.code ++ [.branchLT 893 880 6 29] ++
  read.map Op.code ++ [.branchLT 896 883 27 9,.branchLT 883 896 27 10] ++
  copy.map Op.code ++ tick.map Op.code ++ [.jump 5,.halt]
theorem program_length : program.length=30 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem read_code : BlockAt read program 6 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem copy_code : BlockAt copy program 10 := by
  intro i hi;change i < 17 at hi;interval_cases i <;> rfl
theorem tick_code : BlockAt tick program 27 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem outer_at : program[5]?=some (.branchLT 893 880 6 29) := rfl
theorem less_at : program[8]?=some (.branchLT 896 883 27 9) := rfl
theorem greater_at : program[9]?=some (.branchLT 883 896 27 10) := rfl
theorem tick_at : program[28]?=some (.jump 5) := rfl
theorem halt_at : program[29]?=some .halt := rfl
def selected (i k : ℕ) (color : ℕ→ℕ) :=
  (List.range i).filter (fun j=>decide (color j=k))
theorem selected_mem (i k : ℕ) (color : ℕ→ℕ) (j : ℕ) :
    j∈selected i k color ↔ j < i ∧ color j=k := by simp [selected]
theorem selected_length (i k : ℕ) (color : ℕ→ℕ) :
    (selected i k color).length ≤ i := (List.length_filter_le _ _).trans (by simp)
theorem selected_nodup (i k : ℕ) (color : ℕ→ℕ) : (selected i k color).Nodup :=
  (List.nodup_range).filter _
theorem selected_succ (i k : ℕ) (color : ℕ→ℕ) :
    selected (i+1) k color=selected i k color ++ (if color i=k then [i] else []) := by
  by_cases h:color i=k <;> simp [selected,List.range_succ,List.filter_append,h]
def rowCost (k value : ℕ) := if value < k then 6 else if k < value then 7 else 24
theorem rowCost_bound (k value : ℕ) : rowCost k value ≤ 24 := by
  unfold rowCost
  split_ifs <;> omega
def runtimeBudget (M : ℕ) := 24*M+7

noncomputable section
structure Header (M T C k O I : ℕ) (s : State) : Prop where
  count : s.natReg 880=M
  source : s.natReg 881=T
  colors : s.natReg 882=C
  selectedColor : s.natReg 883=k
  output : s.natReg 884=O
  ordinals : s.natReg 885=I
structure Fixed (M T C k O I : ℕ) (s : State) : Prop where
  header : Header M T C k O I s
  zero : s.natReg 890=0
  one : s.natReg 891=1
  three : s.natReg 892=3
structure Cursor (M T C k O I i count : ℕ) (s : State) : Prop where
  fixed : Fixed M T C k O I s
  pc : s.pc=5
  index : s.natReg 893=i
  count : s.natReg 894=count
def Colors (C M : ℕ) (color : ℕ→ℕ) (s : State) : Prop :=
  ∀ (i : ℕ), i < M → s.natHeap (C+i)=some (color i)
def Rows (T M : ℕ) (row : ℕ→UniformInPlaceMachine.Row) (s : State) : Prop :=
  ∀ (i : ℕ), i < M → s.natHeap (T+3*i)=some (row i).dst ∧
    s.natHeap (T+3*i+1)=some (row i).src ∧
    s.natHeap (T+3*i+2)=some (row i).coefficient
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀q,(q < 890 ∨ 900 ≤ q)→u.natReg q=s.natReg q)
def Outside (O M I : ℕ) (s u : State) : Prop :=
  ∀a,(a < O ∨ O+3*M ≤ a)→(a < I ∨ I+M ≤ a)→u.natHeap a=s.natHeap a
def readState (s : State) := applyBlock read (setPC s 6)
def copyState (s : State) := applyBlock copy (setPC s 10)
def tickState (s : State) := setPC (applyBlock tick (setPC s 27)) 5
def iteration (k value : ℕ) (s : State) :=
  tickState (if value=k then copyState (readState s) else readState s)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun q hq=>(h'.2.2.2.2 q hq).trans (h.2.2.2.2 q hq)⟩
theorem Frame.saved {s u : State} (h:Frame s u) :
    ∀q,100 ≤ q→q ≤ 106→u.natReg q=s.natReg q := by
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
theorem Fixed.withPC {M T C k O I : ℕ} {s : State}
    (h:Fixed M T C k O I s) (pc : ℕ) : Fixed M T C k O I (setPC s pc) :=
  ⟨⟨h.header.count,h.header.source,h.header.colors,h.header.selectedColor,
    h.header.output,h.header.ordinals⟩,h.zero,h.one,h.three⟩
theorem boot_cursor {M T C k O I : ℕ} {s : State}
    (h:Header M T C k O I s) (hp:s.pc=0) :
    Cursor M T C k O I 0 0 (applyBlock boot s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,?_,?_,?_⟩
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next,hp,
    h.count,h.source,h.colors,h.selectedColor,h.output,h.ordinals]
theorem boot_frame (s : State) : Frame s (applyBlock boot s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
theorem read_spec {M T C k O I i count value : ℕ} {s : State}
    (h:Cursor M T C k O I i count s) (hv:s.natHeap (C+i)=some value) :
    (readState s).pc=8 ∧ (readState s).natReg 896=value ∧
    Cursor M T C k O I i count (setPC (readState s) 5) := by
  refine ⟨?_,?_,⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_⟩⟩
  all_goals simp [readState,read,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.colors,
    h.fixed.header.selectedColor,h.fixed.header.output,h.fixed.header.ordinals,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.index,h.count,hv]
theorem read_heap (s : State) : (readState s).natHeap=s.natHeap := rfl
theorem read_frame (s : State) : Frame s (readState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [readState,read,applyBlock,Op.apply,setPC,writeNat,next]
theorem read_bounded {M T C k O I i count value : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor M T C k O I i count s) (hi:i < M)
    (hv:s.natHeap (C+i)=some value) (hC:C+M ≤ B) (hB:30 ≤ B)
    (hs:WordBound B s) : BoundedRuns program n x B s 3 (readState s) := by
  have first:=branch_runs program B n 893 880 6 29 x s
    (by rw [h.pc];exact outer_at) hs (by omega) (by omega)
  have cmp:s.natReg 893 < s.natReg 880:=by rw [h.index,h.fixed.header.count];exact hi
  simp only [cmp,ite_true] at first
  let v:=setPC s 6
  have valueBound:value ≤ B:=(hs.2.2.1 (C+i) value hv).2
  have rd:readable read v:=by
    simp [readable,read,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.colors,h.index,hv]
  have pk:peak read v ≤ B:=by
    simp [peak,read,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.colors,h.index,hv]
    omega
  have body:=block_runs read program 6 n B x v read_code rfl first.final_bound
    (by change 6+2 ≤ B;omega) rd pk
  simpa only [show read.length=2 from rfl,readState,v] using first.trans body
theorem copy_cursor {M T C k O I i count : ℕ} {s : State}
    (h:Cursor M T C k O I i count s) :
    Cursor M T C k O I i (count+1) (setPC (copyState s) 5) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_⟩
  all_goals simp [copyState,copy,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.colors,
    h.fixed.header.selectedColor,h.fixed.header.output,h.fixed.header.ordinals,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.index,h.count]
theorem copy_frame (s : State) : Frame s (copyState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [copyState,copy,applyBlock,Op.apply,setPC,writeNat,next]
theorem tick_cursor {M T C k O I i count : ℕ} {s : State}
    (h:Cursor M T C k O I i count s) : Cursor M T C k O I (i+1) count (tickState s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_⟩
  all_goals simp [tickState,tick,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.colors,
    h.fixed.header.selectedColor,h.fixed.header.output,h.fixed.header.ordinals,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.index,h.count]
theorem tick_frame (s : State) : Frame s (tickState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [tickState,tick,applyBlock,Op.apply,setPC,writeNat,next]
theorem tick_heap (s : State) : (tickState s).natHeap=s.natHeap := rfl

def OutputRows (O : ℕ) (indices : List ℕ) (row : ℕ→UniformInPlaceMachine.Row) (s : State) : Prop :=
  ∀(j : ℕ)(hj:j < indices.length),s.natHeap (O+3*j)=some (row indices[j]).dst ∧
    s.natHeap (O+3*j+1)=some (row indices[j]).src ∧
    s.natHeap (O+3*j+2)=some (row indices[j]).coefficient

def Ordinals (I : ℕ) (indices : List ℕ) (s : State) : Prop :=
  ∀(j : ℕ)(hj:j < indices.length),s.natHeap (I+j)=some indices[j]

theorem outside_trans {O M I : ℕ} {s u v : State}
    (h:Outside O M I s u) (h':Outside O M I u v) : Outside O M I s v :=
  fun a ho hi=>(h' a ho hi).trans (h a ho hi)
theorem rows_transport {T M O I : ℕ} {row : ℕ→UniformInPlaceMachine.Row} {s u : State}
    (h:Rows T M row s) (out:Outside O M I s u) (hT:T+3*M ≤ O) (hO:O+3*M ≤ I) :
    Rows T M row u := by
  intro j hj
  rw [out (T+3*j) (by omega) (by omega),out (T+3*j+1) (by omega) (by omega),
    out (T+3*j+2) (by omega) (by omega)]
  exact h j hj

theorem colors_transport {C M O I : ℕ} {color : ℕ→ℕ} {s u : State}
    (h:Colors C M color s) (out:Outside O M I s u) (hC:C+M ≤ O) (hO:O+3*M ≤ I) :
    Colors C M color u := by
  intro j hj
  rw [out (C+j) (by omega) (by omega)]
  exact h j hj

theorem copy_heap {M T C k O I i count : ℕ} {s : State}
    (row : ℕ→UniformInPlaceMachine.Row) (h:Cursor M T C k O I i count s)
    (hi:i < M) (src:Rows T M row s) (hT:T+3*M ≤ O) :
    (copyState s).natHeap=Function.update (Function.update (Function.update
      (Function.update s.natHeap (O+3*count) (some (row i).dst))
      (O+3*count+1) (some (row i).src)) (O+3*count+2) (some (row i).coefficient)) (I+count) (some i) := by
  obtain ⟨hd,hr,hc⟩:=src i hi
  simp only [Nat.add_assoc] at hr hc
  simp (disch:=omega) [copyState,copy,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.source,h.fixed.header.output,h.fixed.header.ordinals,
    h.index,h.count,h.fixed.one,h.fixed.three,Nat.mul_comm i 3,
    Nat.mul_comm count 3,Nat.add_assoc,hd,hr,hc]

theorem copy_outside {M T C k O I i count : ℕ} {s : State}
    (row : ℕ→UniformInPlaceMachine.Row) (h:Cursor M T C k O I i count s)
    (hi:i < M) (hc:count ≤ i) (src:Rows T M row s) (hT:T+3*M ≤ O) :
    Outside O M I s (copyState s) := by
  intro a ho hI
  rw [copy_heap row h hi src hT]
  simp (disch:=omega)

theorem copy_banks {M T C k O I i count : ℕ} {s : State}
    (row : ℕ→UniformInPlaceMachine.Row) (indices : List ℕ)
    (h:Cursor M T C k O I i count s) (hi:i < M) (hc:count=indices.length)
    (hci:count ≤ i) (src:Rows T M row s) (hT:T+3*M ≤ O) (hO:O+3*M ≤ I)
    (hp:OutputRows O indices row s) (ho:Ordinals I indices s) :
    OutputRows O (indices++[i]) row (copyState s) ∧ Ordinals I (indices++[i]) (copyState s) := by
  have heap:=copy_heap row h hi src hT
  constructor
  · intro j hj
    rw [heap]
    by_cases jl:j < indices.length
    · have old:=hp j jl
      simp (disch:=omega) [List.getElem_append_left jl,old.1,old.2.1,old.2.2]
    · have je:j=count:=by simp only [List.length_append,List.length_cons,List.length_nil] at hj;omega
      subst j;simp (disch:=omega) [hc]
  · intro j hj
    rw [heap]
    by_cases jl:j < indices.length
    · simp (disch:=omega) [List.getElem_append_left jl,ho j jl]
    · have je:j=count:=by simp only [List.length_append,List.length_cons,List.length_nil] at hj;omega
      subst j;simp [hc]

theorem copy_bounded {M T C k O I i count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (row : ℕ→UniformInPlaceMachine.Row) (s : State) (h:Cursor M T C k O I i count s)
    (hi:i < M) (hc:count ≤ i) (src:Rows T M row s)
    (hT:T+3*M ≤ O) (hO:O+3*M ≤ I) (hI:I+M ≤ B) (hB:30 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B (setPC s 10) 17 (copyState s) := by
  obtain ⟨hd,hr,hcoef⟩:=src i hi
  have db:(row i).dst ≤ B:=(hs.2.2.1 _ _ hd).2
  have rb:(row i).src ≤ B:=(hs.2.2.1 _ _ hr).2
  have cb:(row i).coefficient ≤ B:=(hs.2.2.1 _ _ hcoef).2
  simp only [Nat.add_assoc] at hr hcoef
  have rd:readable copy (setPC s 10):=by
    simp (disch:=omega) [readable,copy,Op.readable,Op.apply,setPC,writeNat,next,
      h.fixed.header.source,h.fixed.header.output,
      h.index,h.count,h.fixed.one,h.fixed.three,Nat.mul_comm i 3,
      Nat.mul_comm count 3,Nat.add_assoc,hd,hr,hcoef]
  have pk:peak copy (setPC s 10) ≤ B:=by
    simp (disch:=omega) [peak,copy,Op.peak,Op.apply,setPC,writeNat,next,
      h.fixed.header.source,h.fixed.header.output,h.fixed.header.ordinals,
      h.index,h.count,h.fixed.one,h.fixed.three,Nat.mul_comm i 3,
      Nat.mul_comm count 3,Nat.add_assoc,hd,hr,hcoef]
    exact ⟨db,rb,cb,by omega⟩
  exact block_runs copy program 10 n B x (setPC s 10) copy_code rfl
    (changePC_bound B s 10 hs (by omega)) (by change 10+17 ≤ B;omega) rd pk

theorem tick_bounded {M T C k O I i count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor M T C k O I i count s) (hi:i < M)
    (hB:30 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B (setPC s 27) 2 (tickState s) := by
  have mB:M ≤ B:=by simpa only [h.fixed.header.count] using hs.2.1 880
  have rd:readable tick (setPC s 27):=by simp [readable,tick,Op.readable]
  have pk:peak tick (setPC s 27) ≤ B:=by
    simp [peak,tick,Op.peak,setPC,h.index,h.fixed.one];omega
  have body:=block_runs tick program 27 n B x (setPC s 27) tick_code rfl
    (changePC_bound B s 27 hs (by omega)) (by change 27+1 ≤ B;omega) rd pk
  have pc:(applyBlock tick (setPC s 27)).pc=28:=by
    rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:=jump_runs program B n 5 x (applyBlock tick (setPC s 27))
    (by rw [pc];exact tick_at) body.final_bound (by omega)
  simpa only [show tick.length=1 from rfl,tickState] using body.trans last

theorem readState_setPC (s : State) (pc : ℕ) : readState (setPC s pc)=readState s := rfl
theorem copyState_setPC (s : State) (pc : ℕ) : copyState (setPC s pc)=copyState s := rfl
theorem tickState_setPC (s : State) (pc : ℕ) : tickState (setPC s pc)=tickState s := rfl
theorem setPC_heap (s : State) (pc : ℕ) : (setPC s pc).natHeap=s.natHeap := rfl
theorem setPC_self (s : State) (pc : ℕ) (hp:s.pc=pc) : setPC s pc=s := by
  cases s;simp_all [setPC]

theorem iteration_cursor {M T C k O I i count value : ℕ} {s : State}
    (h:Cursor M T C k O I i count s) (hv:s.natHeap (C+i)=some value) :
    Cursor M T C k O I (i+1) (if value=k then count+1 else count) (iteration k value s) := by
  have hc:=(read_spec h hv).2.2
  by_cases eq:value=k
  · simpa only [iteration,eq,ite_true,copyState_setPC,tickState_setPC] using
      tick_cursor (copy_cursor hc)
  · simpa only [iteration,eq,ite_false,tickState_setPC] using tick_cursor hc

theorem iteration_frame (k value : ℕ) (s : State) : Frame s (iteration k value s) := by
  by_cases eq:value=k
  · simpa only [iteration,eq,ite_true] using frame_trans (read_frame s)
      (frame_trans (copy_frame (readState s)) (tick_frame (copyState (readState s))))
  · simpa only [iteration,eq,ite_false] using frame_trans (read_frame s) (tick_frame (readState s))

theorem iteration_banks {M T C k O I i : ℕ} {s : State} (row : ℕ→UniformInPlaceMachine.Row)
    (color : ℕ→ℕ) (h:Cursor M T C k O I i (selected i k color).length s)
    (hi:i < M) (src:Rows T M row s) (cols:Colors C M color s)
    (hT:T+3*M ≤ O) (hO:O+3*M ≤ I)
    (hp:OutputRows O (selected i k color) row s) (ho:Ordinals I (selected i k color) s) :
    OutputRows O (selected (i+1) k color) row (iteration k (color i) s) ∧
    Ordinals I (selected (i+1) k color) (iteration k (color i) s) ∧
    Outside O M I s (iteration k (color i) s) := by
  have hc:=(read_spec h (cols i hi)).2.2
  have cnt: (selected i k color).length ≤ i:=selected_length i k color
  by_cases eq:color i=k
  · obtain ⟨pb,ob⟩:=copy_banks row (selected i k color) hc hi rfl cnt src hT hO hp ho
    have out:=copy_outside row hc hi cnt src hT
    simp only [copyState_setPC] at pb ob out
    refine ⟨?_,?_,?_⟩
    · simpa only [iteration,eq,ite_true,selected_succ,List.append_nil,OutputRows,tick_heap] using pb
    · simpa only [iteration,eq,ite_true,selected_succ,List.append_nil,Ordinals,tick_heap] using ob
    · simpa only [iteration,eq,ite_true,Outside,tick_heap,setPC_heap,read_heap] using out
  · refine ⟨?_,?_,?_⟩
    · simpa only [iteration,eq,ite_false,selected_succ,List.append_nil,OutputRows,tick_heap,read_heap] using hp
    · simpa only [iteration,eq,ite_false,selected_succ,List.append_nil,Ordinals,tick_heap,read_heap] using ho
    · intro a _ _;simp only [iteration,eq,ite_false,tick_heap,read_heap]

theorem iteration_bounded {M T C k O I i count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (row : ℕ→UniformInPlaceMachine.Row) (color : ℕ→ℕ) (s : State)
    (h:Cursor M T C k O I i count s) (hi:i < M) (hc:count ≤ i)
    (src:Rows T M row s) (cols:Colors C M color s)
    (hT:T+3*M ≤ O) (hC:C+M ≤ O) (hO:O+3*M ≤ I) (hI:I+M ≤ B)
    (hB:30 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s (rowCost k (color i)) (iteration k (color i) s) := by
  have readRun:=read_bounded B n x s h hi (cols i hi) (by omega) hB hs
  let v:=readState s
  have spec:=read_spec h (cols i hi)
  have vc:Cursor M T C k O I i count (setPC v 5):=spec.2.2
  have kreg:v.natReg 883=k:=vc.fixed.header.selectedColor
  have less:=branch_runs program B n 896 883 27 9 x v
    (by rw [spec.1];exact less_at) readRun.final_bound (by omega) (by omega)
  by_cases lt:color i < k
  · have cmp:v.natReg 896 < v.natReg 883:=by rw [spec.2.1,kreg];exact lt
    simp only [cmp,ite_true] at less
    have tickRun:=tick_bounded B n x (setPC v 5) vc hi hB
      (changePC_bound B v 5 readRun.final_bound (by omega))
    have eq:color i ≠ k:=by omega
    simpa only [rowCost,lt,ite_true,iteration,eq,ite_false,v] using
      (by simpa only [tickState_setPC] using readRun.trans (less.trans tickRun))
  · have cmp:¬v.natReg 896 < v.natReg 883:=by rw [spec.2.1,kreg];exact lt
    simp only [cmp,ite_false] at less
    have greater:=branch_runs program B n 883 896 27 10 x (setPC v 9)
      (by change program[9]?=some _;exact greater_at) less.final_bound (by omega) (by omega)
    by_cases gt:k < color i
    · have cmp':(setPC v 9).natReg 883 < (setPC v 9).natReg 896:=by
        change v.natReg 883 < v.natReg 896;rw [spec.2.1,kreg];exact gt
      simp only [cmp',ite_true] at greater
      have tickRun:=tick_bounded B n x (setPC v 5) vc hi hB
        (changePC_bound B v 5 readRun.final_bound (by omega))
      have eq:color i ≠ k:=by omega
      simpa only [rowCost,lt,gt,ite_true,ite_false,iteration,eq,v] using
        (by simpa only [tickState_setPC] using readRun.trans (less.trans (greater.trans tickRun)))
    · have eq:color i=k:=by omega
      have cmp':¬(setPC v 9).natReg 883 < (setPC v 9).natReg 896:=by
        change ¬v.natReg 883 < v.natReg 896;rw [spec.2.1,kreg];exact gt
      simp only [cmp',ite_false] at greater
      have copyRun:=copy_bounded B n x row (setPC v 5) vc hi hc src hT hO hI hB
        (changePC_bound B v 5 readRun.final_bound (by omega))
      simp only [copyState_setPC] at copyRun
      have cc:=copy_cursor vc
      simp only [copyState_setPC] at cc
      have tickRun:=tick_bounded B n x (setPC (copyState v) 5) cc hi hB
        (changePC_bound B (copyState v) 5 copyRun.final_bound (by omega))
      have copyPC:(copyState v).pc=27:=by
        rw [copyState,UniformTensorMonomialMachine.applyBlock_pc];rfl
      have reset:=setPC_self (copyState v) 27 copyPC
      change BoundedRuns program n x B (setPC (copyState v) 27) 2 (tickState (setPC (copyState v) 5)) at tickRun
      rw [reset,tickState_setPC] at tickRun
      simpa [rowCost,iteration,eq,v] using
        readRun.trans (less.trans (greater.trans (copyRun.trans tickRun)))

def scanCost (k : ℕ) (color : ℕ→ℕ) (i : ℕ) : ℕ→ℕ
  | 0=>0
  | rem+1=>rowCost k (color i)+scanCost k color (i+1) rem

theorem scanCost_bound (k : ℕ) (color : ℕ→ℕ) (i remaining : ℕ) :
    scanCost k color i remaining ≤ 24*remaining := by
  induction remaining generalizing i with
  | zero=>simp [scanCost]
  | succ rem ih=>
    have bound:=ih (i+1)
    have row:=rowCost_bound k (color i)
    simp only [scanCost];omega

theorem loop {M T C k O I i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (row : ℕ→UniformInPlaceMachine.Row) (color : ℕ→ℕ) (s : State)
    (h:Cursor M T C k O I i (selected i k color).length s) (hi:i+remaining=M)
    (src:Rows T M row s) (cols:Colors C M color s)
    (hT:T+3*M ≤ O) (hC:C+M ≤ O) (hO:O+3*M ≤ I) (hI:I+M ≤ B)
    (hp:OutputRows O (selected i k color) row s) (ho:Ordinals I (selected i k color) s)
    (hB:30 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (scanCost k color i remaining) u ∧
    Cursor M T C k O I M (selected M k color).length u ∧
    OutputRows O (selected M k color) row u ∧ Ordinals I (selected M k color) u ∧
    Rows T M row u ∧ Colors C M color u ∧ Outside O M I s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero=>
    have eq:i=M:=by omega
    subst i
    exact ⟨s,.refl hs,h,hp,ho,src,cols,fun _ _ _=>rfl,frame_refl s⟩
  | succ rem ih=>
    have il:i < M:=by omega
    have run:=iteration_bounded B n x row color s h il (selected_length i k color)
      src cols hT hC hO hI hB hs
    obtain ⟨pb,ob,out⟩:=iteration_banks row color h il src cols hT hO hp ho
    have next:Cursor M T C k O I (i+1) (selected (i+1) k color).length
        (iteration k (color i) s):=by
      have hc:=iteration_cursor h (cols i il)
      by_cases eq:color i=k <;> simpa [selected_succ,eq] using hc
    obtain ⟨u,ru,uc,up,uo,us,uk,ut,uf⟩:=ih (i:=i+1) (iteration k (color i) s) next (by omega)
      (rows_transport src out hT hO) (colors_transport cols out hC hO) pb ob run.final_bound
    exact ⟨u,run.trans ru,uc,up,uo,us,uk,outside_trans out ut,
      frame_trans (iteration_frame k (color i) s) uf⟩

/-- Filtering is executed from the original physical rows and color cells; no
selected-row or original-ordinal output bank is assumed at entry. -/
theorem execution (M T C k O I B n : ℕ) (x : Fin n→ℂ)
    (row : ℕ→UniformInPlaceMachine.Row) (color : ℕ→ℕ) (s : State)
    (header:Header M T C k O I s) (pc:s.pc=0) (src:Rows T M row s) (cols:Colors C M color s)
    (hT:T+3*M ≤ O) (hC:C+M ≤ O) (hO:O+3*M ≤ I) (hI:I+M ≤ B)
    (hB:30 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (scanCost k color 0 M+7) u ∧
    scanCost k color 0 M+7 ≤ runtimeBudget M ∧ u.pc=29 ∧ Header M T C k O I u ∧
    u.natReg 894=(selected M k color).length ∧
    OutputRows O (selected M k color) row u ∧ Ordinals I (selected M k color) u ∧
    Rows T M row u ∧ Colors C M color u ∧ Outside O M I s u ∧ Frame s u := by
  have rd:readable boot s:=by simp [readable,boot,Op.readable]
  have pk:peak boot s ≤ B:=by simp [peak,boot,Op.peak];omega
  have start:=block_runs boot program 0 n B x s boot_code pc hs
    (by change 0+5 ≤ B;omega) rd pk
  obtain ⟨w,rw,wc,wp,wo,ws,wk,out,fr⟩:=loop M B n x row color (applyBlock boot s)
    (boot_cursor header pc) (by omega) src cols hT hC hO hI
    (by intro j hj;change j < 0 at hj;omega) (by intro j hj;change j < 0 at hj;omega)
    hB start.final_bound
  have last:=branch_runs program B n 893 880 6 29 x w
    (by rw [wc.pc];exact outer_at) rw.final_bound (by omega) (by omega)
  have cmp:¬w.natReg 893 < w.natReg 880:=by rw [wc.index,wc.fixed.header.count];omega
  simp only [cmp,ite_false] at last
  let u:=setPC w 29
  have halt:step program n x u=.halted u:=by simp [step,u,setPC,halt_at]
  have run:BoundedExecution program n x B s (scanCost k color 0 M+7) u:=by
    convert start.executes (rw.executes (last.executes (BoundedExecution.halt last.final_bound halt))) using 1
    change scanCost k color 0 M+7=5+(scanCost k color 0 M+(1+1));omega
  refine ⟨u,run,?_,rfl,?_,wc.count,wp,wo,ws,wk,?_,?_⟩
  · have cost:=scanCost_bound k color 0 M
    unfold runtimeBudget;omega
  · exact ⟨wc.fixed.header.count,wc.fixed.header.source,wc.fixed.header.colors,
      wc.fixed.header.selectedColor,wc.fixed.header.output,wc.fixed.header.ordinals⟩
  · intro a ha hi;exact out a ha hi
  · exact frame_trans (boot_frame s) (frame_trans fr ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩)

def selectedRow (M k : ℕ) (color : ℕ→ℕ) (row : ℕ→UniformInPlaceMachine.Row)
    (j : ℕ) : UniformInPlaceMachine.Row :=
  if hj:j < (selected M k color).length then row (selected M k color)[j] else ⟨0,0,0⟩

theorem selected_rows (M k O : ℕ) (color : ℕ→ℕ) (row : ℕ→UniformInPlaceMachine.Row)
    (s : State) (h:OutputRows O (selected M k color) row s) :
    Rows O (selected M k color).length (selectedRow M k color row) s := by
  intro j hj
  simpa only [selectedRow,dite_eq_left hj] using h j hj

def selectionIndex (M k : ℕ) (color : ℕ→ℕ) (j : Fin (selected M k color).length) : Fin M :=
  ⟨(selected M k color)[j.val],((selected_mem M k color _).mp (List.getElem_mem j.isLt)).1⟩

theorem selectionIndex_color (M k : ℕ) (color : ℕ→ℕ) (j : Fin (selected M k color).length) :
    color (selectionIndex M k color j).val=k :=
  ((selected_mem M k color _).mp (List.getElem_mem j.isLt)).2

theorem selectionIndex_injective (M k : ℕ) (color : ℕ→ℕ) :
    Function.Injective (selectionIndex M k color) := by
  intro i j h
  apply Fin.ext
  exact (selected_nodup M k color).getElem_inj_iff.mp (congrArg Fin.val h)

def selectedEdges {M : ℕ} (E : Fin M→Edge) (k : ℕ) (color : ℕ→ℕ) :
    Fin (selected M k color).length→Edge := fun j=>E (selectionIndex M k color j)

theorem selected_matching {M : ℕ} (E : Fin M→Edge) (k : ℕ) (color : ℕ→ℕ)
    (hd:DegreeBound E 6) (actual:∀i:Fin M,color i.val=coloring E 6 i) :
    UniformMatchingAxisTableMachine.Matching (selectedEdges E k color) := by
  intro i j ne
  have nij:selectionIndex M k color i ≠ selectionIndex M k color j :=
    fun h=>ne (selectionIndex_injective M k color h)
  apply same_color_disjoint E hd (by omega) _ _ nij
  have ci:=selectionIndex_color M k color i
  have cj:=selectionIndex_color M k color j
  simp only [actual] at ci cj
  exact ci.trans cj.symm

theorem selected_inRange {r M : ℕ} (E : Fin M→Edge) (k : ℕ) (color : ℕ→ℕ)
    (hr:UniformMatchingAxisTableMachine.InRange r E) :
    UniformMatchingAxisTableMachine.InRange r (selectedEdges E k color) :=
  fun i=>hr (selectionIndex M k color i)

theorem selected_physical_edges {M O : ℕ} (E : Fin M→Edge) (k : ℕ) (color : ℕ→ℕ)
    (row : ℕ→UniformInPlaceMachine.Row) (s : State)
    (align:∀i:Fin M,(row i.val).dst=(E i).left ∧ (row i.val).src=(E i).right)
    (h:OutputRows O (selected M k color) row s) :
    UniformMatchingAxisTableMachine.Edges (selectedEdges E k color) O s := by
  intro i
  have rows:=h i.val i.isLt
  have eq:=align (selectionIndex M k color i)
  exact ⟨rows.1.trans (congrArg some eq.1),rows.2.1.trans (congrArg some eq.2)⟩

/-- A Color51-generated physical color bank gives actual matching rows for
Matching55. Degree six is scoped to this input row set, never the full cross graph. -/
theorem execution_matching (r M T C k O I B n : ℕ) (x : Fin n→ℂ)
    (E : Fin M→Edge) (row : ℕ→UniformInPlaceMachine.Row) (s : State)
    (header:Header M T C k O I s) (pc:s.pc=0) (src:Rows T M row s)
    (colors:UniformGreedyColorMachine.Colors E C M s) (hd:DegreeBound E 6)
    (align:∀i:Fin M,(row i.val).dst=(E i).left ∧ (row i.val).src=(E i).right)
    (hr:UniformMatchingAxisTableMachine.InRange r E)
    (hT:T+3*M ≤ O) (hC:C+M ≤ O) (hO:O+3*M ≤ I) (hI:I+M ≤ B)
    (hB:30 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (scanCost k (greedy E 11 M) 0 M+7) u ∧
    scanCost k (greedy E 11 M) 0 M+7 ≤ runtimeBudget M ∧ u.pc=29 ∧
    u.natReg 894=(selected M k (greedy E 11 M)).length ∧
    Rows O (selected M k (greedy E 11 M)).length (selectedRow M k (greedy E 11 M) row) u ∧
    Ordinals I (selected M k (greedy E 11 M)) u ∧
    UniformMatchingAxisTableMachine.Edges (selectedEdges E k (greedy E 11 M)) O u ∧
    UniformMatchingAxisTableMachine.Matching (selectedEdges E k (greedy E 11 M)) ∧
    UniformMatchingAxisTableMachine.InRange r (selectedEdges E k (greedy E 11 M)) ∧
    Header M T C k O I u ∧ Rows T M row u ∧ Colors C M (greedy E 11 M) u ∧
    Outside O M I s u ∧ Frame s u := by
  have cols:Colors C M (greedy E 11 M) s:=by intro i hi;exact colors ⟨i,hi⟩ hi
  obtain ⟨u,run,cost,pc',header',count,rows,ordinals,src',cols',out,fr⟩:=
    execution M T C k O I B n x row (greedy E 11 M) s header pc src cols hT hC hO hI hB hs
  exact ⟨u,run,cost,pc',count,selected_rows M k O _ row u rows,ordinals,
    selected_physical_edges E k _ row u align rows,selected_matching E k _ hd (fun _=>rfl),
    selected_inRange E k _ hr,header',src',cols',out,fr⟩

end
end ExactFourierCircuits.UniformColorLayerTableMachine
