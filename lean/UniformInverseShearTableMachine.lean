import UniformCrossShearTableMachine
import UniformReplayCoefficientMachine
import UniformRadixInstructionMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseShearTableMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Nat980=count,981=actual forward triples,982=fresh inverse triples,
983=positive coefficient bank,984=negative bank,985=six-constant bank.
Scratch Nat990..1000. Reverse the rows and negate the physical coefficient
address; every scalar bank, dependence tag and external register is retained. -/
def boot : List Op := [.literal 990 0,.literal 991 1,.literal 992 3,.literal 993 0]
def reads : List Op := [.sub 994 980 993,.sub 994 994 991,
  .mul 995 994 992,.add 995 981 995,.getNat 996 995,
  .add 995 995 991,.getNat 997 995,.add 995 995 991,.getNat 998 995]
def positive : List Op := [.sub 999 998 983,.add 998 984 999]
def offset : List Op := [.sub 999 998 985]
def positiveUnit : List Op := [.add 998 985 991]
def negativeUnit : List Op := [.add 998 985 990]
def normalization : List Op := [.add 998 998 991]
def stores : List Op := [.mul 1000 993 992,.add 1000 982 1000,
  .putNat 1000 996,.add 1000 1000 991,.putNat 1000 997,
  .add 1000 1000 991,.putNat 1000 998,.add 993 993 991]
def program : Program := boot.map Op.code ++ [.branchLT 993 980 5 35] ++
  reads.map Op.code ++ [.branchLT 998 985 15 18] ++ positive.map Op.code ++
  [.jump 26] ++ offset.map Op.code ++ [.branchLT 999 991 20 22] ++
  positiveUnit.map Op.code ++ [.jump 26,.branchLT 991 999 25 23] ++
  negativeUnit.map Op.code ++ [.jump 26] ++ normalization.map Op.code ++
  stores.map Op.code ++ [.jump 4,.halt]

theorem program_length : program.length=36 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem reads_code : BlockAt reads program 5 := by
  intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem positive_code : BlockAt positive program 15 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem offset_code : BlockAt offset program 18 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem positiveUnit_code : BlockAt positiveUnit program 20 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem negativeUnit_code : BlockAt negativeUnit program 23 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem normalization_code : BlockAt normalization program 25 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem stores_code : BlockAt stores program 26 := by
  intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem outer_at : program[4]?=some (.branchLT 993 980 5 35) := rfl
theorem prepared_at : program[14]?=some (.branchLT 998 985 15 18) := rfl
theorem prepared_jump : program[17]?=some (.jump 26) := rfl
theorem unit_at : program[19]?=some (.branchLT 999 991 20 22) := rfl
theorem positive_jump : program[21]?=some (.jump 26) := rfl
theorem negative_at : program[22]?=some (.branchLT 991 999 25 23) := rfl
theorem negative_jump : program[24]?=some (.jump 26) := rfl
theorem next_at : program[34]?=some (.jump 4) := rfl
theorem halt_at : program[35]?=some .halt := rfl

/-- Actual forward-table domain. The signed and constant banks come from
ReplayCoefficient42; this producer never treats a shifted constant base as
a substituted inverse-coefficient policy. -/
def Domain (C P m q : ℕ) : Prop :=
  (∃ (j : ℕ), j < m ∧ q=C+j) ∨ q=P ∨ q=P+1 ∨ q=P+2
def inverseAddress (C T P q : ℕ) :=
  if q < P then T+(q-C) else if q-P < 1 then P+1 else if q-P < 2 then P else q+1
def inverseRow (C T P : ℕ) (row : UniformInPlaceMachine.Row) : UniformInPlaceMachine.Row :=
  ⟨row.dst,row.src,inverseAddress C T P row.coefficient⟩
def inverseRows (C T P : ℕ) (rows : List UniformInPlaceMachine.Row) :=
  rows.reverse.map (inverseRow C T P)
def runtimeBudget (M : ℕ) := 25*M+6

theorem inverseAddress_prepared (C T P m j : ℕ) (hj:j < m) (h:C+m ≤ P) :
    inverseAddress C T P (C+j)=T+j := by
  have lt:C+j < P:=by omega
  simp [inverseAddress,lt]
theorem inverseAddress_unit (C T P : ℕ) : inverseAddress C T P P=P+1 := by
  simp [inverseAddress]
theorem inverseAddress_negativeUnit (C T P : ℕ) : inverseAddress C T P (P+1)=P := by
  simp [inverseAddress]
theorem inverseAddress_normalization (C T P : ℕ) : inverseAddress C T P (P+2)=P+3 := by
  simp [inverseAddress,Nat.add_assoc]
theorem inverseRows_length (C T P : ℕ) (rows : List UniformInPlaceMachine.Row) :
    (inverseRows C T P rows).length=rows.length := by simp [inverseRows]

noncomputable section
open UniformPairMachine (prepared)
open UniformRadixTwoDAG (width)

/-- Every physical inverse address stores the exact negative of the original
coefficient, including the K=0 reciprocal alias at P. -/
theorem inverse_coefficient {K C T P q : ℕ} {bank : ℕ→ℂ} {s : State}
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*width K ≤ P) (domain:Domain C P (7*width K) q) :
    ∃z,s.scalarHeap q=some (prepared z) ∧
      s.scalarHeap (inverseAddress C T P q)=some (prepared (-z)) := by
  obtain ⟨c0,c1,c2,c3,_,_⟩:=UniformReplayCoefficientMachine.constants_values constants
  rcases domain with ⟨j,hj,rfl⟩|rfl|rfl|rfl
  · rw [inverseAddress_prepared C T P _ j hj sep]
    exact ⟨bank j,pos j hj,neg j hj⟩
  · rw [inverseAddress_unit]
    exact ⟨1,c0,c1⟩
  · rw [inverseAddress_negativeUnit]
    exact ⟨-1,c1,by simpa using c0⟩
  · rw [inverseAddress_normalization]
    exact ⟨(width K:ℂ)⁻¹,c2,c3⟩

structure Header (M F O C T P : ℕ) (s : State) : Prop where
  count : s.natReg 980=M
  source : s.natReg 981=F
  output : s.natReg 982=O
  positive : s.natReg 983=C
  negative : s.natReg 984=T
  constants : s.natReg 985=P
structure Fixed (M F O C T P : ℕ) (s : State) : Prop where
  header : Header M F O C T P s
  zero : s.natReg 990=0
  one : s.natReg 991=1
  three : s.natReg 992=3
structure Cursor (M F O C T P i : ℕ) (s : State) : Prop where
  fixed : Fixed M F O C T P s
  pc : s.pc=4
  index : s.natReg 993=i
def Rows (F : ℕ) (rows : List UniformInPlaceMachine.Row) (s : State) : Prop :=
  ∀ (i : ℕ) (hi:i < rows.length),s.natHeap (F+3*i)=some rows[i].dst ∧
    s.natHeap (F+3*i+1)=some rows[i].src ∧
    s.natHeap (F+3*i+2)=some rows[i].coefficient
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀q,(q < 990 ∨ 1001 ≤ q)→u.natReg q=s.natReg q)
def Outside (O M : ℕ) (s u : State) : Prop :=
  ∀a,(a < O ∨ O+3*M ≤ a)→u.natHeap a=s.natHeap a
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun q hq=>(h'.2.2.2.2 q hq).trans (h.2.2.2.2 q hq)⟩

def readState (s : State) := applyBlock reads (setPC s 5)
theorem Fixed.withPC {M F O C T P : ℕ} {s : State}
    (h:Fixed M F O C T P s) (pc : ℕ) : Fixed M F O C T P (setPC s pc) :=
  ⟨⟨h.header.count,h.header.source,h.header.output,h.header.positive,
    h.header.negative,h.header.constants⟩,h.zero,h.one,h.three⟩
theorem boot_cursor {M F O C T P : ℕ} {s : State}
    (h:Header M F O C T P s) (hp:s.pc=0) :
    Cursor M F O C T P 0 (applyBlock boot s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,?_,?_⟩
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next,hp,
    h.count,h.source,h.output,h.positive,h.negative,h.constants]
theorem boot_frame (s : State) : Frame s (applyBlock boot s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
theorem read_spec {M F O C T P i : ℕ} {s : State}
    (row : UniformInPlaceMachine.Row) (h:Cursor M F O C T P i s)
    (hd:s.natHeap (F+3*(M-i-1))=some row.dst)
    (hs:s.natHeap (F+3*(M-i-1)+1)=some row.src)
    (hc:s.natHeap (F+3*(M-i-1)+2)=some row.coefficient) :
    (readState s).pc=14 ∧ (readState s).natReg 996=row.dst ∧
    (readState s).natReg 997=row.src ∧ (readState s).natReg 998=row.coefficient ∧
    Cursor M F O C T P i (setPC (readState s) 4) := by
  simp only [Nat.mul_comm,Nat.add_assoc] at hd hs hc
  refine ⟨?_,?_,?_,?_,⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_⟩⟩
  all_goals simp [readState,reads,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.output,
    h.fixed.header.positive,h.fixed.header.negative,h.fixed.header.constants,
    h.fixed.zero,h.fixed.one,h.fixed.three,h.index,Nat.add_assoc,hd,hs,hc]
theorem read_heap (s : State) : (readState s).natHeap=s.natHeap := rfl
theorem read_frame (s : State) : Frame s (readState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [readState,reads,applyBlock,Op.apply,setPC,writeNat,next]

theorem branch_runs (p : Program) (B n a b yes no : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:p[s.pc]?=some (.branchLT a b yes no)) (hs:WordBound B s)
    (hy:yes ≤ B) (hn:no ≤ B) :
    BoundedRuns p n x B s 1 (setPC s (if s.natReg a < s.natReg b then yes else no)) :=
  UniformRadixInstructionMachine.branch_runs p n B a b yes no x s hs hy hn hc
theorem jump_runs (p : Program) (B n target : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:p[s.pc]?=some (.jump target)) (hs:WordBound B s) (ht:target ≤ B) :
    BoundedRuns p n x B s 1 (setPC s target) :=
  UniformRadixInstructionMachine.jump_runs p n B target x s hs ht hc
theorem read_bounded {M F O C T P i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (row : UniformInPlaceMachine.Row) (h:Cursor M F O C T P i s)
    (hi:i < M) (hd:s.natHeap (F+3*(M-i-1))=some row.dst)
    (hr:s.natHeap (F+3*(M-i-1)+1)=some row.src)
    (hc:s.natHeap (F+3*(M-i-1)+2)=some row.coefficient)
    (hF:F+3*M ≤ B) (hB:36 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 10 (readState s) := by
  have first:=branch_runs program B n 993 980 5 35 x s
    (by rw [h.pc];exact outer_at) hs (by omega) (by omega)
  have cmp:s.natReg 993 < s.natReg 980:=by rw [h.index,h.fixed.header.count];exact hi
  simp only [cmp,ite_true] at first
  have dstB:row.dst ≤ B:=(hs.2.2.1 _ _ hd).2
  have srcB:row.src ≤ B:=(hs.2.2.1 _ _ hr).2
  have coeffB:row.coefficient ≤ B:=(hs.2.2.1 _ _ hc).2
  have countB:M ≤ B:=by simpa only [h.fixed.header.count] using hs.2.1 980
  have jlt:M-i-1 < M:=by omega
  simp only [Nat.mul_comm,Nat.add_assoc] at hd hr hc
  let v:=setPC s 5
  have rd:readable reads v:=by
    simp [readable,reads,Op.readable,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.source,h.index,h.fixed.one,h.fixed.three,
      Nat.add_assoc,hd,hr,hc]
  have pk:peak reads v ≤ B:=by
    simp [peak,reads,Op.peak,Op.apply,v,setPC,writeNat,next,
      h.fixed.header.count,h.fixed.header.source,h.index,h.fixed.one,h.fixed.three,
      Nat.add_assoc,hd,hr,hc]
    omega
  have body:=block_runs reads program 5 n B x v reads_code rfl first.final_bound
    (by change 5+9 ≤ B;omega) rd pk
  simpa only [show reads.length=9 from rfl,readState,v] using first.trans body

def mapState (P q : ℕ) (s : State) :=
  if q < P then setPC (applyBlock positive (setPC s 15)) 26 else
  let v:=applyBlock offset (setPC s 18)
  if q-P < 1 then setPC (applyBlock positiveUnit (setPC v 20)) 26 else
  if q-P < 2 then setPC (applyBlock negativeUnit (setPC v 23)) 26 else
    setPC (applyBlock normalization (setPC v 25)) 26

def mapCost (P q : ℕ) := if q < P then 4 else if q-P < 1 then 5 else if q-P < 2 then 6 else 5

theorem mapCost_bound (P q : ℕ) : mapCost P q ≤ 6 := by
  unfold mapCost;split_ifs <;> omega

theorem readState_setPC (s : State) (pc : ℕ) : readState (setPC s pc)=readState s := rfl
theorem setPC_heap (s : State) (pc : ℕ) : (setPC s pc).natHeap=s.natHeap := rfl

theorem mapState_heap (P q : ℕ) (s : State) : (mapState P q s).natHeap=s.natHeap := by
  unfold mapState;split_ifs <;> rfl

theorem mapState_frame (P q : ℕ) (s : State) : Frame s (mapState P q s) := by
  unfold mapState;split_ifs
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro j hj
  all_goals simp (disch:=omega) [positive,offset,positiveUnit,negativeUnit,normalization,
    applyBlock,Op.apply,setPC,writeNat,next]

structure StoreCursor (M F O C T P i : ℕ) (row : UniformInPlaceMachine.Row) (s : State) : Prop where
  fixed : Fixed M F O C T P s
  pc : s.pc=26
  index : s.natReg 993=i
  dst : s.natReg 996=row.dst
  src : s.natReg 997=row.src
  coefficient : s.natReg 998=row.coefficient

theorem Fixed.ofPC {M F O C T P pc : ℕ} {s : State}
    (h:Fixed M F O C T P (setPC s pc)) : Fixed M F O C T P s :=
  ⟨⟨h.header.count,h.header.source,h.header.output,h.header.positive,h.header.negative,h.header.constants⟩,
    h.zero,h.one,h.three⟩

theorem mapState_cursor {M F O C T P i : ℕ} {s : State} (row : UniformInPlaceMachine.Row)
    (h:Cursor M F O C T P i (setPC s 4)) (dst:s.natReg 996=row.dst)
    (src:s.natReg 997=row.src) (coef:s.natReg 998=row.coefficient) :
    StoreCursor M F O C T P i (inverseRow C T P row) (mapState P row.coefficient s) := by
  have hf:=Fixed.ofPC h.fixed
  have index:s.natReg 993=i:=h.index
  unfold mapState
  split_ifs
  all_goals refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_,?_,?_⟩
  all_goals simp (disch:=omega) [positive,offset,positiveUnit,negativeUnit,normalization,
    applyBlock,Op.apply,setPC,writeNat,next,inverseRow,inverseAddress,
    hf.header.count,hf.header.source,hf.header.output,
    hf.header.positive,hf.header.negative,hf.header.constants,
    hf.zero,hf.one,hf.three, *]

theorem inverseAddress_bound (C T P m q B : ℕ) (dom:Domain C P m q)
    (hC:C+m ≤ T) (hT:T+m ≤ P) (hP:P+3 ≤ B) : inverseAddress C T P q ≤ B := by
  rcases dom with ⟨j,hj,rfl⟩|rfl|rfl|rfl
  · rw [inverseAddress_prepared C T P m j hj (by omega)];omega
  · rw [inverseAddress_unit];omega
  · rw [inverseAddress_negativeUnit];omega
  · rw [inverseAddress_normalization];omega

/-- Four literal address-mapping paths; scalar values are never inspected. -/
theorem map_bounded {M F O C T P i : ℕ} (B n m : ℕ) (x : Fin n→ℂ)
    (row : UniformInPlaceMachine.Row) (s : State) (h:Cursor M F O C T P i (setPC s 4))
    (pc:s.pc=14) (coef:s.natReg 998=row.coefficient)
    (dom:Domain C P m row.coefficient) (hC:C+m ≤ T) (hT:T+m ≤ P)
    (hP:P+3 ≤ B) (hB:36 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s (mapCost P row.coefficient) (mapState P row.coefficient s) := by
  have hf:=Fixed.ofPC h.fixed
  have mappedBound:=inverseAddress_bound C T P m row.coefficient B dom hC hT hP
  have first:=branch_runs program B n 998 985 15 18 x s
    (by rw [pc];exact prepared_at) hs (by omega) (by omega)
  have kreg:s.natReg 985=P:=hf.header.constants
  by_cases lt:row.coefficient < P
  · have cmp:s.natReg 998 < s.natReg 985:=by rw [coef,kreg];exact lt
    simp only [cmp,ite_true] at first
    have rd:readable positive (setPC s 15):=by simp [readable,positive,Op.readable]
    have pk:peak positive (setPC s 15) ≤ B:=by
      simp [peak,positive,Op.peak,Op.apply,setPC,writeNat,next,
        coef,hf.header.positive,hf.header.negative]
      simp only [inverseAddress,lt,ite_true] at mappedBound
      have qb:row.coefficient ≤ B:=by simpa only [coef] using hs.2.1 998
      omega
    have body:=block_runs positive program 15 n B x (setPC s 15) positive_code rfl first.final_bound
      (by change 15+2 ≤ B;omega) rd pk
    have bp:(applyBlock positive (setPC s 15)).pc=17:=by
      rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have jump:=jump_runs program B n 26 x (applyBlock positive (setPC s 15))
      (by rw [bp];exact prepared_jump) body.final_bound (by omega)
    simpa only [mapState,mapCost,lt,ite_true,show positive.length=2 from rfl] using first.trans (body.trans jump)
  · have cmp:¬s.natReg 998 < s.natReg 985:=by rw [coef,kreg];exact lt
    simp only [cmp,ite_false] at first
    have rd:readable offset (setPC s 18):=by simp [readable,offset,Op.readable]
    have pk:peak offset (setPC s 18) ≤ B:=by
      simp [peak,offset,Op.peak,setPC,coef,kreg]
      have qb:row.coefficient ≤ B:=by simpa only [coef] using hs.2.1 998
      omega
    have off:=block_runs offset program 18 n B x (setPC s 18) offset_code rfl first.final_bound
      (by change 18+1 ≤ B;omega) rd pk
    let v:=applyBlock offset (setPC s 18)
    have vp:v.pc=19:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have vo:v.natReg 999=row.coefficient-P:=by simp [v,offset,applyBlock,Op.apply,setPC,writeNat,next,coef,kreg]
    have one:v.natReg 991=1:=by simp [v,offset,applyBlock,Op.apply,setPC,writeNat,next,hf.one]
    have constant:v.natReg 985=P:=by simp [v,offset,applyBlock,Op.apply,setPC,writeNat,next,kreg]
    have zero:v.natReg 990=0:=by simp [v,offset,applyBlock,Op.apply,setPC,writeNat,next,hf.zero]
    have co:v.natReg 998=row.coefficient:=by simp [v,offset,applyBlock,Op.apply,setPC,writeNat,next,coef]
    have unit:=branch_runs program B n 999 991 20 22 x v
      (by rw [vp];exact unit_at) off.final_bound (by omega) (by omega)
    by_cases u:row.coefficient-P < 1
    · have cmp':v.natReg 999 < v.natReg 991:=by rw [vo,one];exact u
      simp only [cmp',ite_true] at unit
      have rd:readable positiveUnit (setPC v 20):=by simp [readable,positiveUnit,Op.readable]
      have pk:peak positiveUnit (setPC v 20) ≤ B:=by simp [peak,positiveUnit,Op.peak,setPC,constant,one];omega
      have body:=block_runs positiveUnit program 20 n B x (setPC v 20) positiveUnit_code rfl unit.final_bound
        (by change 20+1 ≤ B;omega) rd pk
      have bp:(applyBlock positiveUnit (setPC v 20)).pc=21:=by
        rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
      have jump:=jump_runs program B n 26 x (applyBlock positiveUnit (setPC v 20))
        (by rw [bp];exact positive_jump) body.final_bound (by omega)
      simpa only [mapState,mapCost,lt,u,ite_false,ite_true,v,show offset.length=1 from rfl,
        show positiveUnit.length=1 from rfl] using first.trans (off.trans (unit.trans (body.trans jump)))
    · have cmp':¬v.natReg 999 < v.natReg 991:=by rw [vo,one];exact u
      simp only [cmp',ite_false] at unit
      have neg:=branch_runs program B n 991 999 25 23 x (setPC v 22)
        (by change program[22]?=some _;exact negative_at) unit.final_bound (by omega) (by omega)
      by_cases negu:row.coefficient-P < 2
      · have cmp'':¬(setPC v 22).natReg 991 < (setPC v 22).natReg 999:=by
          change ¬v.natReg 991 < v.natReg 999;rw [vo,one];omega
        simp only [cmp'',ite_false] at neg
        have rd:readable negativeUnit (setPC v 23):=by simp [readable,negativeUnit,Op.readable]
        have pk:peak negativeUnit (setPC v 23) ≤ B:=by simp [peak,negativeUnit,Op.peak,setPC,constant,zero];omega
        have body:=block_runs negativeUnit program 23 n B x (setPC v 23) negativeUnit_code rfl neg.final_bound
          (by change 23+1 ≤ B;omega) rd pk
        have bp:(applyBlock negativeUnit (setPC v 23)).pc=24:=by
          rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
        have jump:=jump_runs program B n 26 x (applyBlock negativeUnit (setPC v 23))
          (by rw [bp];exact negative_jump) body.final_bound (by omega)
        simpa only [mapState,mapCost,lt,u,negu,ite_false,ite_true,v,show offset.length=1 from rfl,
          show negativeUnit.length=1 from rfl] using first.trans (off.trans (unit.trans (neg.trans (body.trans jump))))
      · have cmp'':(setPC v 22).natReg 991 < (setPC v 22).natReg 999:=by
          change v.natReg 991 < v.natReg 999;rw [vo,one];omega
        simp only [cmp'',ite_true] at neg
        have rd:readable normalization (setPC v 25):=by simp [readable,normalization,Op.readable]
        have pk:peak normalization (setPC v 25) ≤ B:=by
          simp [peak,normalization,Op.peak,setPC,co,one]
          simp only [inverseAddress,lt,u,negu,ite_false] at mappedBound
          exact mappedBound
        have body:=block_runs normalization program 25 n B x (setPC v 25) normalization_code rfl neg.final_bound
          (by change 25+1 ≤ B;omega) rd pk
        have bp:(applyBlock normalization (setPC v 25)).pc=26:=by
          rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
        have reset:setPC (applyBlock normalization (setPC v 25)) 26=applyBlock normalization (setPC v 25):=by
          have := bp
          cases hstate:applyBlock normalization (setPC v 25)
          simp_all [setPC]
        simpa only [mapState,mapCost,lt,u,negu,ite_false,v,show offset.length=1 from rfl,
          show normalization.length=1 from rfl,reset] using first.trans (off.trans (unit.trans (neg.trans body)))

def storeEnd (s : State) := setPC (applyBlock stores s) 4

theorem storeEnd_heap {M F O C T P i : ℕ} {row : UniformInPlaceMachine.Row} {s : State}
    (h:StoreCursor M F O C T P i row s) :
    (storeEnd s).natHeap=Function.update (Function.update (Function.update s.natHeap
      (O+3*i) (some row.dst)) (O+3*i+1) (some row.src)) (O+3*i+2) (some row.coefficient) := by
  simp [storeEnd,stores,applyBlock,Op.apply,setPC,writeNat,next,h.index,h.fixed.three,
    h.fixed.header.output,h.fixed.one,h.dst,h.src,h.coefficient,Nat.mul_comm i 3,Nat.add_assoc]

theorem storeEnd_cursor {M F O C T P i : ℕ} {row : UniformInPlaceMachine.Row} {s : State}
    (h:StoreCursor M F O C T P i row s) : Cursor M F O C T P (i+1) (storeEnd s) := by
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_⟩
  all_goals simp [storeEnd,stores,applyBlock,Op.apply,setPC,writeNat,next,h.index,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.output,h.fixed.header.positive,
    h.fixed.header.negative,h.fixed.header.constants,h.fixed.zero,h.fixed.one,h.fixed.three]

theorem storeEnd_frame (s : State) : Frame s (storeEnd s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro q hq;simp (disch:=omega) [storeEnd,stores,applyBlock,Op.apply,setPC,writeNat,next]

theorem storeEnd_bounded {M F O C T P i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (row : UniformInPlaceMachine.Row) (s : State) (h:StoreCursor M F O C T P i row s)
    (hi:i < M) (hO:O+3*M ≤ B) (hB:36 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 9 (storeEnd s) := by
  have db:row.dst ≤ B:=by simpa only [h.dst] using hs.2.1 996
  have sb:row.src ≤ B:=by simpa only [h.src] using hs.2.1 997
  have cb:row.coefficient ≤ B:=by simpa only [h.coefficient] using hs.2.1 998
  have rd:readable stores s:=by simp [readable,stores,Op.readable]
  have pk:peak stores s ≤ B:=by
    simp (disch:=omega) [peak,stores,Op.peak,Op.apply,writeNat,next,h.index,h.fixed.three,
      h.fixed.header.output,h.fixed.one,h.dst,h.src,h.coefficient,Nat.mul_comm i 3,Nat.add_assoc,db,sb,cb]
    omega
  have body:=block_runs stores program 26 n B x s stores_code h.pc hs
    (by change 26+8 ≤ B;omega) rd pk
  have pc:(applyBlock stores s).pc=34:=by
    rw [UniformTensorMonomialMachine.applyBlock_pc,h.pc];rfl
  have last:=jump_runs program B n 4 x (applyBlock stores s)
    (by rw [pc];exact next_at) body.final_bound (by omega)
  simpa only [storeEnd,show stores.length=8 from rfl] using body.trans last

def iteration (P q : ℕ) (s : State) := storeEnd (mapState P q (readState s))

theorem iteration_frame (P q : ℕ) (s : State) : Frame s (iteration P q s) :=
  frame_trans (read_frame s) (frame_trans (mapState_frame P q (readState s))
    (storeEnd_frame (mapState P q (readState s))))

theorem inverseRows_get (C T P : ℕ) (rows : List UniformInPlaceMachine.Row)
    (i : ℕ) (hi:i < rows.length) :
    (inverseRows C T P rows)[i]'(by simpa only [inverseRows_length] using hi)=
      inverseRow C T P (rows[rows.length-i-1]'(by omega)) := by
  simp only [inverseRows,List.getElem_map,List.getElem_reverse,Nat.sub_sub,Nat.add_comm i 1]

theorem iteration_bounded {M F O C T P i : ℕ} (B n m : ℕ) (x : Fin n→ℂ)
    (rows : List UniformInPlaceMachine.Row) (s : State) (h:Cursor M F O C T P i s)
    (len:rows.length=M) (hi:i < M) (src:Rows F rows s)
    (dom:∀row∈rows,Domain C P m row.coefficient) (hC:C+m ≤ T) (hT:T+m ≤ P) (hP:P+3 ≤ B)
    (hF:F+3*M ≤ O) (hO:O+3*M ≤ B) (hB:36 ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s
      (19+mapCost P (rows[M-i-1]'(by omega)).coefficient)
      (iteration P (rows[M-i-1]'(by omega)).coefficient s) ∧
    Cursor M F O C T P (i+1) (iteration P (rows[M-i-1]'(by omega)).coefficient s) ∧
    (iteration P (rows[M-i-1]'(by omega)).coefficient s).natHeap=
      Function.update (Function.update (Function.update s.natHeap
        (O+3*i) (some ((inverseRows C T P rows)[i]'(by simp only [inverseRows_length];omega)).dst))
        (O+3*i+1) (some ((inverseRows C T P rows)[i]'(by simp only [inverseRows_length];omega)).src))
        (O+3*i+2) (some ((inverseRows C T P rows)[i]'(by simp only [inverseRows_length];omega)).coefficient) := by
  let row:=rows[M-i-1]'(by omega)
  obtain ⟨hd,hr,hcoef⟩:=src (M-i-1) (by omega)
  have readRun:=read_bounded B n x s row h hi hd hr hcoef (by omega) hB hs
  have spec:=read_spec row h hd hr hcoef
  have mapped:=map_bounded B n m x row (readState s) spec.2.2.2.2 spec.1 spec.2.2.2.1
    (dom row (List.getElem_mem (by omega))) hC hT hP hB readRun.final_bound
  have mc:=mapState_cursor row spec.2.2.2.2 spec.2.1 spec.2.2.1 spec.2.2.2.1
  have last:=storeEnd_bounded B n x (inverseRow C T P row)
    (mapState P row.coefficient (readState s)) mc hi hO hB mapped.final_bound
  refine ⟨?_,storeEnd_cursor mc,?_⟩
  · convert readRun.trans (mapped.trans last) using 1
    · simp only [row];omega
    · simp only [iteration,row]
  · rw [iteration,storeEnd_heap mc,mapState_heap,read_heap]
    have inv:=inverseRows_get C T P rows i (by omega)
    simp only [len] at inv
    simp only [inv,row]

def Prefix (O : ℕ) (rows : List UniformInPlaceMachine.Row) (i : ℕ) (s : State) : Prop :=
  ∀(j : ℕ)(hj:j < rows.length),j < i→s.natHeap (O+3*j)=some rows[j].dst ∧
    s.natHeap (O+3*j+1)=some rows[j].src ∧ s.natHeap (O+3*j+2)=some rows[j].coefficient

theorem prefix_step {O : ℕ} {rows : List UniformInPlaceMachine.Row} {i : ℕ} {s u : State}
    (hi:i < rows.length) (h:Prefix O rows i s)
    (heap:u.natHeap=Function.update (Function.update (Function.update s.natHeap
      (O+3*i) (some rows[i].dst)) (O+3*i+1) (some rows[i].src)) (O+3*i+2) (some rows[i].coefficient)) :
    Prefix O rows (i+1) u := by
  intro j hj ji;rw [heap]
  by_cases eq:j=i
  · subst j;simp
  · have old:=h j hj (by omega)
    simp (disch:=omega) [old.1,old.2.1,old.2.2]

theorem outside_trans {O M : ℕ} {s u v : State} (h:Outside O M s u) (h':Outside O M u v) :
    Outside O M s v:=fun a ha=>(h' a ha).trans (h a ha)

theorem rows_transport {F O M : ℕ} {rows : List UniformInPlaceMachine.Row} {s u : State}
    (h:Rows F rows s) (len:rows.length=M) (out:Outside O M s u) (hF:F+3*M ≤ O) : Rows F rows u := by
  intro j hj
  rw [out (F+3*j) (by omega),out (F+3*j+1) (by omega),out (F+3*j+2) (by omega)]
  exact h j hj

theorem iteration_outside {O M i : ℕ} {rows : List UniformInPlaceMachine.Row} {s u : State}
    (hi:i < rows.length) (len:rows.length=M)
    (heap:u.natHeap=Function.update (Function.update (Function.update s.natHeap
      (O+3*i) (some rows[i].dst)) (O+3*i+1) (some rows[i].src)) (O+3*i+2) (some rows[i].coefficient)) :
    Outside O M s u:=by
  intro a ha;rw [heap];simp (disch:=omega)

/-- The loop only receives the original physical table; its inverse prefix starts empty. -/
theorem loop {M F O C T P i : ℕ} (remaining B n m : ℕ) (x : Fin n→ℂ)
    (rows : List UniformInPlaceMachine.Row) (s : State) (h:Cursor M F O C T P i s)
    (len:rows.length=M) (hi:i+remaining=M) (src:Rows F rows s)
    (dom:∀row∈rows,Domain C P m row.coefficient) (hC:C+m ≤ T) (hT:T+m ≤ P) (hP:P+3 ≤ B)
    (hF:F+3*M ≤ O) (hO:O+3*M ≤ B)
    (pref:Prefix O (inverseRows C T P rows) i s) (hB:36 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ 25*remaining ∧ BoundedRuns program n x B s t u ∧ Cursor M F O C T P M u ∧
    Rows O (inverseRows C T P rows) u ∧ Rows F rows u ∧ Outside O M s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero=>
    have eq:i=M:=by omega
    subst i
    refine ⟨0,s,by omega,.refl hs,h,?_,src,fun _ _=>rfl,frame_refl s⟩
    intro j hj;exact pref j hj (by simpa only [inverseRows_length,len] using hj)
  | succ rem ih=>
    have il:i < M:=by omega
    obtain ⟨run,cur,heap⟩:=iteration_bounded B n m x rows s h len il src dom hC hT hP hF hO hB hs
    have out:=iteration_outside (by simpa only [inverseRows_length,len] using il)
      (by simpa only [inverseRows_length] using len) heap
    obtain ⟨t,u,tc,ru,uc,ui,us,uo,uf⟩:=ih (i:=i+1) _ cur (by omega)
      (rows_transport src len out hF) (prefix_step (by simpa only [inverseRows_length,len] using il) pref heap)
      run.final_bound
    refine ⟨19+mapCost P (rows[M-i-1]'(by omega)).coefficient+t,u,?_,run.trans ru,
      uc,ui,us,outside_trans out uo,frame_trans (iteration_frame P _ s) uf⟩
    have mc:=mapCost_bound P (rows[M-i-1]'(by omega)).coefficient
    omega

/-- Startup and halt are charged. The inverse rows are built from the original
physical rows, without an inverse table or negative-action premise. -/
theorem execution (M F O C T P m B n : ℕ) (x : Fin n→ℂ)
    (rows : List UniformInPlaceMachine.Row) (s : State)
    (header:Header M F O C T P s) (pc:s.pc=0) (len:rows.length=M) (src:Rows F rows s)
    (dom:∀row∈rows,Domain C P m row.coefficient)
    (hC:C+m ≤ T) (hT:T+m ≤ P) (hP:P+3 ≤ B)
    (hF:F+3*M ≤ O) (hO:O+3*M ≤ B) (hB:36 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ runtimeBudget M ∧ BoundedExecution program n x B s t u ∧
    u.pc=35 ∧ Header M F O C T P u ∧
    Rows O (inverseRows C T P rows) u ∧ Rows F rows u ∧ Outside O M s u ∧ Frame s u := by
  have rd:readable boot s:=by simp [readable,boot,Op.readable]
  have pk:peak boot s ≤ B:=by simp [peak,boot,Op.peak];omega
  have start:=block_runs boot program 0 n B x s boot_code pc hs
    (by change 0+4 ≤ B;omega) rd pk
  obtain ⟨t,w,tc,rw,wc,wi,ws,out,fr⟩:=loop M B n m x rows (applyBlock boot s)
    (boot_cursor header pc) len (by omega) src dom hC hT hP hF hO
    (by intro j hj ji;omega) hB start.final_bound
  have last:=branch_runs program B n 993 980 5 35 x w
    (by rw [wc.pc];exact outer_at) rw.final_bound (by omega) (by omega)
  have cmp:¬w.natReg 993 < w.natReg 980:=by rw [wc.index,wc.fixed.header.count];omega
  simp only [cmp,ite_false] at last
  let u:=setPC w 35
  have halt:step program n x u=.halted u:=by simp [step,u,setPC,halt_at]
  have run:BoundedExecution program n x B s (t+6) u:=by
    convert start.executes (rw.executes (last.executes (BoundedExecution.halt last.final_bound halt))) using 1
    change t+6=4+(t+(1+1));omega
  refine ⟨t+6,u,?_,run,rfl,?_,wi,ws,?_,?_⟩
  · unfold runtimeBudget;omega
  · exact ⟨wc.fixed.header.count,wc.fixed.header.source,wc.fixed.header.output,
      wc.fixed.header.positive,wc.fixed.header.negative,wc.fixed.header.constants⟩
  · intro a ha;exact out a ha
  · exact frame_trans (boot_frame s) (frame_trans fr ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩)

/-- All produced inverse-row coefficients are prepared exact negatives in the
unchanged scalar heap. Coefficient-bank preparation remains an explicit input. -/
theorem inverseRows_coefficients {K C T P : ℕ} {bank : ℕ→ℂ} {s u : State}
    (rows : List UniformInPlaceMachine.Row)
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*width K ≤ P) (domain:∀row∈rows,Domain C P (7*width K) row.coefficient)
    (frame:Frame s u) (i : ℕ) (hi:i < rows.length) : ∃z,
    u.scalarHeap (rows[rows.length-i-1]'(by omega)).coefficient=some (prepared z) ∧
    u.scalarHeap ((inverseRows C T P rows)[i]'(by simp only [inverseRows_length];exact hi)).coefficient=
      some (prepared (-z)) := by
  obtain ⟨z,hz,hn⟩:=inverse_coefficient
    (q:=(rows[rows.length-i-1]'(by omega)).coefficient) pos neg constants sep
    (domain _ (List.getElem_mem (by omega)))
  refine ⟨z,?_,?_⟩
  · rw [frame.1];exact hz
  · rw [inverseRows_get C T P rows i hi,frame.1];exact hn


open UniformCrossShearTableMachine (emit directRows locations GoodExpr GoodCoefficient)

/-- A retained source reference has exactly the coefficient address passed to emit. -/
theorem emit_domain (n A dst src q C P m : ℕ) (enabled : Bool) (h:Domain C P m q) :
    ∀row∈emit n A dst src q enabled,Domain C P m row.coefficient := by
  unfold emit;split
  · intro row hr;simp only [List.mem_singleton] at hr;subst row;exact h
  · simp

theorem rational_address_domain (r C Z P m : ℕ) (q : ℚ) :
    Domain C P m ((locations r C Z P).address (.rational q)) := by
  simp only [UniformInPlaceMachine.Locations.address,locations]
  split_ifs <;> simp [Domain]

/-- Typed forward cross expressions contain only positive prepared references
and the reciprocal leaf. Fin indices give the strict prepared-bank bound. -/
theorem directRows_domain (K n A C Z P j : ℕ) (enabled : Bool)
    (g : UniformConvolutionDAG.Expr (UniformToeplitzCrossDAG.bankSize K) ℕ)
    (h:GoodExpr (width K) g) :
    ∀row∈directRows n A (locations (UniformToeplitzCrossDAG.bankSize K) C Z P) j enabled g,
      Domain C P (7*width K) row.coefficient := by
  cases g with
  | add a b=>
    intro row hr;rcases List.mem_append.mp hr with hr|hr
    · exact emit_domain _ _ _ _ _ _ _ _ enabled (rational_address_domain _ _ _ _ _ 1) row hr
    · exact emit_domain _ _ _ _ _ _ _ _ enabled (rational_address_domain _ _ _ _ _ 1) row hr
  | sub a b=>
    intro row hr;rcases List.mem_append.mp hr with hr|hr
    · exact emit_domain _ _ _ _ _ _ _ _ enabled (rational_address_domain _ _ _ _ _ 1) row hr
    · exact emit_domain _ _ _ _ _ _ _ _ enabled (rational_address_domain _ _ _ _ _ (-1)) row hr
  | scale c a=>
    rcases h with rfl|⟨i,rfl⟩
    · exact emit_domain _ _ _ _ _ _ _ _ enabled (rational_address_domain _ _ _ _ _ _)
    · exact emit_domain _ _ _ _ _ _ _ _ enabled
        (Or.inl ⟨i.val,by have lt:=i.isLt;unfold UniformToeplitzCrossDAG.bankSize at lt;omega,rfl⟩)

/-- The actual typed stable cross sweep satisfies the physical domain needed by
Inverse36; it is not inferred from the weaker inclusive row payload bound. -/
theorem typed_orderedRows_domain {n t : ℕ} (K A C Z P : ℕ)
    (p : UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize K) n t)
    (good:∀g∈UniformToeplitzCrossDAG.programRecords p,GoodExpr (width K) g) (enabled : Bool) :
    ∀row∈UniformCrossShearTableMachine.orderedRows n A C P enabled
      (UniformCrossShearTableMachine.rowAt p)
      (UniformDAGBucketMachine.order t (UniformDAGBucketMachine.typedDepth p)),
      Domain C P (7*width K) row.coefficient := by
  intro row hr
  obtain ⟨j,hj,hr⟩:=List.mem_flatMap.mp hr
  have hj':j < t:=((UniformDAGBucketMachine.order_mem t _ j).mp hj).1
  unfold UniformCrossShearTableMachine.rowAt at hr
  rw [UniformCrossShearTableMachine.expansion_typed K n A C Z P j enabled
    (UniformCrossShearTableMachine.exprAt p j)
    (good _ (UniformCrossShearTableMachine.exprAt_mem p j hj'))] at hr
  exact directRows_domain K n A C Z P j enabled _
    (good _ (UniformCrossShearTableMachine.exprAt_mem p j hj')) row hr

theorem cross_orderedRows_domain (K a e A C Z P : ℕ) (enabled : Bool)
    (ha:a ≤ width K) (he:e ≤ width K) :
    let p:=(UniformToeplitzCrossDAG.crossDAG K a e ha he).program
    ∀row∈UniformCrossShearTableMachine.orderedRows e A C P enabled
      (UniformCrossShearTableMachine.rowAt p)
      (UniformDAGBucketMachine.order (UniformToeplitzCrossDAG.crossDAG K a e ha he).size
        (UniformDAGBucketMachine.typedDepth p)),Domain C P (7*width K) row.coefficient :=
  typed_orderedRows_domain K A C Z P _ (UniformCrossShearTableMachine.cross_good K a e ha he) enabled

/-- Pure row action is the exact scalar update used by InPlace19. This does not
assert that Inverse36 itself executes any scalar updates. -/
def rowAction (value : ℕ→ℂ) (row : UniformInPlaceMachine.Row) (v : ℕ→ℂ) : ℕ→ℂ :=
  fun a=>if a=row.dst then v a+value row.coefficient*v row.src else v a

def rowsAction (value : ℕ→ℂ) (rows : List UniformInPlaceMachine.Row) (v : ℕ→ℂ) : ℕ→ℂ :=
  rows.foldl (fun v row=>rowAction value row v) v

theorem rowAction_inverse (C T P : ℕ) (value : ℕ→ℂ) (row : UniformInPlaceMachine.Row)
    (different:row.dst≠row.src) (negative:value (inverseAddress C T P row.coefficient)= -value row.coefficient)
    (v : ℕ→ℂ) : rowAction value (inverseRow C T P row) (rowAction value row v)=v := by
  funext a
  by_cases h:a=row.dst
  · subst a
    simp [rowAction,inverseRow,negative,different.symm]
  · simp [rowAction,inverseRow,h]

/-- Arbitrary dirty arrays are restored by reversed exact-negated rows. -/
theorem rowsAction_inverse (C T P : ℕ) (value : ℕ→ℂ) (rows : List UniformInPlaceMachine.Row)
    (different:∀row∈rows,row.dst≠row.src)
    (negative:∀row∈rows,value (inverseAddress C T P row.coefficient)= -value row.coefficient)
    (v : ℕ→ℂ) : rowsAction value (inverseRows C T P rows) (rowsAction value rows v)=v := by
  induction rows generalizing v with
  | nil=>rfl
  | cons row rows ih=>
    simp only [inverseRows,List.reverse_cons,List.map_append,List.map_singleton,
      rowsAction,List.foldl_cons,List.foldl_append,List.foldl_nil]
    change rowAction value (inverseRow C T P row)
      (rowsAction value (inverseRows C T P rows) (rowsAction value rows (rowAction value row v)))=v
    rw [ih (fun r hr=>different r (by simp [hr])) (fun r hr=>negative r (by simp [hr]))]
    exact rowAction_inverse C T P value row (different row (by simp)) (negative row (by simp)) v

def heapCoefficient (s : State) (q : ℕ) : ℂ := ((s.scalarHeap q).getD (prepared 0)).value

theorem heapCoefficient_negative {K C T P q : ℕ} {bank : ℕ→ℂ} {s : State}
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*width K ≤ P) (domain:Domain C P (7*width K) q) :
    heapCoefficient s (inverseAddress C T P q)= -heapCoefficient s q := by
  obtain ⟨z,hz,hn⟩:=inverse_coefficient pos neg constants sep domain
  simp only [heapCoefficient,hz,hn,Option.getD_some,UniformPairMachine.prepared]

theorem physical_inverse_action {K C T P : ℕ} {bank : ℕ→ℂ} {s : State}
    (rows : List UniformInPlaceMachine.Row)
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*width K ≤ P) (domain:∀row∈rows,Domain C P (7*width K) row.coefficient)
    (different:∀row∈rows,row.dst≠row.src) (v : ℕ→ℂ) :
    rowsAction (heapCoefficient s) (inverseRows C T P rows)
      (rowsAction (heapCoefficient s) rows v)=v :=
  rowsAction_inverse C T P (heapCoefficient s) rows different
    (fun row hr=>heapCoefficient_negative pos neg constants sep (domain row hr)) v


theorem Frame.saved {s u : State} (f:Frame s u) (j : ℕ) (h:100 ≤ j ∧ j ≤ 106) :
    u.natReg j=s.natReg j:=f.2.2.2.2 j (by omega)

/-- The actual table producer plus internally derived signed-coefficient
semantics. Its concluding row action is an algebraic contract for the subsequent
scalar interpreter, not an execution claim for that interpreter. -/
theorem execution_signed (K M F O C T P B n : ℕ) (x : Fin n→ℂ)
    (rows : List UniformInPlaceMachine.Row) (bank : ℕ→ℂ) (s : State)
    (header:Header M F O C T P s) (pc:s.pc=0) (len:rows.length=M) (src:Rows F rows s)
    (dom:∀row∈rows,Domain C P (7*width K) row.coefficient)
    (different:∀row∈rows,row.dst≠row.src)
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (hC:C+7*width K ≤ T) (hT:T+7*width K ≤ P) (hP:P+3 ≤ B)
    (hF:F+3*M ≤ O) (hO:O+3*M ≤ B) (hB:36 ≤ B) (hs:WordBound B s) : ∃t u,
    t ≤ runtimeBudget M ∧ BoundedExecution program n x B s t u ∧ u.pc=35 ∧
    Header M F O C T P u ∧ Rows O (inverseRows C T P rows) u ∧ Rows F rows u ∧
    Outside O M s u ∧ Frame s u ∧
    (∀(i : ℕ)(hi:i < rows.length),∃z,
      u.scalarHeap (rows[rows.length-i-1]'(by omega)).coefficient=some (prepared z) ∧
      u.scalarHeap ((inverseRows C T P rows)[i]'(by simp only [inverseRows_length];exact hi)).coefficient=
        some (prepared (-z))) ∧
    ∀v:ℕ→ℂ,rowsAction (heapCoefficient u) (inverseRows C T P rows)
      (rowsAction (heapCoefficient u) rows v)=v := by
  obtain ⟨t,u,tc,run,pu,hu,inv,orig,out,fr⟩:=execution M F O C T P (7*width K) B n x rows s
    header pc len src dom hC hT hP hF hO hB hs
  refine ⟨t,u,tc,run,pu,hu,inv,orig,out,fr,?_,?_⟩
  · exact inverseRows_coefficients rows pos neg constants (by omega) dom fr
  · intro v
    have same:heapCoefficient u=heapCoefficient s:=by funext q;unfold heapCoefficient;rw [fr.1]
    rw [same]
    exact physical_inverse_action rows pos neg constants (by omega) dom different v

end
end ExactFourierCircuits.UniformInverseShearTableMachine
