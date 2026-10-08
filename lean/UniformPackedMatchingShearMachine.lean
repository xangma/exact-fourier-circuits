import UniformZeroFreePairShearMachine
import UniformMatchingConjugateLoadMachine
import UniformScalarScatterMachine
import UniformSeedChunkPackingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPackedMatchingShearMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
open UniformInPlaceMachine (Row)
open UniformCrossShearTableMachine (Table)
open UniformMatchingConjugateLoadMachine (Coefficient)
noncomputable section

/-- Caller allocations only; the actual generated count is read from Nat894. -/
structure Config where
 length : ℕ
 packed : ℕ
 destination : ℕ
 inverse : ℕ
 rows : ℕ
 positive : ℕ
 negative : ℕ
 constants : ℕ
 conjugates : ℕ
 mu : ℕ
 conjugateMu : ℕ

def boot : List Op := [.literal 1660 0,.literal 1661 1,.literal 1662 2,.literal 1663 0,
 .add 1664 894 1663,.add 2100 1645 1663,.add 2101 1646 1663,.add 2102 1647 1663,
 .add 2103 1648 1663,.add 2106 1649 1663,.add 2107 1650 1663]
def rowSetup : List Op := [.add 2140 1644 1663,.add 2141 1660 1663]
def pairSetup : List Op := [.mul 1620 1660 1662,.add 1620 1641 1620,
 .add 1621 1620 1661,.add 1622 1649 1663,.add 1623 1650 1663]
def tick : List Op := [.add 1660 1660 1661]
def scatterSetup : List Op := [.add 1506 1640 1663,.add 1507 1641 1663,
 .add 1508 1642 1663,.add 1509 1643 1663]
def beforeRow : Program := boot.map Op.code++[.branchLT 1660 1664 12 405]++rowSetup.map Op.code
def beforePair : Program := beforeRow++UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 14 39)++pairSetup.map Op.code
def beforeScatter : Program := beforePair++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11]++scatterSetup.map Op.code
def program : Program := beforeScatter++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]

lemma boot_length : boot.length=11:=rfl
lemma rowSetup_length : rowSetup.length=2:=rfl
lemma pairSetup_length : pairSetup.length=5:=rfl
lemma tick_length : tick.length=1:=rfl
lemma scatterSetup_length : scatterSetup.length=4:=rfl
lemma beforeRow_length : beforeRow.length=14:=rfl
lemma beforePair_length : beforePair.length=44:=by simp [beforePair,beforeRow_length,UniformMatchingConjugateLoadMachine.rowProgram_length,pairSetup_length]
lemma beforeScatter_length : beforeScatter.length=409:=by
 simp [beforeScatter,beforePair_length,UniformZeroFreePairShearMachine.program_length,tick_length,scatterSetup_length]
lemma program_length : program.length=422:=by
 simp [program,beforeScatter_length,UniformScalarScatterMachine.program_length]

lemma row_code : CodeAt UniformMatchingConjugateLoadMachine.rowProgram program 14 39:=by
 let rest:=pairSetup.map Op.code++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11]++scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]
 have eq:program=beforeRow++UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 14 39)++rest:=by
  simp [program,beforeScatter,beforePair,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeRow rest _ 14 39 beforeRow_length
lemma pair_code : CodeAt UniformZeroFreePairShearMachine.program program 44 403:=by
 let rest:=tick.map Op.code++[.jump 11]++scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]
 have eq:program=beforePair++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++rest:=by
  simp [program,beforeScatter,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforePair rest _ 44 403 beforePair_length
lemma scatter_code : CodeAt UniformScalarScatterMachine.program program 409 421:=
 UniformChunkRowTableMachine.segment_code beforeScatter [.halt] _ 409 421 beforeScatter_length

lemma boot_code : BlockAt boot program 0:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (boot.map Op.code)
  ([.branchLT 1660 1664 12 405]++rowSetup.map Op.code++UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 14 39)++pairSetup.map Op.code++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11]++scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) i (by simpa using hi)
 simpa only [program,beforeScatter,beforePair,beforeRow,List.append_assoc,List.length_nil,Nat.zero_add,List.nil_append,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma branch_at : program[11]?=some (.branchLT 1660 1664 12 405):=rfl
lemma jump_at : program[404]?=some (.jump 11):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment beforePair
  (UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11])
  (scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) 360 (by simp [UniformZeroFreePairShearMachine.program_length,tick_length])
 have tail:(UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11])[360]?=some (.jump 11):=by
  rw [List.append_assoc,List.getElem?_append_right (by simp [UniformZeroFreePairShearMachine.program_length])]
  simp [UniformZeroFreePairShearMachine.program_length,tick,Op.code]
 rw [tail] at h
 simpa only [program,beforeScatter,List.append_assoc,beforePair_length] using h
lemma halt_at : program[421]?=some .halt:=by
 rw [program,List.getElem?_append_right (by simp [beforeScatter_length,UniformScalarScatterMachine.program_length])]
 simp [beforeScatter_length,UniformScalarScatterMachine.program_length]

structure Header (c:Config) (s:State) : Prop where
 length:s.natReg 1640=c.length
 packed:s.natReg 1641=c.packed
 destination:s.natReg 1642=c.destination
 inverse:s.natReg 1643=c.inverse
 rows:s.natReg 1644=c.rows
 positive:s.natReg 1645=c.positive
 negative:s.natReg 1646=c.negative
 constants:s.natReg 1647=c.constants
 conjugates:s.natReg 1648=c.conjugates
 mu:s.natReg 1649=c.mu
 conjugateMu:s.natReg 1650=c.conjugateMu

structure Layout (c:Config) (M R B:ℕ) : Prop where
 coefficient : UniformMatchingConjugateLoadMachine.Layout R c.positive c.negative c.constants c.conjugates c.mu c.conjugateMu B
 capacity:2*M ≤ c.length
 packedFresh:c.conjugateMu<c.packed
 destinationFresh:c.conjugateMu<c.destination
 disjoint:UniformScalarScatterMachine.Disjoint c.packed c.destination c.length
 packedBound:c.packed+c.length ≤ B
 destinationBound:c.destination+c.length ≤ B
 inverseBound:c.inverse+c.length ≤ B
 rowsBound:c.rows+3*M ≤ B
 code:422 ≤ B

/-- Data carries arbitrary conservative flags. This is an actual presence
contract, not an action/transform certificate. -/
def Packed (c:Config) (v:ℕ → Scalar) (s:State) : Prop:=
 ∀j,j<c.length  →  s.scalarHeap (c.packed+j)=some (v j)

structure Cursor (c:Config) (M i:ℕ) (s:State) : Prop where
 header:Header c s
 pc:s.pc=11
 index:s.natReg 1660=i
 one:s.natReg 1661=1
 two:s.natReg 1662=2
 zero:s.natReg 1663=0
 count:s.natReg 1664=M
 positive:s.natReg 2100=c.positive
 negative:s.natReg 2101=c.negative
 constants:s.natReg 2102=c.constants
 conjugates:s.natReg 2103=c.conjugates
 mu:s.natReg 2106=c.mu
 conjugateMu:s.natReg 2107=c.conjugateMu

lemma boot_cursor (c:Config) (M:ℕ) (s:State) (h:Header c s)
 (count:s.natReg 894=M) (pc:s.pc=0) : Cursor c M 0 (applyBlock boot s):=by
 constructor
 · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.length,h.packed,h.destination,h.inverse,h.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu]
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,pc,count,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu]

lemma boot_bounded (n B M:ℕ) (x:Fin n → ℂ) (c:Config) (s:State) (h:Header c s)
 (count:s.natReg 894=M) (pc:s.pc=0) (hs:WordBound B s) (code:422 ≤ B) :
 BoundedRuns program n x B s 11 (applyBlock boot s):=by
 apply block_runs boot program 0 n B x s boot_code pc hs (by change 0+11 ≤ B;omega)
 · simp [boot,readable,Op.readable]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,count,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu]
   have b0:=hs.2.1 894
   have b1:=hs.2.1 1645;have b2:=hs.2.1 1646;have b3:=hs.2.1 1647;have b4:=hs.2.1 1648;have b5:=hs.2.1 1649;have b6:=hs.2.1 1650
   simp only [count,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu] at b0 b1 b2 b3 b4 b5 b6
   omega

lemma rowSetup_code : BlockAt rowSetup program 12 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 1660 1664 12 405]) (rowSetup.map Op.code)
  (UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 14 39)++pairSetup.map Op.code++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11]++scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) i (by simpa using hi)
 simpa only [program,beforeScatter,beforePair,beforeRow,List.append_assoc,List.length_append,List.length_map,boot_length,List.length_cons,List.length_nil,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma pairSetup_code : BlockAt pairSetup program 39 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeRow++UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 14 39)) (pairSetup.map Op.code)
  (UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11]++scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) i (by simpa using hi)
 simpa only [program,beforeScatter,beforePair,List.append_assoc,List.length_append,List.length_map,beforeRow_length,UniformMatchingConjugateLoadMachine.rowProgram_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma tick_code : BlockAt tick program 403 := by
 intro i hi;change i<1 at hi
 have iz:i=0:=by omega
 subst i
 have h:=UniformAllAxisSeedPreparation.lookup_segment beforePair
  (UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11])
  (scatterSetup.map Op.code++UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) 359 (by simp [UniformZeroFreePairShearMachine.program_length,tick_length])
 have tail:(UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11])[359]?=some (.natBinary .add 1660 1660 1661):=by
  rw [List.append_assoc,List.getElem?_append_right (by simp [UniformZeroFreePairShearMachine.program_length])]
  simp [UniformZeroFreePairShearMachine.program_length,tick,Op.code]
 rw [tail] at h
 simpa only [program,beforeScatter,List.append_assoc,beforePair_length,tick,Op.code,List.getElem_cons_zero,Nat.reduceAdd] using h
lemma scatterSetup_code : BlockAt scatterSetup program 405 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforePair++UniformZeroFreePairShearMachine.program.map (relocate 44 403)++tick.map Op.code++[.jump 11])
  (scatterSetup.map Op.code) (UniformScalarScatterMachine.program.map (relocate 409 421)++[.halt]) i (by simpa using hi)
 simpa only [program,beforeScatter,List.append_assoc,List.length_append,List.length_map,beforePair_length,UniformZeroFreePairShearMachine.program_length,tick_length,List.length_cons,List.length_nil,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h

/-- The physical footprint, including coefficient temporaries, both data banks
and every register touched by the literal helper code. -/
def NatStable (q:ℕ) : Prop := 3 ≤ q ∧ (q<1506∨1517 ≤ q) ∧
 (q<1620∨1625 ≤ q) ∧ (q<1660∨1665 ≤ q) ∧
 (q<2100∨2108 ≤ q) ∧ (q<2110∨2113 ≤ q) ∧ (q<2140∨2142 ≤ q)
def ScalarStable (q:ℕ) : Prop := 8 ≤ q ∧ q≠70 ∧ q≠71 ∧ q≠72 ∧ q≠90 ∧ (q<100∨110 ≤ q)
def HeapStable (c:Config) (q:ℕ) : Prop := q≠c.mu ∧ q≠c.conjugateMu ∧
 (q<c.packed∨c.packed+c.length ≤ q) ∧ (q<c.destination∨c.destination+c.length ≤ q)
structure Frame (c:Config) (s t:State) : Prop where
 natHeap:t.natHeap=s.natHeap
 outputs:t.outputs=s.outputs
 rootOrders:t.rootOrders=s.rootOrders
 natReg:∀q,NatStable q → t.natReg q=s.natReg q
 scalarReg:∀q,ScalarStable q → t.scalarReg q=s.scalarReg q
 scalarHeap:∀q,HeapStable c q → t.scalarHeap q=s.scalarHeap q
lemma Frame.refl (c:Config) (s:State) : Frame c s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {c:Config} {s t u:State} (a:Frame c s t) (b:Frame c t u) : Frame c s u :=
 ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.rootOrders.trans a.rootOrders,
 fun q h=>(b.natReg q h).trans (a.natReg q h),fun q h=>(b.scalarReg q h).trans (a.scalarReg q h),
 fun q h=>(b.scalarHeap q h).trans (a.scalarHeap q h)⟩
lemma Frame.from_setPC {c:Config} {s t:State} {p:ℕ} (h:Frame c (setPC s p) t) : Frame c s t :=
 ⟨h.natHeap,h.outputs,h.rootOrders,h.natReg,h.scalarReg,h.scalarHeap⟩
lemma Frame.setPC {c:Config} {s t:State} (h:Frame c s t) (p:ℕ) : Frame c s (setPC t p) := ⟨h.natHeap,h.outputs,h.rootOrders,h.natReg,h.scalarReg,h.scalarHeap⟩
lemma block_frame (c:Config) (s:State) :
 Frame c s (applyBlock boot s) ∧ Frame c s (applyBlock rowSetup s) ∧
 Frame c s (applyBlock pairSetup s) ∧ Frame c s (applyBlock tick s) ∧
 Frame c s (applyBlock scatterSetup s) := by
 repeat' apply And.intro
 all_goals refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 all_goals intro q h;rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
 all_goals simp (disch:=omega) [boot,rowSetup,pairSetup,tick,scatterSetup,applyBlock,Op.apply,writeNat,next]
lemma loader_frame {c:Config} {s t:State}
 (h:UniformMatchingConjugateLoadMachine.RowFrame s t)
 (heap:∀q,q≠c.mu → q≠c.conjugateMu → t.scalarHeap q=s.scalarHeap q) : Frame c s t :=
 ⟨h.1,h.2.1,h.2.2.1,fun q hq=>h.2.2.2.1 q (by rcases hq with ⟨_,_,_,_,_,h5,_⟩;omega)
 (by rcases hq with ⟨_,_,_,_,_,h5,_⟩;omega) (by rcases hq with ⟨_,_,_,_,_,h5,_⟩;omega)
 (by rcases hq with ⟨_,_,_,_,_,h5,_⟩;omega),
 fun q hq=>h.2.2.2.2 q hq.2.1 hq.2.2.1 hq.2.2.2.1,fun q hq=>heap q hq.1 hq.2.1⟩
lemma pair_frame {c:Config} {i:ℕ} {s t:State}
 (h:UniformZeroFreePairShearMachine.Frame (c.packed+2*i) (c.packed+2*i+1) s t)
 (cap:2*i+1<c.length) : Frame c s t := by
 refine ⟨h.natHeap,h.outputs,h.roots,?_,?_,?_⟩
 · intro q hq;exact h.natReg q hq.1 (by rcases hq with ⟨_,_,h2,_,_,_,_⟩;omega)
 · intro q hq;exact h.scalarReg q hq.1 hq.2.2.2.2.2
 · intro q hq;apply h.outside q <;> rcases hq with ⟨_,_,h3,_⟩ <;> omega
lemma scatter_frame {c:Config} {s t:State} (h:UniformScalarScatterMachine.Frame s t)
 (heap:UniformScalarScatterMachine.Outside c.destination c.length s.scalarHeap t) : Frame c s t := by
 refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,?_⟩
 · intro q hq;exact h.2.2.2.2 q (by rcases hq with ⟨_,h1,_,_,_,_,_⟩;omega)
 · intro q hq;exact h.2.2.2.1 q hq.2.2.2.2.1
 · intro q hq;exact heap q hq.2.2.2

/-- Exact conservative-tagged pair update. The untouched right value still
receives the OR flag, including a zero coefficient and cancellation. -/
def pairUpdate (i:ℕ) (mu:ℂ) (v:ℕ → Scalar) (j:ℕ) : Scalar :=
 if j=2*i then ⟨(v (2*i)).value+mu*(v (2*i+1)).value,(v (2*i)).dependent||(v (2*i+1)).dependent⟩
 else if j=2*i+1 then ⟨(v (2*i+1)).value,(v (2*i)).dependent||(v (2*i+1)).dependent⟩ else v j

def matchingAction {R:ℕ} (K:ℕ) (bank:Fin R → ℂ) (labels:ℕ → Coefficient R)
 (i:ℕ) : ℕ → (ℕ → Scalar) → (ℕ → Scalar)
 | 0,v => v
 | fuel+1,v => matchingAction K bank labels (i+1) fuel
  (pairUpdate i (UniformMatchingConjugateLoadMachine.value K bank (labels i)) v)

def matchingCost {R:ℕ} (labels:ℕ → Coefficient R) (i:ℕ) : ℕ → ℕ
 | 0 => 0
 | fuel+1 => 376+UniformMatchingConjugateLoadMachine.runtime (labels i)+matchingCost labels (i+1) fuel
lemma matchingCost_bound {R:ℕ} (labels:ℕ → Coefficient R) (i fuel:ℕ) : matchingCost labels i fuel ≤ 388*fuel := by
 induction fuel generalizing i with
 | zero => simp [matchingCost]
 | succ fuel ih =>
  have b:UniformMatchingConjugateLoadMachine.runtime (labels i) ≤ 12:=by cases labels i <;> simp [UniformMatchingConjugateLoadMachine.runtime]
  simp only [matchingCost];have h:=ih (i+1);omega

def cursorRegisters : List ℕ := [1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,
 1660,1661,1662,1663,1664,2100,2101,2102,2103,2106,2107]
def Registers (s t:State) : Prop := ∀q,q∈cursorRegisters → t.natReg q=s.natReg q
lemma Registers.trans {s t u:State} (a:Registers s t) (b:Registers t u) : Registers s u :=
 fun q h=>(b q h).trans (a q h)
lemma Cursor.transport {c:Config} {M i:ℕ} {s t:State} (h:Cursor c M i s)
 (eq:Registers s t) : Cursor c M i (setPC t 11) := by
 refine ⟨?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor
   all_goals first | exact (eq _ (by decide)).trans h.header.length
                   | exact (eq _ (by decide)).trans h.header.packed
                   | exact (eq _ (by decide)).trans h.header.destination
                   | exact (eq _ (by decide)).trans h.header.inverse
                   | exact (eq _ (by decide)).trans h.header.rows
                   | exact (eq _ (by decide)).trans h.header.positive
                   | exact (eq _ (by decide)).trans h.header.negative
                   | exact (eq _ (by decide)).trans h.header.constants
                   | exact (eq _ (by decide)).trans h.header.conjugates
                   | exact (eq _ (by decide)).trans h.header.mu
                   | exact (eq _ (by decide)).trans h.header.conjugateMu
 all_goals first | exact (eq _ (by decide)).trans h.index
                 | exact (eq _ (by decide)).trans h.one
                 | exact (eq _ (by decide)).trans h.two
                 | exact (eq _ (by decide)).trans h.zero
                 | exact (eq _ (by decide)).trans h.count
                 | exact (eq _ (by decide)).trans h.positive
                 | exact (eq _ (by decide)).trans h.negative
                 | exact (eq _ (by decide)).trans h.constants
                 | exact (eq _ (by decide)).trans h.conjugates
                 | exact (eq _ (by decide)).trans h.mu
                 | exact (eq _ (by decide)).trans h.conjugateMu
lemma setup_registers (s:State) : Registers s (applyBlock rowSetup s) ∧ Registers s (applyBlock pairSetup s) := by
 constructor
 all_goals intro q h;simp only [cursorRegisters,List.mem_cons,List.not_mem_nil,or_false] at h
 all_goals simp (disch:=omega) [rowSetup,pairSetup,applyBlock,Op.apply,writeNat,next]
lemma loader_registers {s t:State} (h:UniformMatchingConjugateLoadMachine.RowFrame s t) : Registers s t := by
 intro q hq;simp only [cursorRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq
 exact h.2.2.2.1 q (by omega) (by omega) (by omega) (by omega)
lemma pair_registers {left right:ℕ} {s t:State} (h:UniformZeroFreePairShearMachine.Frame left right s t) : Registers s t := by
 intro q hq;simp only [cursorRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq
 exact h.natReg q (by omega) (by omega)

lemma Layout.below {c:Config} {M R B:ℕ} (l:Layout c M R B) :
 6 ≤ c.mu ∧ c.mu<c.conjugateMu ∧ 8 ≤ c.packed ∧ 8 ≤ c.destination := by
 have a:=l.coefficient.constantsBelow;have b:=l.coefficient.conjugatesBelow
 have d:=l.coefficient.destinations;have e:=l.packedFresh;have f:=l.destinationFresh
 omega
lemma Frame.sources {c:Config} {M R B K:ℕ} {bank:Fin R → ℂ} {s t:State}
 (l:Layout c M R B) (h:Frame c s t)
 (src:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s) :
 UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank t := by
 have a:=l.coefficient.positiveBelow;have b:=l.coefficient.negativeBelow
 have d:=l.coefficient.constantsBelow;have e:=l.coefficient.conjugatesBelow
 have f:=l.coefficient.destinations;have g:=l.packedFresh;have k:=l.destinationFresh
 constructor
 · intro i;rw [h.scalarHeap _ (by have:=i.isLt;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact src.positive i
 · intro i;rw [h.scalarHeap _ (by have:=i.isLt;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact src.negative i
 · intro i;rw [h.scalarHeap _ (by have:=i.isLt;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact src.conjugate i
 · intro i hi;rw [h.scalarHeap _ (by constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact src.constants i hi
lemma Frame.constants {c:Config} {M R B:ℕ} {s t:State} (l:Layout c M R B)
 (h:Frame c s t) (hc:UniformHadamardPairMachine.Constants s) :
 UniformHadamardPairMachine.Constants t := by
 have a:=l.below
 rcases hc with ⟨h1,h2,h3,h4,h5⟩
 refine ⟨?_,?_,?_,?_,?_⟩
 all_goals first | rw [h.scalarHeap 1 (by rcases a with ⟨_,_,_,_⟩;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact h1
                 | rw [h.scalarHeap 2 (by rcases a with ⟨_,_,_,_⟩;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact h2
                 | rw [h.scalarHeap 3 (by rcases a with ⟨_,_,_,_⟩;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact h3
                 | rw [h.scalarHeap 4 (by rcases a with ⟨_,_,_,_⟩;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact h4
                 | rw [h.scalarHeap 5 (by rcases a with ⟨_,_,_,_⟩;constructor;omega;constructor;omega;constructor <;> left <;> omega)];exact h5

lemma rowSetup_args {c:Config} {M i:ℕ} {s:State} (h:Cursor c M i s) :
 UniformMatchingConjugateLoadMachine.RowArgs c.positive c.negative c.constants c.conjugates c.mu c.conjugateMu c.rows i (applyBlock rowSetup s) := by
 constructor <;> simp [rowSetup,applyBlock,Op.apply,writeNat,next,h.index,h.zero,h.header.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu]
lemma pairSetup_args {c:Config} {M i:ℕ} {s:State} (h:Cursor c M i (setPC s 11)) :
 UniformZeroFreePairShearMachine.Args (c.packed+2*i) (c.packed+2*i+1) c.mu c.conjugateMu (applyBlock pairSetup s) := by
 constructor <;> simp [pairSetup,applyBlock,Op.apply,writeNat,next,
 show s.natReg 1660=i from h.index,show s.natReg 1661=1 from h.one,
 show s.natReg 1662=2 from h.two,show s.natReg 1663=0 from h.zero,
 show s.natReg 1641=c.packed from h.header.packed,
 show s.natReg 1649=c.mu from h.header.mu,show s.natReg 1650=c.conjugateMu from h.header.conjugateMu,Nat.mul_comm i 2]

/-- One generated row is decoded, its two nonzero shear blocks are prepared
internally, and both physical data cells are updated by six C calls. -/
theorem row_execution {R K B n:ℕ} (x:Fin n → ℂ) (c:Config) (rows:List Row)
 (l:Layout c rows.length R B) (bank:Fin R → ℂ) (i:Fin rows.length) (coef:Coefficient R)
 (v:ℕ → Scalar) (s:State) (cursor:Cursor c rows.length i.val s)
 (src:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s)
 (table:Table c.rows rows s) (ref:(rows[i.val]'i.isLt).coefficient=UniformMatchingConjugateLoadMachine.address c.positive c.negative c.constants coef)
 (data:Packed c v s) (constants:UniformHadamardPairMachine.Constants s) (hs:WordBound B s) : ∃u,
 BoundedRuns program n x B s (374+UniformMatchingConjugateLoadMachine.runtime coef) u ∧
 u.pc=403 ∧ Cursor c rows.length i.val (setPC u 11) ∧
 Packed c (pairUpdate i.val (UniformMatchingConjugateLoadMachine.value K bank coef) v) u ∧
 Frame c s u := by
 have code:=l.code
 have cap:2*i.val+1<c.length:=by have:=i.isLt;have:=l.capacity;omega
 let a:=setPC s 12
 have ab:=changePC_bound B s 12 hs (by omega)
 have branch:BoundedRuns program n x B s 1 a:=.next hs
  (by simp [step,cursor.pc,branch_at,cursor.index,cursor.count,i.isLt,a,setPC]) (.refl ab)
 have head:=block_runs rowSetup program 12 n B x a rowSetup_code rfl ab
  (by rw [rowSetup_length];omega) (by simp [rowSetup,readable,Op.readable]) (by
   simp [rowSetup,peak,Op.peak,Op.apply,writeNat,next,a,setPC,cursor.zero,cursor.index,cursor.header.rows]
   have rowb:=hs.2.1 1644;rw [cursor.header.rows] at rowb;have ib:=i.isLt;have countb:=hs.2.1 1664;rw [cursor.count] at countb;omega)
 let b:=applyBlock rowSetup a
 have bp:b.pc=14:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 let e:=setPC b 0
 have rh:=rowSetup_args cursor
 have ra:UniformMatchingConjugateLoadMachine.RowArgs c.positive c.negative c.constants c.conjugates c.mu c.conjugateMu c.rows i.val e:=
  ⟨rh.positive,rh.negative,rh.constants,rh.conjugates,rh.original,rh.conjugate,rh.rows,rh.index⟩
 have es:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank e:=
  ⟨src.positive,src.negative,src.conjugate,src.constants⟩
 obtain ⟨z,zrun,zmu,zbar,zheap,znh,zout,zroot,zpc,zframe⟩:=UniformMatchingConjugateLoadMachine.execution_from_row rows i coef
  ra l.coefficient es table ref l.rowsBound (by omega) x rfl
  (changePC_bound B b 0 head.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed row_code
  (by rw [UniformMatchingConjugateLoadMachine.rowProgram_length];omega) (by omega) zrun
 have ep:placed 14 e=b:=by change {b with pc:=14}=b;rw [←bp]
 rw [ep] at moved
 let d:=setPC z 39
 have regs:Registers s d:=(setup_registers a).1.trans (loader_registers zframe)
 have dc:=cursor.transport regs
 have safe:readable pairSetup d ∧ peak pairSetup d ≤ B:=by
  constructor
  · simp [pairSetup,readable,Op.readable]
  · simp [pairSetup,peak,Op.peak,Op.apply,writeNat,next,
    show d.natReg 1660=i.val from dc.index,show d.natReg 1661=1 from dc.one,
    show d.natReg 1662=2 from dc.two,show d.natReg 1663=0 from dc.zero,
    show d.natReg 1641=c.packed from dc.header.packed,
    show d.natReg 1649=c.mu from dc.header.mu,show d.natReg 1650=c.conjugateMu from dc.header.conjugateMu,Nat.mul_comm i.val 2]
    have b0:=l.packedBound;have b1:=l.coefficient.bound;have b2:=l.coefficient.destinations;omega
 have setup:=block_runs pairSetup program 39 n B x d pairSetup_code rfl moved.final_bound
  (by rw [pairSetup_length];omega) safe.1 safe.2
 let f:=applyBlock pairSetup d
 have fp:f.pc=44:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 let e2:=setPC f 0
 have hp:Packed c v f:=by
  intro j hj
  rw [show f.scalarHeap=z.scalarHeap from rfl,zheap _ (by have:=l.coefficient.destinations;have:=l.packedFresh;omega) (by have:=l.packedFresh;omega)]
  exact data j hj
 have pa:=pairSetup_args dc
 have ea:UniformZeroFreePairShearMachine.Args (c.packed+2*i.val) (c.packed+2*i.val+1) c.mu c.conjugateMu e2:=
  ⟨pa.leftAddress,pa.rightAddress,pa.coefficient,pa.conjugateCoefficient⟩
 have lf:(c.packed+2*i.val)≠(c.packed+2*i.val+1):=by omega
 have preFrame:Frame c s f:=Frame.from_setPC (((block_frame c a).2.1.trans (loader_frame zframe zheap)).trans (Frame.from_setPC (block_frame c d).2.2.1))
 obtain ⟨out,prun,result⟩:=UniformZeroFreePairShearMachine.execution_result n B x
  (UniformMatchingConjugateLoadMachine.value K bank coef) (c.packed+2*i.val) (c.packed+2*i.val+1) c.mu c.conjugateMu e2
  (v (2*i.val)) (v (2*i.val+1)) ea ⟨zmu,zbar⟩
  ((preFrame.setPC 0).constants l constants) (by have:=l.below;omega) (by have:=l.below;omega) lf
  (hp _ (by omega)) (by simpa only [e2,setPC,Nat.add_assoc] using hp (2*i.val+1) cap)
  rfl (changePC_bound B f 0 setup.final_bound (by omega)) (by omega)
 have pmove:=UniformBoundedAssembly.boundedExecution_placed pair_code
  (by rw [UniformZeroFreePairShearMachine.program_length];omega) (by omega) prun
 have e2p:placed 44 e2=f:=by change {f with pc:=44}=f;rw [←fp]
 rw [e2p] at pmove
 let u:=setPC out 403
 have pr:Registers f u:=by intro q h;exact pair_registers result.frame q h
 refine ⟨u,?_,rfl,cursor.transport (regs.trans ((setup_registers d).2.trans pr)),?_,(preFrame.trans (Frame.from_setPC (pair_frame result.frame cap))).setPC 403⟩
 · have all:BoundedRuns program n x B s (1+(2+((UniformMatchingConjugateLoadMachine.runtime coef+7)+(5+359)))) u:=
    branch.trans (head.trans (moved.trans (setup.trans pmove)))
   have count:1+(2+((UniformMatchingConjugateLoadMachine.runtime coef+7)+(5+359)))=374+UniformMatchingConjugateLoadMachine.runtime coef:=by omega
   rw [count] at all;exact all
 · intro j hj
   change out.scalarHeap (c.packed+j)=some (pairUpdate i.val (UniformMatchingConjugateLoadMachine.value K bank coef) v j)
   by_cases h0:j=2*i.val
   · subst j;simpa [pairUpdate] using result.leftValue
   · by_cases h1:j=2*i.val+1
     · subst j;simpa [pairUpdate,Nat.add_assoc] using result.rightValue
     · rw [result.frame.outside _ (by omega) (by omega)]
       simpa [e2,setPC,pairUpdate,h0,h1] using hp j hj

lemma tick_cursor {c:Config} {M i:ℕ} {s:State} (h:Cursor c M i (setPC s 11)) :
 Cursor c M (i+1) (setPC (applyBlock tick s) 11) := by
 refine ⟨?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor
   all_goals first | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.length
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.packed
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.destination
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.inverse
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.rows
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.positive
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.negative
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.constants
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.conjugates
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.mu
                   | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.header.conjugateMu
 · have h0:s.natReg 1660=i:=h.index;have h1:s.natReg 1661=1:=h.one
   simp [tick,applyBlock,Op.apply,writeNat,next,setPC,h0,h1]
 all_goals first | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.one
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.two
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.zero
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.count
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.positive
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.negative
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.constants
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.conjugates
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.mu
                 | simpa [tick,applyBlock,Op.apply,writeNat,next,setPC] using h.conjugateMu

/-- Every row, including a zero coefficient, traverses the actual loader and
six-C program. The count was copied from physical Nat894 at startup. -/
theorem loop {R K B n:ℕ} (x:Fin n → ℂ) (c:Config) (rows:List Row)
 (l:Layout c rows.length R B) (bank:Fin R → ℂ) (labels:ℕ → Coefficient R)
 (refs:∀i (hi:i<rows.length),(rows[i]'hi).coefficient=UniformMatchingConjugateLoadMachine.address c.positive c.negative c.constants (labels i))
 (i fuel:ℕ) (rest:i+fuel=rows.length) (v:ℕ → Scalar) (s:State)
 (cursor:Cursor c rows.length i s)
 (src:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s)
 (table:Table c.rows rows s) (data:Packed c v s)
 (constants:UniformHadamardPairMachine.Constants s) (hs:WordBound B s) : ∃u,
 BoundedRuns program n x B s (matchingCost labels i fuel) u ∧
 Cursor c rows.length rows.length u ∧ Packed c (matchingAction K bank labels i fuel v) u ∧ Frame c s u := by
 induction fuel generalizing i v s with
 | zero =>
  have eq:i=rows.length:=by omega
  subst i
  exact ⟨s,.refl hs,cursor,data,Frame.refl c s⟩
 | succ fuel ih =>
  have hi:i<rows.length:=by omega
  obtain ⟨z,run,zpc,zc,zd,zf⟩:=row_execution x c rows l bank ⟨i,hi⟩ (labels i) v s cursor src table (refs i hi) data constants hs
  have tr:=block_runs tick program 403 n B x z tick_code zpc run.final_bound
   (by rw [tick_length];have:=l.code;omega) (by simp [tick,readable,Op.readable]) (by
    simp [tick,peak,Op.peak,show z.natReg 1660=i from zc.index,show z.natReg 1661=1 from zc.one]
    have:=hs.2.1 1664;rw [cursor.count] at this;omega)
  let w:=applyBlock tick z
  have wp:w.pc=404:=by rw [UniformTensorMonomialMachine.applyBlock_pc,zpc,tick_length]
  let t:=setPC w 11
  have tb:=changePC_bound B w 11 tr.final_bound (by have:=l.code;omega)
  have jump:BoundedRuns program n x B w 1 t:=.next tr.final_bound
   (by simp [step,wp,jump_at,t,setPC]) (.refl tb)
  have tf:Frame c s t:=(zf.trans (block_frame c z).2.2.2.1).setPC 11
  have tc:=tick_cursor zc
  have ts:=tf.sources l src
  have tt:Table c.rows rows t:=by
   unfold UniformCrossShearTableMachine.Table
   rw [tf.natHeap];exact table
  obtain ⟨u,ur,uc,ud,uf⟩:=ih (i+1) (by omega)
   (pairUpdate i (UniformMatchingConjugateLoadMachine.value K bank (labels i)) v)
   t tc ts tt zd (tf.constants l constants) tb
  refine ⟨u,?_,uc,ud,tf.trans uf⟩
  convert run.trans (tr.trans (jump.trans ur)) using 1
  simp only [matchingCost,tick_length]
  omega

lemma scatterSetup_spec {c:Config} {M:ℕ} {s:State} (h:Cursor c M M s) :
 (applyBlock scatterSetup s).natReg 1506=c.length ∧
 (applyBlock scatterSetup s).natReg 1507=c.packed ∧
 (applyBlock scatterSetup s).natReg 1508=c.destination ∧
 (applyBlock scatterSetup s).natReg 1509=c.inverse := by
 simp [scatterSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.header.length,h.header.packed,h.header.destination,h.header.inverse]
lemma scatterSetup_safe {c:Config} {M B:ℕ} {s:State} (h:Cursor c M M s) (bound:WordBound B s) :
 readable scatterSetup s ∧ peak scatterSetup s ≤ B := by
 simp [scatterSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.zero]
 exact ⟨bound.2.1 1640,bound.2.1 1641,bound.2.1 1642,bound.2.1 1643⟩

/-- Exact physical matching result; the permutation bank is the packing
inverse, independently from the coefficient table and actual Nat894 count. -/
structure Result {R:ℕ} (c:Config) (rows:List Row) (K:ℕ) (bank:Fin R → ℂ)
 (labels:ℕ → Coefficient R) (phi:Fin c.length≃Fin c.length) (v:ℕ → Scalar) (s u:State) : Prop where
 pc:u.pc=421
 packed:Packed c (matchingAction K bank labels 0 rows.length v) u
 destination:∀j:Fin c.length,u.scalarHeap (c.destination+j.val)=
  some (matchingAction K bank labels 0 rows.length v (phi.symm j).val)
 coefficients:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank u
 constants:UniformHadamardPairMachine.Constants u
 frame:Frame c s u

/-- Continuous literal422: charge all row-pointer reads, conjugate loads,
internal scale preparation, six-C pair updates, and inverse scatter. Neither
helper headers nor C-transformed data are supplied. -/
theorem execution {R K B n:ℕ} (x:Fin n → ℂ) (c:Config) (rows:List Row)
 (l:Layout c rows.length R B) (bank:Fin R → ℂ) (labels:ℕ → Coefficient R)
 (refs:∀i (hi:i<rows.length),(rows[i]'hi).coefficient=UniformMatchingConjugateLoadMachine.address c.positive c.negative c.constants (labels i))
 (phi:Fin c.length≃Fin c.length) (v:ℕ → Scalar) (s:State) (args:Header c s)
 (count:s.natReg 894=rows.length)
 (src:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s)
 (table:Table c.rows rows s)
 (inverse:UniformGlobalNatPreparation.PermutationBank c.length c.inverse s.natHeap phi)
 (data:Packed c v s) (constants:UniformHadamardPairMachine.Constants s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (matchingCost labels 0 rows.length+9*c.length+21) u ∧
 Result c rows K bank labels phi v s u := by
 have code:=l.code
 have first:=boot_bounded n B rows.length x c s args count pc bound code
 let a:=applyBlock boot s
 have af:Frame c s a:=(block_frame c s).1
 have sa:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank a:=
  ⟨src.positive,src.negative,src.conjugate,src.constants⟩
 obtain ⟨z,run,zc,zd,zf⟩:=loop x c rows l bank labels refs 0 rows.length (by omega) v a
  (boot_cursor c rows.length s args count pc) sa table data (af.constants l constants) first.final_bound
 let b:=setPC z 405
 have bb:=changePC_bound B z 405 run.final_bound (by omega)
 have lastBranch:BoundedRuns program n x B z 1 b:=.next run.final_bound
  (by simp [step,zc.pc,branch_at,zc.index,zc.count,b,setPC]) (.refl bb)
 have bc:Cursor c rows.length rows.length (setPC b 11):=zc.transport (fun _ _=>rfl)
 have safe:=scatterSetup_safe bc (changePC_bound B b 11 bb (by omega))
 have setup:=block_runs scatterSetup program 405 n B x b scatterSetup_code rfl bb
  (by rw [scatterSetup_length];omega) safe.1 safe.2
 let d:=applyBlock scatterSetup b
 have dp:d.pc=409:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 let e:=setPC d 0
 have headers:=scatterSetup_spec bc
 have it:UniformGlobalNatPreparation.PermutationBank c.length c.inverse e.natHeap phi:=by
  rw [show e.natHeap=z.natHeap from rfl,zf.natHeap,af.natHeap];exact inverse
 have sd:UniformScalarScatterMachine.Source c.length c.packed e.scalarHeap:=by
  intro j;exact ⟨matchingAction K bank labels 0 rows.length v j.val,zd j.val j.isLt⟩
 obtain ⟨out,sr,destination,packed,outside,frame,op,_⟩:=UniformScalarScatterMachine.execution n x
  c.length c.packed c.destination c.inverse B phi e it sd l.disjoint l.packedBound l.destinationBound l.inverseBound
  (by omega) rfl headers.1 headers.2.1 headers.2.2.1 headers.2.2.2
  (changePC_bound B d 0 setup.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed scatter_code
  (by rw [UniformScalarScatterMachine.program_length];omega) (by omega) sr
 have ep:placed 409 e=d:=by change {d with pc:=409}=d;rw [←dp]
 rw [ep] at moved
 let u:=setPC out 421
 have stop:BoundedExecution program n x B u 1 u:=.halt moved.final_bound
  (by simp [step,u,setPC,halt_at])
 have sf:Frame c d u:=(Frame.from_setPC (scatter_frame frame outside)).setPC 421
 have allframe:Frame c s u:=af.trans (zf.trans ((Frame.from_setPC (block_frame c b).2.2.2.2).trans sf))
 refine ⟨u,?_,rfl,?_,?_,allframe.sources l src,allframe.constants l constants,allframe⟩
 · have all:=first.executes (run.executes (lastBranch.executes (setup.executes (moved.executes stop))))
   convert all using 1
   simp only [scatterSetup_length]
   omega
 · intro j hj
   rw [show u.scalarHeap=out.scalarHeap from rfl,packed ⟨j,hj⟩]
   exact zd j hj
 · intro j
   rw [show u.scalarHeap=out.scalarHeap from rfl,UniformScalarScatterMachine.scatter_coordinates destination j]
   exact zd _ (phi.symm j).isLt

lemma runtime_linear {R:ℕ} {c:Config} {rows:List Row} (labels:ℕ → Coefficient R)
 (capacity:2*rows.length ≤ c.length) :
 matchingCost labels 0 rows.length+9*c.length+21 ≤ 203*c.length+21 := by
 have:=matchingCost_bound labels 0 rows.length;omega
lemma Result.saved_headers {R K:ℕ} {c:Config} {rows:List Row} {bank:Fin R → ℂ}
 {labels:ℕ → Coefficient R} {phi:Fin c.length≃Fin c.length} {v:ℕ → Scalar} {s u:State}
 (h:Result c rows K bank labels phi v s u) (q:ℕ) (lo:100 ≤ q) (hi:q ≤ 106) :
 u.natReg q=s.natReg q := h.frame.natReg q (by unfold NatStable;omega)
lemma Result.count_retained {R K:ℕ} {c:Config} {rows:List Row} {bank:Fin R → ℂ}
 {labels:ℕ → Coefficient R} {phi:Fin c.length≃Fin c.length} {v:ℕ → Scalar} {s u:State}
 (h:Result c rows K bank labels phi v s u) : u.natReg 894=s.natReg 894 :=
 h.frame.natReg 894 (by unfold NatStable;omega)

/-- Each physical row executes both literal three-C words. This is a gate
count statement, distinct from the charged scalar/Nat instruction runtime. -/
def cCalls (M:ℕ) : ℕ := M*UniformZeroFreePairShearMachine.kernelCalls UniformZeroFreePairShearMachine.phases
lemma cCalls_eq (M:ℕ) : cCalls M=6*M := by rw [cCalls,UniformZeroFreePairShearMachine.six_kernel_calls];omega

lemma matchingAction_outside {R:ℕ} (K:ℕ) (bank:Fin R → ℂ) (labels:ℕ → Coefficient R)
 (start fuel j:ℕ) (v:ℕ → Scalar) (out:j<2*start ∨ 2*(start+fuel) ≤ j) :
 matchingAction K bank labels start fuel v j=v j := by
 induction fuel generalizing start v with
 | zero => rfl
 | succ fuel ih =>
  have next:j<2*(start+1) ∨ 2*(start+1+fuel) ≤ j:=by omega
  rw [matchingAction,ih (start+1) _ next]
  simp [pairUpdate,show j≠2*start by omega,show j≠2*start+1 by omega]

lemma matchingAction_pair {R:ℕ} (K:ℕ) (bank:Fin R → ℂ) (labels:ℕ → Coefficient R)
 (start fuel i : ℕ) (v : ℕ → Scalar) (lo : start  ≤  i) (hi : i < start + fuel) :
 matchingAction K bank labels start fuel v (2*i)=
  ⟨(v (2*i)).value+UniformMatchingConjugateLoadMachine.value K bank (labels i)*(v (2*i+1)).value,
   (v (2*i)).dependent||(v (2*i+1)).dependent⟩ ∧
 matchingAction K bank labels start fuel v (2*i+1)=
  ⟨(v (2*i+1)).value,(v (2*i)).dependent||(v (2*i+1)).dependent⟩ := by
 induction fuel generalizing start v with
 | zero => omega
 | succ fuel ih =>
  by_cases eq:i=start
  · subst i
    simp only [matchingAction]
    rw [matchingAction_outside K bank labels (start+1) fuel (2*start) _ (Or.inl (by omega)),
      matchingAction_outside K bank labels (start+1) fuel (2*start+1) _ (Or.inl (by omega))]
    simp [pairUpdate]
  · have hl:start+1 ≤ i:=by omega
    have hh : i < start+1+fuel := by omega
    have hyp:=ih (start+1) (pairUpdate start (UniformMatchingConjugateLoadMachine.value K bank (labels start)) v) hl hh
    simpa [matchingAction,pairUpdate,show 2*i≠2*start by omega,show 2*i≠2*start+1 by omega,
      show 2*i+1≠2*start by omega,show 2*i+1≠2*start+1 by omega] using hyp

lemma Result.pair_coordinates {R K:ℕ} {c:Config} {rows:List Row} {bank:Fin R → ℂ}
 {labels:ℕ → Coefficient R} {phi:Fin c.length≃Fin c.length} {v:ℕ → Scalar} {s u:State}
 (h:Result c rows K bank labels phi v s u) (cap:2*rows.length ≤ c.length) (i:Fin rows.length) :
 u.scalarHeap (c.destination+(phi ⟨2*i.val,by have:=i.isLt;omega⟩).val)=
  some ⟨(v (2*i.val)).value+UniformMatchingConjugateLoadMachine.value K bank (labels i.val)*(v (2*i.val+1)).value,
   (v (2*i.val)).dependent||(v (2*i.val+1)).dependent⟩ ∧
 u.scalarHeap (c.destination+(phi ⟨2*i.val+1,by have:=i.isLt;omega⟩).val)=
  some ⟨(v (2*i.val+1)).value,(v (2*i.val)).dependent||(v (2*i.val+1)).dependent⟩ := by
 have a:=h.destination (phi ⟨2*i.val,by have:=i.isLt;omega⟩)
 have b:=h.destination (phi ⟨2*i.val+1,by have:=i.isLt;omega⟩)
 simp only [phi.symm_apply_apply] at a b
 have numeric:=matchingAction_pair K bank labels 0 rows.length i.val v (by omega) (by have:=i.isLt;omega)
 exact ⟨a.trans (congrArg some numeric.1),b.trans (congrArg some numeric.2)⟩
lemma Result.tail {R K:ℕ} {c:Config} {rows:List Row} {bank:Fin R → ℂ}
 {labels:ℕ → Coefficient R} {phi:Fin c.length≃Fin c.length} {v:ℕ → Scalar} {s u:State}
 (h:Result c rows K bank labels phi v s u) (j:Fin c.length) (tail:2*rows.length ≤ j.val) :
 u.scalarHeap (c.destination+(phi j).val)=some (v j.val) ∧
 u.scalarHeap (c.packed+j.val)=some (v j.val) := by
 have eq:=matchingAction_outside K bank labels 0 rows.length j.val v (Or.inr (by omega))
 have a:=h.destination (phi j)
 simp only [phi.symm_apply_apply,eq] at a
 exact ⟨a,(h.packed j.val j.isLt).trans (congrArg some eq)⟩

/-- Labels are read mathematically from the actual selected logical rows.
Their physical addresses are printed unchanged by the row mapper. -/
def selectedLabels {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (i:ℕ) : Coefficient R :=
 if hi:i<(UniformChunkMatchingPreparation.indices p W).length then
  UniformMatchingConjugateLoadMachine.fromReference
   (W[(UniformColorLayerTableMachine.selectionIndex W.length p.color (UniformChunkMatchingPreparation.colors W) ⟨i,hi⟩).val]).coefficient
 else .constant 0
lemma mappedRows_length {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (loc:UniformInPlaceMachine.Locations R) :
 (UniformChunkMatchingPreparation.mappedRows p fit W loc).length=(UniformChunkMatchingPreparation.indices p W).length := by
 simp [UniformChunkMatchingPreparation.mappedRows,UniformChunkMatchingPreparation.selectedRows]
lemma mappedRows_reference {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ) (i:ℕ)
 (hi:i<(UniformChunkMatchingPreparation.mappedRows p fit W (UniformCrossShearTableMachine.locations R C T P)).length) :
 ((UniformChunkMatchingPreparation.mappedRows p fit W (UniformCrossShearTableMachine.locations R C T P))[i]'hi).coefficient=
 UniformMatchingConjugateLoadMachine.address C T P (selectedLabels p W i) := by
 have small:i<(UniformChunkMatchingPreparation.indices p W).length:=by simpa only [mappedRows_length] using hi
 let idx:=UniformColorLayerTableMachine.selectionIndex W.length p.color (UniformChunkMatchingPreparation.colors W) ⟨i,small⟩
 have idxBound:idx.val<W.length:=idx.isLt
 simp only [UniformChunkMatchingPreparation.mappedRows,UniformChunkMatchingPreparation.selectedRows,List.getElem_map,
  ]
 change (UniformChunkMatchingPreparation.rowFunction W (UniformCrossShearTableMachine.locations R C T P) idx.val).coefficient=_
 rw [UniformChunkMatchingPreparation.rowFunction,dite_eq_left idxBound]
 simp only [UniformCrossShearTableMachine.shiftedRow,selectedLabels,dite_eq_left small]
 exact UniformMatchingConjugateLoadMachine.reference_address C T P _

abbrev seedWord (n:ℕ) (j:Fin (UniformAllAxisSeedPreparation.axisCount n)) (seed:UniformSeedChunkPreparation.Config) :=
 UniformSeedChunkPackingPreparation.word n j seed
abbrev seedRows {n B:ℕ} {j:Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed:UniformSeedChunkPreparation.Config} (p:UniformSeedChunkPackingPreparation.Layout n j seed B) :=
 UniformChunkMatchingPreparation.mappedRows (seed.chunk n j) p.seed.chunk.capacity
  (seedWord n j seed) (UniformChunkMatchingPreparation.crossLocations (seed.chunk n j) seed.seed.negative)
abbrev seedLabels (n:ℕ) (j:Fin (UniformAllAxisSeedPreparation.axisCount n)) (seed:UniformSeedChunkPreparation.Config) :=
 selectedLabels (seed.chunk n j) (seedWord n j seed)

def packingConfig (L:UniformSectorPackingMachine.Layout) (D C T P V mu bar:ℕ) : Config :=
 ⟨L.total,L.destination,L.source,L.inverse,D,C,T,P,V,mu,bar⟩

lemma generated_count {n B:ℕ} (hn:0<n) {j:Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed:UniformSeedChunkPreparation.Config} {origin s:State}
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 {original:Fin p.packing.total → Scalar} (packed:UniformSeedChunkPackingPreparation.Packed p original origin s) :
 s.natReg 894=(seedRows p).length := by
 rw [packed.frame.2.2.1 894 (by omega),post.count]
 exact (mappedRows_length ..).symm

lemma generated_table {n B:ℕ} (hn:0<n) {j:Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed:UniformSeedChunkPreparation.Config} {origin s:State}
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 {original:Fin p.packing.total → Scalar} (packed:UniformSeedChunkPackingPreparation.Packed p original origin s) :
 Table seed.mapped (seedRows p) s := by
 let par:=seed.chunk n j
 have size:(seedWord n j seed).length ≤ 2*UniformCrossHeightPreparationMachine.gates par.height:=by
  simpa only [seedWord,UniformSeedChunkPackingPreparation.word,UniformChunkMatchingPreparation.crossWord,
   UniformCrossHeightPreparationMachine.cross_size par.height (UniformSeedHeightPreparation.widths seed.seed).1 (UniformSeedHeightPreparation.widths seed.seed).2] using
   UniformCrossHeightPreparationMachine.bucket_length
    (UniformToeplitzCrossDAG.crossDAG par.height.K par.height.a par.height.e (UniformSeedHeightPreparation.widths seed.seed).1 (UniformSeedHeightPreparation.widths seed.seed).2).program par.height.enabled par.depth
 have small:(seedRows p).length ≤ 2*UniformCrossHeightPreparationMachine.gates par.height:=by
  rw [mappedRows_length];exact (UniformChunkMatchingPreparation.selected_count par _).trans size
 have mappedBelow:seed.mapped+3*(seedRows p).length ≤ p.packing.suffix:=by
  have a:=p.seed.chunk.mappedFresh;have b:=p.seed.chunk.permutationFresh
  have d:=p.seed.chunk.widthsFresh;have e:=p.seed.chunk.markersFresh
  have f:=p.packing.rowsBelow
  change seed.mapped+6*UniformCrossHeightPreparationMachine.gates par.height ≤ seed.permutation at a
  change seed.permutation+par.radix ≤ seed.widths at b
  change seed.widths+par.radix ≤ seed.markers at d
  change seed.markers+par.radix ≤ seed.axis at e
  rw [p.axisRow] at f
  omega
 intro i hi
 have orig:=post.mapped i hi
 have same:∀q,q<seed.mapped+3*(seedRows p).length → s.natHeap q=origin.natHeap q:=by
  intro q hq
  exact packed.natOutside q (Or.inl (by omega)) (Or.inl (by have:=p.packing.suffixBelow;omega))
   (Or.inl (by have:=p.packing.suffixBelow;have:=p.packing.stackBelow;omega))
 rcases orig with ⟨h0,h1,h2⟩
 refine ⟨?_,?_,?_⟩
 · rw [same _ (by omega)];exact h0
 · rw [same _ (by omega)];exact h1
 · rw [same _ (by omega)];exact h2

/-- Actual produced matching count, mapped coefficient rows and generated
packing inverse discharge the three table/count entry contracts. Original
packed scalars and the real conjugate coefficient bank retain their physical
producer boundary. No table, transformed bank or helper header is invented. -/
theorem execution_from_generated_packing {n B:ℕ} (hn:0<n)
 {j:Fin (UniformAllAxisSeedPreparation.axisCount n)} {seed:UniformSeedChunkPreparation.Config}
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 {origin s:State} (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 (original:Fin p.packing.total → Scalar) (packed:UniformSeedChunkPackingPreparation.Packed p original origin s)
 (V mu bar:ℕ)
 (l:Layout (packingConfig p.packing seed.mapped seed.seed.C seed.seed.negative seed.seed.constants V mu bar)
  (seedRows p).length (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) B)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) → ℂ)
 (src:UniformMatchingConjugateLoadMachine.Sources seed.seed.exponent seed.seed.C seed.seed.negative seed.seed.constants V bank s)
 (x:Fin n → ℂ) (ops:UniformInitialPreparation.Operands n x s)
 (args:Header (packingConfig p.packing seed.mapped seed.seed.C seed.seed.negative seed.seed.constants V mu bar) s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (matchingCost (seedLabels n j seed) 0 (seedRows p).length+9*p.packing.total+21) u ∧
 Result (packingConfig p.packing seed.mapped seed.seed.C seed.seed.negative seed.seed.constants V mu bar)
  (seedRows p) seed.seed.exponent bank (seedLabels n j seed) (UniformSeedChunkPackingPreparation.unpacking p)
  (fun i=>if hi:i<p.packing.total then original (UniformSeedChunkPackingPreparation.unpacking p ⟨i,hi⟩) else Scalar.zero) s u := by
 apply execution x _ (seedRows p) l bank (seedLabels n j seed) _ (UniformSeedChunkPackingPreparation.unpacking p)
  _ s args (generated_count hn p post packed) src (generated_table hn p post packed) packed.inverse _
  (UniformHadamardPairMachine.constants_from_bank n s ops.constants) pc bound
 · intro i hi
   exact mappedRows_reference (seed.chunk n j) p.seed.chunk.capacity (seedWord n j seed) seed.seed.C seed.seed.negative seed.seed.constants i hi
 · intro i hi
   have hh:i<p.packing.total:=hi
   change s.scalarHeap (p.packing.destination+i)=some (if h:i<p.packing.total then original (UniformSeedChunkPackingPreparation.unpacking p ⟨i,h⟩) else Scalar.zero)
   rw [dite_eq_left hh]
   exact packed.values ⟨i,hh⟩

end
end ExactFourierCircuits.UniformPackedMatchingShearMachine
