import UniformGlobalCalendarSelectorLoop

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarUnionRows
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

/-- Read actual ordered pair positions and append genuine three-word matching
rows with coefficient1. No scalar or endpoint action is an input oracle. -/
def boot : List Op := [.literal 6744 0,.literal 6745 1,.literal 6746 2,
 .literal 6747 3,.literal 6748 0]
def pairBody : List Op := [.mul 6749 6748 6746,.add 6749 6740 6749,.getNat 6750 6749,
 .add 6749 6749 6745,.getNat 6751 6749,.add 6752 6743 6748,
 .mul 6752 6747 6752,.add 6752 6742 6752,.putNat 6752 6750,
 .add 6752 6752 6745,.putNat 6752 6751,.add 6752 6752 6745,
 .putNat 6752 6745,.add 6748 6748 6745]
def finish : List Op := [.add 6743 6743 6748]
def program : Program := boot.map Op.code++[.branchLT 6748 6741 6 21]++
 pairBody.map Op.code++[.jump 5]++finish.map Op.code++[.halt]
lemma program_length : program.length = 23 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma pairBody_code : BlockAt pairBody program 6 := by intro i hi;change i<14 at hi;interval_cases i <;> rfl
lemma finish_code : BlockAt finish program 21 := by intro i hi;change i<1 at hi;interval_cases i; rfl
lemma code_5 : program[5]? = some (.branchLT 6748 6741 6 21) := rfl
lemma code_20 : program[20]? = some (.jump 5) := rfl
lemma code_22 : program[22]? = some .halt := rfl

structure Header (P N O used j : ℕ) (s : State) : Prop where
 pairs : s.natReg 6740 = P
 count : s.natReg 6741 = N
 output : s.natReg 6742 = O
 used : s.natReg 6743 = used
 zero : s.natReg 6744 = 0
 one : s.natReg 6745 = 1
 two : s.natReg 6746 = 2
 three : s.natReg 6747 = 3
 index : s.natReg 6748 = j

lemma Header.pc {P N O used j : ℕ} {s : State} (h : Header P N O used j s) (p : ℕ) :
 Header P N O used j (setPC s p) :=
 ⟨h.pairs,h.count,h.output,h.used,h.zero,h.one,h.two,h.three,h.index⟩

def Rows (P N : ℕ) (records : ℕ → ℕ × ℕ) (heap : ℕ → Option ℕ) : Prop :=
 ∀ j, j < N → heap (P+2*j)=some (records j).1 ∧ heap (P+2*j+1)=some (records j).2

def storeRow (O ordinal left right : ℕ) (heap : ℕ → Option ℕ) : ℕ → Option ℕ :=
 Function.update (Function.update (Function.update heap (O+3*ordinal) (some left))
  (O+3*ordinal+1) (some right)) (O+3*ordinal+2) (some 1)

def writeRows (O used : ℕ) (records : ℕ → ℕ × ℕ) : ℕ → ℕ → (ℕ → Option ℕ) → (ℕ → Option ℕ)
 | _,0,heap => heap
 | j,fuel+1,heap => writeRows O used records (j+1) fuel
     (storeRow O (used+j) (records j).1 (records j).2 heap)

lemma storeRow_low (O ordinal left right : ℕ) (heap : ℕ → Option ℕ) (a : ℕ)
 (ha : a < O) : storeRow O ordinal left right heap a = heap a := by
 simp (disch := omega) [storeRow]

lemma Rows.storeRow {P N O ordinal left right : ℕ} {records : ℕ → ℕ × ℕ}
 {heap : ℕ → Option ℕ} (h : Rows P N records heap) (fresh : P+2*N ≤ O) :
 Rows P N records (storeRow O ordinal left right heap) := by
 intro j hj
 rw [storeRow_low _ _ _ _ _ _ (by omega),storeRow_low _ _ _ _ _ _ (by omega)]
 exact h j hj

lemma pairBody_header {P N O used j : ℕ} {s : State} (h : Header P N O used j s) :
 Header P N O used (j+1) (applyBlock pairBody s) := by
 constructor <;> simp [pairBody,applyBlock,Op.apply,writeNat,next,
  h.pairs,h.count,h.output,h.used,h.zero,h.one,h.two,h.three,h.index]

lemma pairBody_heap {P N O used j left right : ℕ} {s : State} (h : Header P N O used j s)
 (leftCell : s.natHeap (P+2*j)=some left) (rightCell : s.natHeap (P+2*j+1)=some right) :
 (applyBlock pairBody s).natHeap = storeRow O (used+j) left right s.natHeap := by
 simp only [Nat.mul_comm,Nat.add_assoc] at leftCell rightCell
 simp [pairBody,applyBlock,Op.apply,writeNat,next,h.pairs,h.output,h.used,h.one,h.two,h.three,h.index,
  leftCell,rightCell,storeRow,Nat.mul_comm,Nat.add_assoc]

lemma pairBody_execution {n P N O used j left right B : ℕ} (x : Fin n → ℂ) (s : State)
 (h : Header P N O used j s) (pc : s.pc=6) (wb : WordBound B s)
 (code : 23 ≤ B) (hj : j < N) (sourceFit : P+2*N ≤ B) (outputFit : O+3*(used+N) ≤ B)
 (leftFit : left ≤ B) (rightFit : right ≤ B)
 (leftCell : s.natHeap (P+2*j)=some left) (rightCell : s.natHeap (P+2*j+1)=some right) :
 BoundedRuns program n x B s 14 (applyBlock pairBody s) := by
 simp only [Nat.mul_comm] at leftCell rightCell
 apply block_runs pairBody program 6 n B x s pairBody_code pc wb (by change 20 ≤ B;omega)
 · simp [pairBody,readable,Op.readable,Op.apply,writeNat,next,h.pairs,
    h.one,h.two,h.index,leftCell,rightCell]
 · simp [pairBody,peak,Op.peak,Op.apply,writeNat,next,h.pairs,h.output,h.used,
    h.one,h.two,h.three,h.index,leftCell,rightCell,Nat.mul_comm]
   omega

end
end ExactFourierCircuits.UniformGlobalCalendarUnionRows
