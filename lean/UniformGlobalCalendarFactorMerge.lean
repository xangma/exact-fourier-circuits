import UniformGlobalCalendarSelectorLoop

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarFactorMerge
open UniformMachine UniformAssembly
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
noncomputable section

/-- Multiply one genuine selected native factor lane into the fresh global lane0.
All arithmetic is prepared complex multiplication and has literal charged code. -/
def boot : List Op := [.literal 6744 0,.literal 6745 1,.literal 6746 0,
 .mul 6750 6742 6741,.add 6750 6740 6750]
def body : List Op := [.add 6751 6750 6746,.getScalar 130 6751,.add 6752 6743 6746,
 .getScalar 131 6752,.scalarMul 132 130 131,.putScalar 6752 132,.add 6746 6746 6745]
def program : Program := boot.map Op.code++[.branchLT 6746 6741 6 14]++body.map Op.code++[.jump 5,.halt]
lemma program_length : program.length=15 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma body_code : BlockAt body program 6 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma code_5 : program[5]?=some (.branchLT 6746 6741 6 14) := rfl
lemma code_13 : program[13]?=some (.jump 5) := rfl
lemma code_14 : program[14]?=some .halt := rfl

structure Header (P r lane O j : ℕ) (s : State) : Prop where
 pool : s.natReg 6740=P
 radix : s.natReg 6741=r
 laneReg : s.natReg 6742=lane
 output : s.natReg 6743=O
 zero : s.natReg 6744=0
 one : s.natReg 6745=1
 index : s.natReg 6746=j
 source : s.natReg 6750=P+lane*r

lemma Header.pc {P r lane O j : ℕ} {s : State} (h : Header P r lane O j s) (p : ℕ) :
 Header P r lane O j (setPC s p) :=
 ⟨h.pool,h.radix,h.laneReg,h.output,h.zero,h.one,h.index,h.source⟩

def Factors (A N : ℕ) (f : ℕ → ℂ) (heap : ℕ → Option Scalar) : Prop :=
 ∀ j, j<N → heap (A+j)=some (prepared (f j))
def Tail (O j N : ℕ) (g : ℕ → ℂ) (heap : ℕ → Option Scalar) : Prop :=
 ∀ i, j ≤ i → i < N → heap (O+i)=some (prepared (g i))

def storeProduct (O j : ℕ) (f g : ℕ → ℂ) (heap : ℕ → Option Scalar) : ℕ → Option Scalar :=
 Function.update heap (O+j) (some (prepared (f j*g j)))
def mergeHeap (O : ℕ) (f g : ℕ → ℂ) : ℕ → ℕ → (ℕ → Option Scalar) → (ℕ → Option Scalar)
 | _,0,heap => heap
 | j,fuel+1,heap => mergeHeap O f g (j+1) fuel (storeProduct O j f g heap)

lemma body_header {P r lane O j : ℕ} {s : State} (h : Header P r lane O j s) :
 Header P r lane O (j+1) (applyBlock body s) := by
 constructor <;> simp [body,applyBlock,Op.apply,writeNat,writeScalar,next,
  h.pool,h.radix,h.laneReg,h.output,h.zero,h.one,h.index,h.source]

lemma body_heap {P r lane O j : ℕ} {s : State} (h : Header P r lane O j s) (f g : ℕ → ℂ)
 (source : s.scalarHeap (P+lane*r+j)=some (prepared (f j)))
 (target : s.scalarHeap (O+j)=some (prepared (g j))) :
 (applyBlock body s).scalarHeap=storeProduct O j f g s.scalarHeap := by
 simp [body,applyBlock,Op.apply,writeNat,writeScalar,next,h.output,h.index,h.one,h.source,
  source,target,prepared,evalField,storeProduct]

lemma body_execution {n P r lane O j B : ℕ} (x : Fin n → ℂ) (s : State)
 (h : Header P r lane O j s) (pc : s.pc=6) (wb : WordBound B s) (code : 15≤B)
 (index : j<r) (sourceFit : P+9*r≤B) (laneFit : lane<9) (outputFit : O+r≤B)
 (f g : ℕ → ℂ) (source : s.scalarHeap (P+lane*r+j)=some (prepared (f j)))
 (target : s.scalarHeap (O+j)=some (prepared (g j))) :
 BoundedRuns program n x B s 7 (applyBlock body s) := by
 have laneBound : lane*r≤8*r := Nat.mul_le_mul_right r (by omega)
 apply block_runs body program 6 n B x s body_code pc wb (by change 13≤B;omega)
 · simp [body,readable,Op.readable,Op.apply,writeNat,writeScalar,next,h.output,h.index,h.source,
    source,target,prepared,evalField]
 · simp [body,peak,Op.peak,Op.apply,writeNat,writeScalar,next,h.output,h.index,h.one,h.source,
    source,target,prepared,evalField]
   omega

end
end ExactFourierCircuits.UniformGlobalCalendarFactorMerge
