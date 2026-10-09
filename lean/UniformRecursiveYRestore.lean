import UniformRecursiveSavingExecution
import UniformRecursiveParentReturn
import UniformRecursiveResidualControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveYRestore
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (program address piece Part size offset order)
end P
noncomputable section

def ops:List Op:=[.literal 4189 4,.binary .mul 4189 4122 4189,.binary .add 3364 4123 4189]
def Changed (j:ℕ):Prop:=j=3364∨j=4189
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
lemma restore_frame(s:State)(ret:ℕ):Frame s (setPC (applyBlock ops s) ret):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj
 unfold Changed at hj
 simp (disch:=omega) [ops,applyBlock,Op.apply,evalNat,writeNat,next,setPC]
lemma restore_value(s:State)(F V ret:ℕ)(work:s.natReg 4123=F)(volume:s.natReg 4122=V):
 (setPC (applyBlock ops s) ret).natReg 3364=F+4*V:=by
 simp [ops,applyBlock,Op.apply,evalNat,writeNat,next,setPC,work,volume,Nat.mul_comm]

/-- Four actual instructions overwrite even an arbitrary dirty cached pointer.
There is no incoming3364 readiness premise. -/
theorem generic_execution (main:Program)(start ret n B F V:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt ops main start)(atJump:main[start+3]?=some (.jump ret))
 (pc:s.pc=start)(work:s.natReg 4123=F)(volume:s.natReg 4122=V)
 (bound:WordBound B s)(bufferBound:F+4*V ≤ B)(four:4 ≤ B)(codeEnd:start+4 ≤ B)(returnBound:ret ≤ B):∃u,
 BoundedRuns main n x B s 4 u ∧ u.pc=ret ∧ u.natReg 3364=F+4*V ∧ Frame s u:=by
 have safe:readable ops s∧peak ops s ≤ B:=by
  simp [ops,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,work,volume]
  omega
 have run:=UniformRecursiveResidualControl.block_jump main ops start ret n B x s atCode atJump pc bound
  codeEnd returnBound safe.1 safe.2
 exact ⟨setPC (applyBlock ops s) ret,run,rfl,restore_value s F V ret work volume,restore_frame s ret⟩
lemma code:BlockAt ops P.program (P.address .yRestore):=
 UniformRecursiveSavingExecution.part_block .yRestore ops _ rfl
lemma jump:P.program[P.address .yRestore+3]?=some (.jump (P.address .translation)):=
 UniformRecursiveSavingExecution.part_at .yRestore 3 (by decide)
theorem execution (n B F V:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .yRestore)(work:s.natReg 4123=F)(volume:s.natReg 4122=V)
 (bound:WordBound B s)(bufferBound:F+4*V ≤ B)(four:4 ≤ B)(codeEnd:P.program.length ≤ B):∃u,
 BoundedRuns P.program n x B s 4 u ∧ u.pc=P.address .translation ∧ u.natReg 3364=F+4*V ∧ Frame s u:=
 generic_execution P.program (P.address .yRestore) (P.address .translation) n B F V x s code jump pc work volume
  bound bufferBound four (UniformRecursiveParentReturn.code_bound .yRestore 4 B rfl codeEnd)
  (UniformRecursiveParentReturn.start_bound .translation B codeEnd)

/-- The v1 address order is retained verbatim as a prefix. -/
def previousOrder:List P.Part:=[.entry,.rootAllocate,.readyEntry,.smallSetup,.base,.largeSetup,.seedPrinter,.unitSetup,.unitPrinter,.nodeReady,
 .loop,.reader,.dispatch,.residualMark,.residualInit,.gather,.bootGroups,.groupTest,.call,
 .inverseTest,.inverseSetup,.inverse,.scatterSetup,.scatter,.directionNext,.directionTest,
 .edgeDone,.recordAdvance,.scalar,.translation,.exchange,.marker,
 .paddingInit,.paddingTest,.paddingPatch,.paddingReader,.paddingNext,.paddingFinish,
 .spectatorSetup,.spectator,.finish,.returnSite,.restored,.halt,.orientation]
lemma order_append:P.order=previousOrder++[.yRestore]:=rfl
lemma offset_append_of_mem {α:Type*}[DecidableEq α](size:α→ℕ)(xs ys:List α)(a:α)
 (mem:a∈xs):P.offset size (xs++ys) a=P.offset size xs a:=by
 induction xs with
 | nil=>simp at mem
 | cons b bs ih=>
  by_cases eq:b=a
  · simp [P.offset,eq]
  · have tail:a∈bs:=by rcases List.mem_cons.mp mem with h|h;exact False.elim (eq h.symm);exact h
    simp only [List.cons_append,P.offset,eq,ite_false,ih tail]
theorem old_addresses (a:P.Part)(old:a≠.yRestore):P.address a=P.offset P.size previousOrder a:=by
 unfold P.address
 rw [order_append]
 apply offset_append_of_mem
 cases a  <;>simp_all [previousOrder]
end
end ExactFourierCircuits.UniformRecursiveYRestore
