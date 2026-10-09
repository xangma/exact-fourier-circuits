import UniformRecursiveSmallBase
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSmallExecution
open UniformMachine UniformAssembly UniformBinaryTensorCoordinates
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (program address size threshold)
end P
namespace T
export UniformBinaryBatchCMachine (arrayBase arrayCost transformed)
end T
namespace S
export UniformRecursiveSmallBase (Frame Changed baseTicks)
end S
noncomputable section

lemma start_bound (a:UniformRecursiveSavingProgram.Part)(B:ℕ)(code:P.program.length≤B):P.address a≤B:=by
 have h:=(UniformRecursiveSavingExecution.part_bound a).trans code
 omega
lemma zero_cell (main:Program)(loc:ℕ)(i:Instruction)(h:main[loc+0]?=some i):main[loc]?=some i:=by
 simpa only [Nat.add_zero] using h
lemma ready_literal:P.program[P.address .readyEntry]?=some (.natLiteral 4177 P.threshold):=
 zero_cell P.program (P.address .readyEntry) _ (UniformRecursiveSavingExecution.ready_at 0 (by omega))
lemma ready_branch:P.program[P.address .readyEntry+1]?=
 some (.branchLT 4120 4177 (P.address .smallSetup) (P.address .largeSetup)):=
 UniformRecursiveSavingExecution.ready_at 1 (by omega)
lemma setup_code:UniformNatBlockMachine.BlockAt
 (UniformRecursiveSmallPrologue.setupOps UniformRecursiveSelfCallMachine.W) P.program (P.address .smallSetup):=by
 simpa only [List.append_nil] using UniformRecursiveSavingExecution.part_block .smallSetup
  (UniformRecursiveSmallPrologue.setupOps UniformRecursiveSelfCallMachine.W) [] rfl
lemma setup_follow:P.address .smallSetup+4=P.address .base:=rfl
lemma finish_code:P.program[P.address .finish]?=
 some (.branchLT 4151 4153 (P.address .halt) (P.address .returnSite)):=
 zero_cell P.program (P.address .finish) _ (UniformRecursiveSavingExecution.part_at .finish 0 (by decide))
lemma halt_code:P.program[P.address .halt]?=some .halt:=
 zero_cell P.program (P.address .halt) _ (UniformRecursiveSavingExecution.part_at .halt 0 (by decide))

/-- The actual corrected-v2 saving program's complete small branch, for all W
stored roles and either root or descendant stack depth. -/
theorem execution (n B k A depth:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=P.address .readyEntry)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(dp:s.natReg 4151=depth)(small:k<P.threshold)
 (data:∀w z,s.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z))
 (heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (code:P.program.length≤B)(thresholdBound:P.threshold≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B):∃u,
 BoundedRuns P.program n x B s (S.baseTicks UniformRecursiveSelfCallMachine.W k) u ∧
 u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
 (∀w z,u.scalarHeap (T.arrayBase A k w.val+z.val)=some (T.transformed k (v w) z)) ∧
 (∀w z,(u.scalarHeap (T.arrayBase A k w.val+z.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
 S.Frame A (UniformRecursiveSelfCallMachine.W*2^k) s u ∧UniformBinaryCStageMachine.Constants u:=by
 apply UniformRecursiveSmallBase.execution_generic P.program (P.address .readyEntry) (P.address .smallSetup)
  (P.address .base) (P.address .largeSetup) (P.address .finish) (P.address .halt) (P.address .returnSite)
  P.threshold UniformRecursiveSelfCallMachine.W n B k A depth x s v
  ready_literal ready_branch setup_code setup_follow UniformRecursiveSavingProgram.base_code finish_code
  pc one bits base size dp small data heapBase constants bound
  (UniformRecursiveSavingExecution.part_bound .readyEntry |>.trans code)
  (UniformRecursiveSavingExecution.part_bound .smallSetup |>.trans code)
  ?_ (start_bound .finish B code) (start_bound .halt B code) (start_bound .returnSite B code)
  thresholdBound countBound extent
 have h:=(UniformRecursiveSavingExecution.part_bound .base).trans code
 change P.address .base+54≤B at h
 simpa only [UniformBinaryBatchCMachine.program_length] using h

lemma frame_stack {A volume:ℕ}{s u:State}(f:S.Frame A volume s u):
 u.natReg 4150=s.natReg 4150 ∧u.natReg 4151=s.natReg 4151 ∧u.natReg 4153=s.natReg 4153:=by
 constructor
 · exact f.natReg _ (by unfold S.Changed UniformRecursiveSmallPrologue.Changed UniformBinaryBatchCMachine.Changed UniformBinaryTensorCMachine.Changed;omega)
 constructor
 · exact f.natReg _ (by unfold S.Changed UniformRecursiveSmallPrologue.Changed UniformBinaryBatchCMachine.Changed UniformBinaryTensorCMachine.Changed;omega)
 · exact f.natReg _ (by unfold S.Changed UniformRecursiveSmallPrologue.Changed UniformBinaryBatchCMachine.Changed UniformBinaryTensorCMachine.Changed;omega)

/-- Root execution includes the genuine halt, separately from the finish
branch; its instruction count is W*arrayCost k+13. -/
theorem root_execution (n B k A:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=P.address .readyEntry)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(dp:s.natReg 4151=0)(small:k<P.threshold)
 (data:∀w z,s.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z))
 (heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (code:P.program.length≤B)(thresholdBound:P.threshold≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B):∃u,
 BoundedExecution P.program n x B s (S.baseTicks UniformRecursiveSelfCallMachine.W k+1) u ∧
 u.pc=P.address .halt ∧
 (∀w z,u.scalarHeap (T.arrayBase A k w.val+z.val)=some (T.transformed k (v w) z)) ∧
 (∀w z,(u.scalarHeap (T.arrayBase A k w.val+z.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
 S.Frame A (UniformRecursiveSelfCallMachine.W*2^k) s u ∧UniformBinaryCStageMachine.Constants u:=by
 obtain ⟨u,run,up,out,values,frame,con⟩:=execution n B k A 0 x s v pc one bits base size dp small data
  heapBase constants bound code thresholdBound countBound extent
 have stop:u.pc=P.address .halt:=by simpa only [ite_true] using up
 have halt:BoundedExecution P.program n x B u 1 u:=.halt run.final_bound (by simp only [step,stop,halt_code])
 exact ⟨u,run.executes halt,stop,out,values,frame,con⟩

end
end ExactFourierCircuits.UniformRecursiveSmallExecution
