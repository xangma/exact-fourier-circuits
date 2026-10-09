import UniformRecursiveSavingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNodePreparation
open UniformMachine UniformAssembly BinaryFrames
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords)
namespace P
export UniformRecursiveSavingProgram (Part program piece address size seedLength unitLength unitRecord seedPrinterLength unitPrinterLength)
end P
noncomputable section

lemma unit_nonzero (j : Fin ExplicitSeedBudget.m) : unit j≠0:=by
 intro h
 have hh:=congrFun h j
 simpa [unit] using hh
lemma unit_word (j i : Fin ExplicitSeedBudget.m) :
 P.unitRecord.directions[j.val*ExplicitSeedBudget.m+i.val]'(by
  simp only [UniformRecursiveSavingProgram.unitRecord,List.length_ofFn]
  have hj:=j.isLt;have hi:=i.isLt;nlinarith)= (unit j i).val:=by
 have division:(j.val*ExplicitSeedBudget.m+i.val)/ExplicitSeedBudget.m=j.val:=by
  rw [Nat.mul_comm j.val ExplicitSeedBudget.m,Nat.add_comm,Nat.add_mul_div_left _ _ UniformRecursiveSavingExecution.radix_positive,
   Nat.div_eq_of_lt i.isLt]
  omega
 have modulus:(j.val*ExplicitSeedBudget.m+i.val)%ExplicitSeedBudget.m=i.val:=by
  rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt i.isLt]
 simp only [UniformRecursiveSavingProgram.unitRecord,List.getElem_ofFn,division,modulus,unit]
 by_cases eq:i=j
 · subst i;simp;rfl
 · have ne:j.val≠i.val:=by intro h;exact eq (Fin.ext h.symm)
   simp [eq,ne]
lemma unit_source (U : ℕ) (j : Fin ExplicitSeedBudget.m) (s : State)
 (bank : Printed U P.unitRecord.data s) :
 UniformRepeatedMaskMachine.Source (U+8+j.val*ExplicitSeedBudget.m) (unit j) s:=by
 intro i
 have h:=bank.body (j.val*ExplicitSeedBudget.m+i.val) (by
  simp only [UniformRecursiveSavingProgram.unitRecord,List.length_ofFn]
  have hj:=j.isLt;have hi:=i.isLt;nlinarith)
 rw [unit_word] at h
 simpa only [Nat.add_assoc] using h

/-- Allocation proof uses symbolic payload lengths, so no giant fixed table is
normalized by the kernel. The held Program specializes these two constants. -/
def unitBase (F M : ℕ) := F+M
def workBase (F M l : ℕ) := unitBase F M+l+6

def unitSetupOps (M l : ℕ) : List Op := [.literal 4170 M,.binary .add 2600 2600 4170,
 .literal 4171 (l+6),.binary .add 4123 2600 4171,
 .literal 4179 2,.binary .sub 4178 4123 4179,.store 4178 2600,
 .literal 4179 1,.binary .sub 4178 4123 4179,.store 4178 2600,
 .literal 4179 6,.binary .sub 4178 4123 4179]
lemma unitSetup_code : BlockAt (unitSetupOps P.seedLength P.unitLength) P.program (P.address .unitSetup):=by
 simpa only [List.append_nil] using UniformRecursiveSavingExecution.part_block .unitSetup
  (unitSetupOps P.seedLength P.unitLength) [] rfl
lemma unitSetup_length (M l : ℕ) : (unitSetupOps M l).length=12:=rfl
lemma unitSetup_follow : P.address .unitSetup+12=P.address .unitPrinter:=by
 simp only [UniformRecursiveSavingProgram.address]
 simp [UniformRecursiveSavingProgram.offset,UniformRecursiveSavingProgram.order,UniformRecursiveSavingProgram.size]
 omega

def UnitSetupChanged (i : ℕ) : Prop := i=4170∨i=2600∨i=4171∨i=4123∨i=4179∨i=4178
structure UnitSetupFrame (F M l : ℕ) (s u : State) : Prop where
 natHeap:∀z,z<unitBase F M+l+4∨unitBase F M+l+6≤z→u.natHeap z=s.natHeap z
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬UnitSetupChanged i→u.natReg i=s.natReg i
lemma unitSetup_values (F M l : ℕ) (s : State) (base:s.natReg 2600=F) :
 (applyBlock (unitSetupOps M l) s).natReg 2600=unitBase F M ∧
 (applyBlock (unitSetupOps M l) s).natReg 4123=workBase F M l ∧
 (applyBlock (unitSetupOps M l) s).natHeap (workBase F M l-2)=some (unitBase F M) ∧
 (applyBlock (unitSetupOps M l) s).natHeap (workBase F M l-1)=some (unitBase F M):=by
 have ne:F+(M+(l+6))-2≠F+(M+(l+6))-1:=by omega
 simp [unitSetupOps,applyBlock,Op.apply,evalNat,writeNat,next,base,unitBase,workBase,Nat.add_assoc,ne]
lemma unitSetup_frame (F M l : ℕ) (s : State) (base:s.natReg 2600=F) :
 UnitSetupFrame F M l s (applyBlock (unitSetupOps M l) s):=by
 refine ⟨?_,rfl,rfl,rfl,rfl,?_⟩
 · intro z hz
   have ne2:z≠workBase F M l-2:=by unfold workBase at *;omega
   have ne1:z≠workBase F M l-1:=by unfold workBase at *;omega
   simp [unitSetupOps,applyBlock,Op.apply,evalNat,writeNat,next,base,unitBase,workBase,Nat.add_assoc] at ne2 ne1 ⊢
   simp only [Function.update_of_ne ne1,Function.update_of_ne ne2]
 · intro i hi
   unfold UnitSetupChanged at hi
   simp (disch:=omega) [unitSetupOps,applyBlock,Op.apply,evalNat,writeNat,next]

theorem unitSetup_generic_execution (p : Program) (start n B F M l : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=start) (base:s.natReg 2600=F) (bound:WordBound B s)
 (code:BlockAt (unitSetupOps M l) p start) (codeEnd:start+12≤B) (endptr:workBase F M l≤B) :
 BoundedRuns p n x B s 12 (applyBlock (unitSetupOps M l) s) ∧
 (applyBlock (unitSetupOps M l) s).pc=start+12 ∧ UnitSetupFrame F M l s (applyBlock (unitSetupOps M l) s):=by
 have ub:unitBase F M≤B:=by unfold workBase at endptr;omega
 have lb:l+6≤B:=by unfold workBase at endptr;omega
 have sb:M≤B:=by unfold unitBase at ub;omega
 have endb:F+(M+(l+6))≤B:=by simpa [workBase,unitBase,Nat.add_assoc] using endptr
 have safe:readable (unitSetupOps M l) s ∧ peak (unitSetupOps M l) s≤B:=by
  simp [unitSetupOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,base,unitBase,workBase,Nat.add_assoc]
  omega
 have run:=block_runs (unitSetupOps M l) p start n B x s code pc bound
  (by rwa [unitSetup_length]) safe.1 safe.2
 refine ⟨by simpa only [unitSetup_length] using run,?_,unitSetup_frame F M l s base⟩
 simp [unitSetupOps,applyBlock,Op.apply,writeNat,next,pc]

theorem unitSetup_execution (n B F : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .unitSetup) (base:s.natReg 2600=F) (bound:WordBound B s)
 (code:P.program.length≤B) (endptr:workBase F P.seedLength P.unitLength≤B) :
 BoundedRuns P.program n x B s 12 (applyBlock (unitSetupOps P.seedLength P.unitLength) s) ∧
 (applyBlock (unitSetupOps P.seedLength P.unitLength) s).pc=P.address .unitPrinter ∧
 UnitSetupFrame F P.seedLength P.unitLength s (applyBlock (unitSetupOps P.seedLength P.unitLength) s):=by
 obtain ⟨run,up,frame⟩:=unitSetup_generic_execution P.program (P.address .unitSetup) n B F P.seedLength P.unitLength x s
  pc base bound unitSetup_code ((UniformRecursiveSavingExecution.part_bound .unitSetup).trans code) endptr
 exact ⟨run,up.trans unitSetup_follow,frame⟩

lemma local_placed (s : State) (start : ℕ) (pc:s.pc=start) : placed start {s with pc:=0}=s:=by
 cases s
 simp_all [placed]

lemma printed_pc (A : ℕ) (data : List ℕ) (s : State) (pc : ℕ) (h:Printed A data s) :
 Printed A data {s with pc:=pc}:=by
 intro j hj
 exact h j hj
lemma printedRecords_pc (A : ℕ) (rs : List Record) (s : State) (pc : ℕ) (h:PrintedRecords A rs s) :
 PrintedRecords A rs {s with pc:=pc}:=by
 induction rs generalizing A with
 | nil=>trivial
 | cons r rs ih=>exact ⟨printed_pc A r.data s pc h.1,ih (A+r.data.length) h.2⟩

/-- The actual fixed runtime-column writer is executed inside the common
Program; the template and every column patch are physically generated. -/
theorem seed_execution (n B F q : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .seedPrinter) (base:s.natReg 2600=F) (columns:s.natReg 2599=q)
 (bound:WordBound B s) (code:P.program.length≤B)
 (literals:UniformFixedNetworkScheduleMachine.literalCap
  (UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule)≤B)
 (extent:F+P.seedLength+1≤B) : ∃u,
 BoundedRuns P.program n x B s P.seedPrinterLength u ∧ u.pc=P.address .unitSetup ∧
 PrintedRecords F (UniformFixedNetworkScheduleMachine.scheduleRecords q) u ∧
 (∀z,z<F∨F+P.seedLength≤z→u.natHeap z=s.natHeap z) ∧
 UniformFixedNetworkLiteralDecoderMachine.Frame s u:=by
 let localState:State:={s with pc:=0}
 have lb:WordBound B localState:=changePC_bound B s 0 bound (Nat.zero_le _)
 have cb:P.seedPrinterLength≤B:=by have h:=UniformRecursiveSavingExecution.part_bound .seedPrinter;change P.address .seedPrinter+P.seedPrinterLength≤P.program.length at h;omega
 obtain ⟨t,run,bank,outside,frame⟩:=UniformFixedNetworkLiteralDecoderMachine.fixed_execution F B q n x localState
  base columns rfl lb literals extent cb
 let u:State:={t with pc:=P.address .unitSetup}
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed UniformRecursiveSavingProgram.printer_code
  (by rw [UniformRecursiveSavingProgram.seedPrinter_length];exact (UniformRecursiveSavingExecution.part_bound .seedPrinter).trans code)
  (by have h:=(UniformRecursiveSavingExecution.part_bound .unitSetup).trans code;omega) run
 rw [local_placed s _ pc] at placedRun
 refine ⟨u,placedRun,rfl,printedRecords_pc _ _ _ _ bank,outside,?_⟩
 exact ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots,frame.natReg⟩

def binaryUnitRecord (m : ℕ) : Record :=
 ⟨0,0,m,0,0,0,m,0,List.ofFn (fun i:Fin (m*m)=>if i.val/m=i.val%m then 1 else 0)⟩
lemma binaryUnitRecord_literals (m B : ℕ) (hm:m≤B) (one:1≤B) :
 ∀v∈(binaryUnitRecord m).data,v≤B:=by
 intro v hv
 rcases List.mem_append.mp hv with head|body
 · simp only [binaryUnitRecord,Record.header,List.mem_cons,List.not_mem_nil,or_false] at head
   rcases head with h|h|h|h|h|h|h|h <;> subst v <;> omega
 · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp body
   split <;> omega
lemma unitRecord_eq : P.unitRecord=binaryUnitRecord ExplicitSeedBudget.m:=rfl
lemma unit_literals (B : ℕ) (m:ExplicitSeedBudget.m≤B) : ∀v∈P.unitRecord.data,v≤B:=by
 rw [unitRecord_eq]
 exact binaryUnitRecord_literals ExplicitSeedBudget.m B m
  (UniformRecursiveSavingExecution.radix_positive.trans_le m)

lemma unit_code : CodeAt (UniformFixedNetworkScheduleMachine.program P.unitRecord.data) P.program
 (P.address .unitPrinter) (P.address .nodeReady):=UniformRecursiveSavingProgram.part_child rfl

/-- Relocation of the literal writer is proved for an arbitrary list, keeping
fixed payloads symbolic throughout the proof. -/
theorem printer_placed (p : Program) (data : List ℕ) (start ret n B U : ℕ)
 (x : Fin n→ℂ) (s : State) (pc:s.pc=start) (base:s.natReg 2600=U) (bound:WordBound B s)
 (atCode:CodeAt (UniformFixedNetworkScheduleMachine.program data) p start ret)
 (code:start+(UniformFixedNetworkScheduleMachine.program data).length≤B) (returnBound:ret≤B)
 (values:∀v∈data,v≤B) (extent:U+data.length≤B) : ∃u,
 BoundedRuns p n x B s (3*data.length+4) u ∧ u.pc=ret ∧
 Printed U data u ∧ (∀z,z<U∨U+data.length≤z→u.natHeap z=s.natHeap z) ∧
 UniformFixedNetworkScheduleMachine.Frame s u:=by
 let localState:State:={s with pc:=0}
 have lb:WordBound B localState:=changePC_bound B s 0 bound (Nat.zero_le _)
 obtain ⟨t,run,bank,outside,frame,_ptr⟩:=UniformFixedNetworkScheduleMachine.printer_execution data U B n x localState
  base rfl lb values extent (by rw [UniformFixedNetworkScheduleMachine.program_length] at code;omega)
 let u:State:={t with pc:=ret}
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed atCode code returnBound run
 rw [local_placed s _ pc] at placedRun
 refine ⟨u,placedRun,rfl,printed_pc U data t ret bank,outside,?_⟩
 exact ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots,frame.natReg⟩

/-- The unit-frame directions used by padding are printed by the actual
Nat-only writer, including all zero coordinates. -/
theorem unit_execution (n B U : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .unitPrinter) (base:s.natReg 2600=U) (bound:WordBound B s)
 (code:P.program.length≤B) (m:ExplicitSeedBudget.m≤B) (extent:U+P.unitLength≤B) : ∃u,
 BoundedRuns P.program n x B s P.unitPrinterLength u ∧ u.pc=P.address .nodeReady ∧
 Printed U P.unitRecord.data u ∧ (∀z,z<U∨U+P.unitLength≤z→u.natHeap z=s.natHeap z) ∧
 UniformFixedNetworkScheduleMachine.Frame s u:=by
 have run:=printer_placed P.program P.unitRecord.data (P.address .unitPrinter) (P.address .nodeReady) n B U x s
  pc base bound unit_code
  (by rw [UniformRecursiveSavingProgram.unitPrinter_length];exact (UniformRecursiveSavingExecution.part_bound .unitPrinter).trans code)
  (by have h:=(UniformRecursiveSavingExecution.part_bound .nodeReady).trans code;omega)
  (unit_literals B m) (by rwa [UniformRecursiveSavingProgram.unitRecord_length])
 simpa only [UniformRecursiveSavingProgram.unitRecord_length,UniformRecursiveSavingProgram.unitPrinterLength] using run

def readyLoad (M : ℕ) : List Op := [.literal 4179 2,.binary .sub 4178 4123 4179,.load 4170 4178,
 .literal 4171 M,.binary .sub 2850 4170 4171]
def readyPatch : List Op := [.literal 4171 1,.binary .add 4178 4170 4171,.store 4178 4060]
def readyPools : List Op := [.literal 4171 3,.binary .mul 4172 4122 4171,.binary .add 3389 4123 4172,
 .literal 4171 4,.binary .mul 4172 4122 4171,.binary .add 3364 4123 4172]
def nodeReadyOps (M : ℕ) : List Op := readyLoad M++readyPatch++readyPools
lemma block_pc (ops : List Op) (s : State) : (applyBlock ops s).pc=s.pc+ops.length:=by
 induction ops generalizing s with
 | nil=>simp [applyBlock]
 | cons o ops ih=>rw [applyBlock,ih,Op.apply_pc,List.length_cons];omega
lemma block_append (a b : List Op) (s : State) : applyBlock (a++b) s=applyBlock b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>rfl
 | cons o a ih=>exact ih (o.apply s)
lemma readable_append (a b : List Op) (s : State) : readable (a++b) s↔readable a s∧readable b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>simp [readable,applyBlock]
 | cons o a ih=>simp only [List.cons_append,readable,applyBlock,ih,and_assoc]
lemma peak_append (a b : List Op) (s : State) : peak (a++b) s=max (peak a s) (peak b (applyBlock a s)):=by
 induction a generalizing s with
 | nil=>simp [peak,applyBlock]
 | cons o a ih=>simp only [List.cons_append,peak,applyBlock,ih,max_assoc]

lemma readyLoad_values (F M J : ℕ) (s : State) (ptr:s.natReg 4123=J)
 (stored:s.natHeap (J-2)=some (F+M)) :
 (applyBlock (readyLoad M) s).natReg 4170=F+M ∧
 (applyBlock (readyLoad M) s).natReg 2850=F:=by
 simp [readyLoad,applyBlock,Op.apply,evalNat,writeNat,next,ptr,stored]
lemma readyLoad_keep (M : ℕ) (s : State) (i : ℕ) (safe:i≠4179∧i≠4178∧i≠4170∧i≠4171∧i≠2850) :
 (applyBlock (readyLoad M) s).natReg i=s.natReg i:=by
 simp [readyLoad,applyBlock,Op.apply,evalNat,writeNat,next,safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2]
lemma readyPatch_heap (U q : ℕ) (s : State) (ptr:s.natReg 4170=U) (columns:s.natReg 4060=q) :
 (applyBlock readyPatch s).natHeap=Function.update s.natHeap (U+1) (some q):=by
 simp [readyPatch,applyBlock,Op.apply,evalNat,writeNat,next,ptr,columns]
lemma readyPatch_keep (s : State) (i : ℕ) (safe:i≠4171∧i≠4178) :
 (applyBlock readyPatch s).natReg i=s.natReg i:=by
 simp [readyPatch,applyBlock,Op.apply,evalNat,writeNat,next,safe.1,safe.2]
lemma readyPools_values (J V : ℕ) (s : State) (ptr:s.natReg 4123=J) (volume:s.natReg 4122=V) :
 (applyBlock readyPools s).natReg 3389=J+3*V ∧ (applyBlock readyPools s).natReg 3364=J+4*V:=by
 simp [readyPools,applyBlock,Op.apply,evalNat,writeNat,next,ptr,volume,Nat.mul_comm]
lemma readyPools_keep (s : State) (i : ℕ) (safe:i≠4171∧i≠4172∧i≠3389∧i≠3364) :
 (applyBlock readyPools s).natReg i=s.natReg i:=by
 simp [readyPools,applyBlock,Op.apply,evalNat,writeNat,next,safe.1,safe.2.1,safe.2.2.1,safe.2.2.2]
lemma nodeReady_length (M : ℕ) : (nodeReadyOps M).length=14:=rfl
lemma nodeReady_code : BlockAt (nodeReadyOps P.seedLength) P.program (P.address .nodeReady):=
 UniformRecursiveSavingExecution.part_block .nodeReady _ _ rfl
lemma nodeReady_jump : P.program[P.address .nodeReady+14]?=some (.jump (P.address .loop)):=
 UniformRecursiveSavingExecution.part_at .nodeReady 14 (by decide)

def NodeReadyChanged (i : ℕ) : Prop := i=4179∨i=4178∨i=4170∨i=4171∨i=2850∨i=4172∨i=3389∨i=3364
structure NodeReadyFrame (U : ℕ) (s u : State) : Prop where
 natHeap:∀z,z≠U+1→u.natHeap z=s.natHeap z
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬NodeReadyChanged i→u.natReg i=s.natReg i
lemma nodeReady_values (F M J V q : ℕ) (s : State) (ptr:s.natReg 4123=J) (volume:s.natReg 4122=V)
 (columns:s.natReg 4060=q) (stored:s.natHeap (J-2)=some (F+M)) :
 (applyBlock (nodeReadyOps M) s).natReg 2850=F ∧
 (applyBlock (nodeReadyOps M) s).natReg 3389=J+3*V ∧
 (applyBlock (nodeReadyOps M) s).natReg 3364=J+4*V ∧
 (applyBlock (nodeReadyOps M) s).natHeap (F+M+1)=some q:=by
 let a:=applyBlock (readyLoad M) s
 let b:=applyBlock readyPatch a
 have av:=readyLoad_values F M J s ptr stored
 have keep (i : ℕ) (h:i≠4171∧i≠4178∧i≠4179∧i≠4170∧i≠2850) : b.natReg i=s.natReg i:=
  (readyPatch_keep a i (by omega)).trans (readyLoad_keep M s i (by omega))
 have bp:b.natReg 4123=J:=(keep 4123 (by omega)).trans ptr
 have bv:b.natReg 4122=V:=(keep 4122 (by omega)).trans volume
 have bc:b.natReg 2850=F:=(readyPatch_keep a 2850 (by omega)).trans av.2
 have aq:a.natReg 4060=q:=(readyLoad_keep M s 4060 (by omega)).trans columns
 have bh:b.natHeap=Function.update s.natHeap (F+M+1) (some q):=readyPatch_heap (F+M) q a av.1 aq
 rw [nodeReadyOps,block_append,block_append]
 change (applyBlock readyPools b).natReg 2850=F ∧ _
 have pools:=readyPools_values J V b bp bv
 refine ⟨(readyPools_keep b 2850 (by omega)).trans bc,pools.1,pools.2,?_⟩
 change b.natHeap (F+M+1)=some q
 rw [bh,Function.update_self]
lemma nodeReady_frame (F M J : ℕ) (s : State) (ptr:s.natReg 4123=J) (stored:s.natHeap (J-2)=some (F+M)) :
 NodeReadyFrame (F+M) s (applyBlock (nodeReadyOps M) s):=by
 let a:=applyBlock (readyLoad M) s
 let b:=applyBlock readyPatch a
 have av:=readyLoad_values F M J s ptr stored
 have aq:a.natReg 4060=s.natReg 4060:=readyLoad_keep M s 4060 (by omega)
 have bh:b.natHeap=Function.update s.natHeap (F+M+1) (some (s.natReg 4060)):=readyPatch_heap (F+M) (s.natReg 4060) a av.1 aq
 rw [nodeReadyOps,block_append,block_append]
 refine ⟨?_,rfl,rfl,rfl,rfl,?_⟩
 · intro z hz
   change b.natHeap z=s.natHeap z
   rw [bh,Function.update_of_ne hz]
 · intro i hi
   unfold NodeReadyChanged at hi
   exact (readyPools_keep b i (by omega)).trans ((readyPatch_keep a i (by omega)).trans (readyLoad_keep M s i (by omega)))

lemma printed_patch_columns (U q : ℕ) (r : Record) (s u : State) (bank:Printed U r.data s)
 (field:u.natHeap (U+1)=some q) (outside:∀z,z≠U+1→u.natHeap z=s.natHeap z) :
 Printed U (r.withColumns q).data u:=by
 intro j hj
 have hj':j<r.data.length:=by rwa [UniformFixedNetworkLiteralDecoderMachine.data_columns_length] at hj
 rw [UniformFixedNetworkLiteralDecoderMachine.data_columns q r j hj']
 by_cases eq:j=1
 · subst j;exact field
 · rw [if_neg eq,outside (U+j) (by omega)]
   exact bank j hj'

lemma nodeReady_safe (F M l V q B : ℕ) (s : State)
 (ptr:s.natReg 4123=workBase F M l) (volume:s.natReg 4122=V) (columns:s.natReg 4060=q)
 (stored:s.natHeap (workBase F M l-2)=some (F+M))
 (qb:q≤B) (pool:workBase F M l+4*V≤B) : readable (nodeReadyOps M) s∧peak (nodeReadyOps M) s≤B:=by
 let a:=applyBlock (readyLoad M) s
 let b:=applyBlock readyPatch a
 have av:=readyLoad_values F M (workBase F M l) s ptr stored
 have ap:a.natReg 4170=F+M:=av.1
 have aq:a.natReg 4060=q:=(readyLoad_keep M s 4060 (by omega)).trans columns
 have bp:b.natReg 4123=workBase F M l:=
  (readyPatch_keep a 4123 (by omega)).trans ((readyLoad_keep M s 4123 (by omega)).trans ptr)
 have bv:b.natReg 4122=V:=
  (readyPatch_keep a 4122 (by omega)).trans ((readyLoad_keep M s 4122 (by omega)).trans volume)
 have safeload:readable (readyLoad M) s∧peak (readyLoad M) s≤B:=by
  simp [readyLoad,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,ptr,stored]
  unfold workBase unitBase at *
  omega
 have safepatch:readable readyPatch a∧peak readyPatch a≤B:=by
  simp [readyPatch,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,ap,aq]
  unfold workBase unitBase at *
  omega
 have safepools:readable readyPools b∧peak readyPools b≤B:=by
  simp [readyPools,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,bp,bv,Nat.mul_comm]
  unfold workBase unitBase at *
  omega
 simp only [nodeReadyOps,readable_append,peak_append,block_append,max_le_iff]
 exact ⟨⟨⟨safeload.1,safepatch.1⟩,safepools.1⟩,⟨⟨safeload.2,safepatch.2⟩,safepools.2⟩⟩

/-- The fourteen concrete operations plus their real continuation jump are
proved with symbolic code addresses and lengths; no fixed payload is expanded. -/
theorem nodeReady_generic_execution (p : Program) (start ret total n B F M l V q : ℕ) (x : Fin n→ℂ) (s : State)
 (len:total=15) (atCode:BlockAt (nodeReadyOps M) p start) (atJump:p[start+14]?=some (.jump ret))
 (pc:s.pc=start) (ptr:s.natReg 4123=workBase F M l) (volume:s.natReg 4122=V) (columns:s.natReg 4060=q)
 (stored:s.natHeap (workBase F M l-2)=some (unitBase F M))
 (bound:WordBound B s) (code:start+total≤B) (returnBound:ret≤B) (pool:workBase F M l+4*V≤B) : ∃u,
 BoundedRuns p n x B s total u ∧ u.pc=ret ∧ u.natReg 2850=F ∧
 u.natReg 3389=workBase F M l+3*V ∧ u.natReg 3364=workBase F M l+4*V ∧
 u.natHeap (unitBase F M+1)=some q ∧ NodeReadyFrame (unitBase F M) s u:=by
 have qb:q≤B:=by have h:=bound.2.1 4060;rwa [columns] at h
 have safe:=nodeReady_safe F M l V q B s ptr volume columns stored qb pool
 have run:=block_runs (nodeReadyOps M) p start n B x s atCode pc bound
  (by rw [nodeReady_length];omega) safe.1 safe.2
 let t:=applyBlock (nodeReadyOps M) s
 let u:State:={t with pc:=ret}
 have tp:t.pc=start+14:=by rw [block_pc,pc,nodeReady_length]
 have ubound:=changePC_bound B t ret run.final_bound returnBound
 have jump:BoundedRuns p n x B t 1 u:=.next run.final_bound
  (by simp [step,tp,atJump,u]) (.refl ubound)
 obtain ⟨cursor,table,buffer,field⟩:=nodeReady_values F M (workBase F M l) V q s ptr volume columns stored
 refine ⟨u,?_,rfl,cursor,table,buffer,field,?_⟩
 · simpa only [nodeReady_length,len] using run.trans jump
 · have h:=nodeReady_frame F M (workBase F M l) s ptr stored
   exact ⟨h.natHeap,h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩

/-- Actual node readiness in the held common Program. -/
theorem nodeReady_execution (n B F M l V q : ℕ) (x : Fin n→ℂ) (s : State)
 (eqM:M=P.seedLength) (pc:s.pc=P.address .nodeReady) (ptr:s.natReg 4123=workBase F M l)
 (volume:s.natReg 4122=V) (columns:s.natReg 4060=q)
 (stored:s.natHeap (workBase F M l-2)=some (unitBase F M))
 (bound:WordBound B s) (code:P.program.length≤B) (pool:workBase F M l+4*V≤B) : ∃u,
 BoundedRuns P.program n x B s (P.size .nodeReady) u ∧ u.pc=P.address .loop ∧ u.natReg 2850=F ∧
 u.natReg 3389=workBase F M l+3*V ∧ u.natReg 3364=workBase F M l+4*V ∧
 u.natHeap (unitBase F M+1)=some q ∧ NodeReadyFrame (unitBase F M) s u:=by
 exact nodeReady_generic_execution P.program (P.address .nodeReady) (P.address .loop) (P.size .nodeReady)
  n B F M l V q x s rfl (by rw [eqM];exact nodeReady_code) nodeReady_jump pc ptr volume columns stored bound
  ((UniformRecursiveSavingExecution.part_bound .nodeReady).trans code)
  ((Nat.le_add_right _ _).trans ((UniformRecursiveSavingExecution.part_bound .loop).trans code)) pool
end
end ExactFourierCircuits.UniformRecursiveNodePreparation
