import UniformGlobalDiagonalChildPrefix
import UniformRecursiveSavingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSameProgramSectorLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Generated sector count464 and5word directory4441 are retained at high
registers. Fresh5801 is reused only because each root child allocates outside
all live sector banks; proving that child execution is still outstanding. -/
def boot:List Op:=[.literal 5895 0,.literal 5891 1,.literal 5892 0,
 .add 5890 464 5895,.add 5893 4441 5895,.add 5894 5801 5895,.literal 5896 5]
def setup:List Op:=[.mul 5897 5892 5896,.add 5897 5893 5897,.getNat 4120 5897,
 .add 5897 5897 5891,.getNat 4122 5897,.add 5897 5897 5891,.getNat 4121 5897,
 .add 4123 5894 5895,.literal 4151 0]
def finish:List Op:=[.add 5892 5892 5891]
/-- Abstract static placement lemma boundary, specialized below to the ONE
held actual recursive C program. No actual bytecode payload is expanded. -/
def assembly (child:Program):Program:=boot.map Op.code++[.branchLT 5892 5890 8 (child.length+19)]++
 setup.map Op.code++child.map (relocate 17 (17+child.length))++
 finish.map Op.code++[.jump 7,.halt]
def program:Program:=assembly UniformRecursiveSavingProgram.program
lemma boot_length:boot.length=7:=rfl
lemma setup_length:setup.length=9:=rfl
lemma finish_length:finish.length=1:=rfl
lemma assembly_length (child:Program):(assembly child).length=child.length+20:=by
 simp only[assembly,List.length_append,List.length_map,boot_length,setup_length,finish_length,
  List.length_cons,List.length_nil];omega
lemma program_length:program.length=UniformRecursiveSavingProgram.program.length+20:=assembly_length _
lemma boot_code (child:Program):BlockAt boot (assembly child) 0:=by
 intro i hi;change i<7 at hi;interval_cases i <;>rfl
lemma setup_code (child:Program):BlockAt setup (assembly child) 8:=by
 have h:=UniformRankCrossPreparationMachine.block_of_segment setup
  (boot.map Op.code++[.branchLT 5892 5890 8 (child.length+19)])
  (child.map (relocate 17 (17+child.length))++finish.map Op.code++[.jump 7,.halt]) 8
  (by rw[List.length_append,List.length_map,boot_length];rfl)
 simpa only[assembly,List.append_assoc] using h
lemma child_code (child:Program):CodeAt child (assembly child) 17 (17+child.length):=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 5892 5890 8 (child.length+19)]++setup.map Op.code)
  (finish.map Op.code++[.jump 7,.halt]) child 17 (17+child.length)
  (by simp only[List.length_append,List.length_map,boot_length,setup_length,List.length_cons,List.length_nil])
 simpa only[assembly,List.append_assoc] using h
lemma actual_child_code:CodeAt UniformRecursiveSavingProgram.program program 17
 (17+UniformRecursiveSavingProgram.program.length):=child_code _
lemma branch_at (child:Program):(assembly child)[7]?=some (.branchLT 5892 5890 8 (child.length+19)):=by
 unfold assembly
 rw[List.getElem?_append_left (by simp only[List.length_append,List.length_map,boot_length,setup_length,
  finish_length,List.length_cons,List.length_nil];omega)]
 rw[List.getElem?_append_left (by simp only[List.length_append,List.length_map,boot_length,setup_length,
  List.length_cons,List.length_nil];omega)]
 rw[List.getElem?_append_left (by simp only[List.length_append,List.length_map,boot_length,setup_length,
  List.length_cons,List.length_nil];omega)]
 rw[List.getElem?_append_left (by simp only[List.length_append,List.length_map,boot_length,
  List.length_cons,List.length_nil];omega)]
 rw[List.getElem?_append_right (by rw[List.length_map,boot_length])]
 simp only[List.length_map,boot_length];rfl

structure Cursor (M E frontier i:ℕ) (s:State):Prop where
 count:s.natReg 5890=M
 one:s.natReg 5891=1
 index:s.natReg 5892=i
 directory:s.natReg 5893=E
 fresh:s.natReg 5894=frontier
 zero:s.natReg 5895=0
 five:s.natReg 5896=5

lemma boot_cursor (M E frontier:ℕ) (s:State) (num:s.natReg 464=M) (dir:s.natReg 4441=E)
 (fresh:s.natReg 5801=frontier):Cursor M E frontier 0 (applyBlock boot s):=by
 constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,num,dir,fresh]
lemma boot_safe {B:ℕ} {s:State} (wb:WordBound B s) (code:20≤B):readable boot s ∧peak boot s≤B:=by
 have a:=wb.2.1 464;have b:=wb.2.1 4441;have c:=wb.2.1 5801
 simp[boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next];omega

lemma row_reads {W E A i:ℕ} {st:UniformSectorPacking.BlockState} {s:State}
 (row:UniformSectorBatchDirectoryMachine.BatchCell W E A i st s):
 s.natHeap (E+i*5)=some st.pairs ∧s.natHeap (E+(i*5+1))=some st.width ∧
 s.natHeap (E+(i*5+2))=some (A+W*st.start):=by
 exact ⟨by simpa only[Nat.mul_comm] using row.1,
  by simpa only[Nat.add_assoc,Nat.mul_comm] using row.2.1,
  by simpa only[Nat.add_assoc,Nat.mul_comm] using row.2.2.1⟩

lemma setup_safe {M E frontier i B W A:ℕ} (st:UniformSectorPacking.BlockState) {s:State}
 (h:Cursor M E frontier i s) (hi:i<M) (directoryFit:E+5*M≤B)
 (row:UniformSectorBatchDirectoryMachine.BatchCell W E A i st s)
 (qBound:st.pairs≤B) (widthBound:st.width≤B) (baseBound:A+W*st.start≤B) (frontierBound:frontier≤B) :
 readable setup s ∧peak setup s≤B:=by
 obtain ⟨r0,r1,r2⟩:=row_reads row
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.index,h.directory,h.five,
  h.one,h.fresh,h.zero,r0,r1,r2,Nat.add_assoc]
 have mul:5*i+5≤5*M:=by omega
 omega

lemma setup_header {M E frontier i W A:ℕ} (st:UniformSectorPacking.BlockState) {s:State}
 (h:Cursor M E frontier i s)
 (row:UniformSectorBatchDirectoryMachine.BatchCell W E A i st s):
 UniformSectorChildEntryPreparation.ChildHeader st.pairs (A+W*st.start) st.width frontier (applyBlock setup s) ∧
 (applyBlock setup s).natReg 4151=0:=by
 obtain ⟨r0,r1,r2⟩:=row_reads row
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.index,h.directory,h.five,h.one,h.fresh,h.zero,
    r0,r1,r2,Nat.add_assoc]
 · simp[setup,applyBlock,Op.apply,writeNat,next]
lemma setup_heaps (s:State):(applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧(applyBlock setup s).scalarReg=s.scalarReg ∧
 (applyBlock setup s).outputs=s.outputs ∧(applyBlock setup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Actual charged9-op generated child ABI and root-depth installation in the
literal loop containing the genuine saving program at a single static site.
No theorem here assumes or claims completed common-C child execution. -/
theorem setup_execution {M E frontier i B W A n:ℕ} (st:UniformSectorPacking.BlockState) (x:Fin n→ℂ) (s:State)
 (h:Cursor M E frontier i s) (hi:i<M) (directoryFit:E+5*M≤B)
 (row:UniformSectorBatchDirectoryMachine.BatchCell W E A i st s)
 (qBound:st.pairs≤B) (widthBound:st.width≤B) (baseBound:A+W*st.start≤B) (frontierBound:frontier≤B)
 (programFit:program.length≤B) (pc:s.pc=8) (wb:WordBound B s):
 BoundedRuns program n x B s 9 (applyBlock setup s) ∧
 UniformSectorChildEntryPreparation.ChildHeader st.pairs (A+W*st.start) st.width frontier (applyBlock setup s) ∧
 (applyBlock setup s).natReg 4151=0:=by
 have safe:=setup_safe st h hi directoryFit row qBound widthBound baseBound frontierBound
 have size:17≤B:=by have:=programFit;rw[program_length] at this;omega
 have run:=block_runs setup program 8 n B x s (setup_code _) pc wb
  (by rw[setup_length];omega) safe.1 safe.2
 exact ⟨by simpa only[setup_length] using run,setup_header st h row⟩

/- Remaining operational obligation: derive each root C execution, its honest
cost and outside-bank/frame postcondition from the genuine recursive theorem;
compose it with the exact increment/jump and whole finite sector induction.
Then actual41 inverse transpose and true inverse packing return native order.
This is an OPEN obligation, not an axiom or a child callback premise. -/
end
end ExactFourierCircuits.UniformSameProgramSectorLoop
