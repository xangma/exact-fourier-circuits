import UniformLocalRectangleWorkspaceHeaders
import UniformJointCacheRowCopy
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestBootstrap
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
namespace H
abbrev program:=UniformLocalRectangleWorkspaceHeaders.program
abbrev Bank:=UniformLocalRectangleWorkspaceHeaders.Bank
end H

/-- The descriptor pointer is read from the real outer cursor. -/
def setup:List Op:=[.literal 6190 0,.literal 53 7,.add 54 6173 6190,.add 55 6400 6190]
def program:Program:=setup.map Op.code++
 UniformNatCopyMachine.program.map (relocate 4 14)++H.program.map (relocate 14 46)++[.halt]
lemma program_length:program.length=47:=by
 simp only [program,List.length_append,List.length_map,UniformNatCopyMachine.program_length,
  UniformLocalRectangleWorkspaceHeaders.program_length,List.length_singleton]
 rfl
attribute [local irreducible] UniformLocalRectangleWorkspaceHeaders.program
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma copy_code:CodeAt UniformNatCopyMachine.program program 4 14:=by
 have eq:program=setup.map Op.code++UniformNatCopyMachine.program.map (relocate 4 14)++
  (H.program.map (relocate 14 46)++[.halt]):=by simp only [program,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code (setup.map Op.code) _ _ 4 14 rfl
lemma header_code:CodeAt H.program program 14 46:=by
 exact UniformChunkRowTableMachine.segment_code
  (setup.map Op.code++UniformNatCopyMachine.program.map (relocate 4 14)) [.halt] _ 14 46
  (by simp only [List.length_append,List.length_map,UniformNatCopyMachine.program_length];rfl)
lemma halt_at:program[46]?=some .halt:=by
 let before:=setup.map Op.code++UniformNatCopyMachine.program.map (relocate 4 14)++H.program.map (relocate 14 46)
 have len:before.length=46:=by
  simp only [before,List.length_append,List.length_map,UniformNatCopyMachine.program_length,
   UniformLocalRectangleWorkspaceHeaders.program_length];rfl
 change (before++[.halt])[46]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
def prepared(s:State):State:=applyBlock setup s
lemma prepared_eq(s:State):prepared s=applyBlock setup s:=rfl
lemma prepared_keeps_any(s:State)(r:ℕ)(zero:r ≠ 6190)(h53:r ≠ 53)(h54:r ≠ 54)(h55:r ≠ 55):
 (prepared s).natReg r=s.natReg r:=by
 apply UniformLocalCacheSlotHeaderMachine.block_keeps
 intro o ho
 simp only [setup,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl
 all_goals simp [Op.code,UniformNewtonTableMachine.KeepsNat];omega
lemma prepared_keeps(s:State)(r:ℕ)(high:4236 ≤ r)(zero:r ≠ 6190):
 (prepared s).natReg r=s.natReg r:=by
 exact prepared_keeps_any s r zero (by omega) (by omega) (by omega)
lemma prepared_safe{B:ℕ}(s:State)(wb:WordBound B s)(small:7 ≤ B):
 readable setup s ∧ peak setup s ≤ B:=by
 constructor
 · simp [setup,readable,Op.readable]
 · have a:=wb.2.1 6173
   have b:=wb.2.1 6400
   simpa [setup,peak,Op.peak,Op.apply,writeNat,next,Nat.add_zero] using
    (show max 0 (max 7 (max (s.natReg 6173) (s.natReg 6400))) ≤ B from
     max_le (by omega) (max_le small (max_le a b)))

/-- Actual47 copies the seven physical request words below the stored forest,
then installs every reused producer argument from the actual workspace bank.
No low-row or initialized producer-header premise is supplied. -/
theorem execution {n B:ℕ}(j:Fin (axisCount n))(D:ℕ)(q:Row)(x:Fin n → ℂ)(s:State)
 (bank:H.Bank n s)(axis:s.natReg 4200=j.val)(pointer:s.natReg 6173=D)
 (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (apart:UniformJointCacheWorkspace.lowRow n+7 ≤ D)(db:D+7 ≤ B)
 (low:UniformJointCacheWorkspace.lowRow n+7 ≤ B)(code:47 ≤ B)
 (pc:s.pc=0)(wb:WordBound B s):∃u,
 BoundedExecution program n x B s 90 u ∧ u.pc=46 ∧
 UniformLocalRectangleBankMachine.RowSource (UniformJointCacheWorkspace.lowRow n) q u ∧
 UniformLocalRectangleBankMachine.RowSource D q u ∧
 UniformLocalRectangleBankMachine.Args j (UniformJointCacheWorkspace.lowRow n)
  (UniformJointCacheWorkspace.original n q) u ∧
 UniformLocalRectangleCoefficientMachine.NextArgs (UniformJointCacheWorkspace.work n)
  (UniformJointCacheWorkspace.conjugate n) u ∧
 UniformLocalDisabledHeightMachine.Args (UniformJointCacheWorkspace.falseRows n)
  (UniformJointCacheWorkspace.falseColors n) (UniformJointCacheWorkspace.falsePalette n)
  (UniformJointCacheWorkspace.falseDirectory n) u ∧
 u.natReg 4230=UniformJointCacheWorkspace.control n ∧
 UniformNatCopyMachine.Outside (UniformJointCacheWorkspace.lowRow n) 7 s.natHeap u ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,4236 ≤ r → r ≠ 6190 → u.natReg r=s.natReg r):=by
 have safe:=prepared_safe s wb (by omega)
 have first:=block_runs setup program 0 n B x s setup_code pc wb (by change 4 ≤ B;omega) safe.1 safe.2
 change BoundedRuns program n x B s 4 (prepared s) at first
 let start:=setPC (prepared s) 0
 have bounds:=changePC_bound B (prepared s) 0 first.final_bound (by omega)
 have ready:UniformLocalRectangleBankMachine.RowSource D q start:=source
 have count:start.natReg 53=7:=by simp [start,setPC,prepared,setup,applyBlock,Op.apply,writeNat,next]
 have src:start.natReg 54=D:=by simp [start,setPC,prepared,setup,applyBlock,Op.apply,writeNat,next,pointer]
 have dest:start.natReg 55=UniformJointCacheWorkspace.lowRow n:=by
  have h:=bank ⟨0,by decide⟩
  simpa [start,setPC,prepared,setup,applyBlock,Op.apply,writeNat,next,UniformJointCacheWorkspace.lowRow] using h
 obtain ⟨a,copy,lowRow,stored,outside,copyFrame,copyNat⟩:=
  UniformJointCacheRowCopy.row_execution x D (UniformJointCacheWorkspace.lowRow n) B q start ready apart db low
   (by omega) rfl count src dest bounds
 have placedCopy:=UniformBoundedAssembly.boundedExecution_placed copy_code
  (by rw [UniformNatCopyMachine.program_length];omega) (by omega) copy
 have eq:placed 4 start=prepared s:=by
  have hp:(prepared s).pc=4:=by rw [prepared,applyBlock_pc,pc];rfl
  exact UniformSeedRankCrossPreparation.placed_zero (prepared s) 4 hp
 rw [eq] at placedCopy
 let headerStart:=setPC a 0
 have hb:=changePC_bound B a 0 copy.final_bound (by omega)
 have headerBank:H.Bank n headerStart:=by
  intro i
  exact (copyNat _ (Or.inr (by omega))).trans
   ((prepared_keeps s _ (by omega) (by omega)).trans (bank i))
 have headerAxis:headerStart.natReg 4200=j.val:=
  (copyNat _ (Or.inr (by omega))).trans
   ((prepared_keeps_any s _ (by omega) (by omega) (by omega) (by omega)).trans axis)
 obtain ⟨last,header,lp,args,nextArgs,falseArgs,slot,nh,sh,sr,outputs,roots,kept⟩:=
  UniformLocalRectangleWorkspaceHeaders.execution j q x headerStart headerBank headerAxis (by omega) rfl hb
 have placedHeader:=UniformBoundedAssembly.boundedExecution_placed header_code
  (by rw [UniformLocalRectangleWorkspaceHeaders.program_length];omega) (by omega) header
 have heq:placed 14 headerStart=setPC a 14:=by cases a;rfl
 rw [heq] at placedHeader
 let u:=setPC last 46
 have stop:BoundedExecution program n x B u 1 u:=.halt placedHeader.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,?_,rfl,?_,?_,args,nextArgs,⟨falseArgs.rows,falseArgs.colors,falseArgs.palette,falseArgs.directory⟩,slot,?_,
  sh.trans copyFrame.1,sr.trans copyFrame.2.1,outputs.trans copyFrame.2.2.1,
  roots.trans copyFrame.2.2.2,?_⟩
 · exact first.executes (placedCopy.executes (placedHeader.executes stop))
 · intro i;exact (congrFun nh _).trans (lowRow i)
 · intro i;exact (congrFun nh _).trans (stored i)
 · intro i hi;exact (congrFun nh i).trans (outside i hi)
 · intro r hr hz
   exact (kept r hr hz).trans ((copyNat r (Or.inr (by omega))).trans (prepared_keeps s r hr hz))

attribute [irreducible] prepared
end
end ExactFourierCircuits.UniformLocalStoredRequestBootstrap
