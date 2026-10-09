import UniformLocalStoredRectanglePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestAdvanceMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine

/-- Copy measured end cursors, never recompute the slot count on the host. -/
def copies:List (ℕ×ℕ):=[(6160,6128),(6162,6133),(6163,6134),(6164,6135),(6165,6136),(6166,6137)]
def boot:List Op:=[.literal 6190 0,.literal 6191 1,.literal 6193 7]
def tail:List Op:=[.add 6173 6173 6193,.add 6174 6174 6191,.add 6161 6161 6191]
def operations:List Op:=boot++copyOps copies++tail
def program:Program:=operations.map Op.code++[.halt]
lemma operations_length:operations.length=12:=rfl
lemma program_length:program.length=13:=rfl
lemma block_code:BlockAt operations program 0:=by intro i hi;change i<12 at hi;interval_cases i <;>rfl
lemma halt_at:program[12]?=some .halt:=rfl
lemma safe:UniformLocalCacheContextCopies.Safe copies:=by
 have h:(copies.all fun p=>p.1!=6190 && copies.all fun q=>p.1!=q.2)=true:=by decide
 intro p hp
 have a:p.1 ≠ 6190 ∧ (copies.all fun q=>p.1!=q.2)=true:=by simpa [and_assoc] using List.all_eq_true.mp h p hp
 exact ⟨a.1,fun q hq=>by simpa [and_assoc] using List.all_eq_true.mp a.2 q hq⟩
lemma nodup:(copies.map Prod.fst).Nodup:=by decide

noncomputable section
def copied(s:State):State:=applyBlock (copyOps copies) (applyBlock boot s)
lemma copied_eq(s:State):copied s=applyBlock (copyOps copies) (applyBlock boot s):=rfl
lemma copied_nat(s:State):(copied s).natReg=copyEnv copies s.natReg (applyBlock boot s).natReg:=by
 apply UniformLocalCacheContextCopies.copy_nat copies s.natReg (applyBlock boot s)
 · intro p hp
   have h:(copies.all fun p=>p.2!=6190 && p.2!=6191 && p.2!=6193)=true:=by decide
   have a:p.2 ≠ 6190 ∧ p.2 ≠ 6191 ∧ p.2 ≠ 6193:=by simpa [and_assoc] using List.all_eq_true.mp h p hp
   simp [boot,applyBlock,Op.apply,writeNat,next,a.1,a.2.1,a.2.2]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · exact safe
lemma copied_output(s:State)(d r:ℕ)(mem:(d,r)∈copies):(copied s).natReg d=s.natReg r:=by
 rw [copied_nat,copy_env_output copies _ _ nodup d r mem]
lemma copied_keep(s:State)(q:ℕ)(keep:∀p∈copies,p.1 ≠ q)(a:q ≠ 6190)(b:q ≠ 6191)(c:q ≠ 6193):
 (copied s).natReg q=s.natReg q:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ q keep]
 simp [boot,applyBlock,Op.apply,writeNat,next,a,b,c]
lemma copied_one(s:State):(copied s).natReg 6191=1:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ 6191 (by decide)]
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma copied_seven(s:State):(copied s).natReg 6193=7:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ 6193 (by decide)]
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma copied_heap(s:State):(copied s).natHeap=s.natHeap ∧ (copied s).scalarHeap=s.scalarHeap ∧
 (copied s).scalarReg=s.scalarReg ∧ (copied s).outputs=s.outputs ∧ (copied s).rootOrders=s.rootOrders:=
 UniformLocalCacheContextCopies.copy_heaps copies (applyBlock boot s)
def advanced(s:State):State:=applyBlock tail (copied s)
lemma advanced_eq(s:State):advanced s=applyBlock operations s:=by
 rw [operations,applyBlock_append,applyBlock_append];rfl
lemma tail_keeps(s:State)(r:ℕ)(a:r ≠ 6173)(b:r ≠ 6174)(c:r ≠ 6161):
 (advanced s).natReg r=(copied s).natReg r:=by
 apply block_keeps
 intro o ho
 simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl
 all_goals simp [Op.code,UniformNewtonTableMachine.KeepsNat];omega
lemma advanced_output(s:State)(d r:ℕ)(mem:(d,r)∈copies):(advanced s).natReg d=s.natReg r:=by
 have h:(copies.all fun p=>p.1!=6173 && p.1!=6174 && p.1!=6161)=true:=by decide
 have a:d ≠ 6173 ∧ d ≠ 6174 ∧ d ≠ 6161:=by simpa [and_assoc] using List.all_eq_true.mp h (d,r) mem
 rw [tail_keeps s d a.1 a.2.1 a.2.2,copied_output s d r mem]
lemma copied_outer(s:State)(q:ℕ)(h:q=6173 ∨ q=6174 ∨ q=6161):(copied s).natReg q=s.natReg q:=by
 apply copied_keep s q _ (by rcases h with rfl|rfl|rfl <;>omega)
  (by rcases h with rfl|rfl|rfl <;>omega) (by rcases h with rfl|rfl|rfl <;>omega)
 intro p hp
 have tested:(copies.all fun p=>p.1!=6173 && p.1!=6174 && p.1!=6161)=true:=by decide
 have a:p.1 ≠ 6173 ∧ p.1 ≠ 6174 ∧ p.1 ≠ 6161:=by simpa [and_assoc] using List.all_eq_true.mp tested p hp
 rcases h with rfl|rfl|rfl <;>omega
lemma advanced_outer(s:State):
 (advanced s).natReg 6173=s.natReg 6173+7 ∧
 (advanced s).natReg 6174=s.natReg 6174+1 ∧
 (advanced s).natReg 6161=s.natReg 6161+1:=by
 simp [advanced,tail,applyBlock,Op.apply,writeNat,next,copied_one,copied_seven,
  copied_outer s 6173 (Or.inl rfl),copied_outer s 6174 (Or.inr (Or.inl rfl)),
  copied_outer s 6161 (Or.inr (Or.inr rfl))]
lemma safe_operations{B:ℕ}(s:State)(wb:WordBound B s)(small:7 ≤ B)
 (pointer:s.natReg 6173+7 ≤ B)(index:s.natReg 6174+1 ≤ B)(time:s.natReg 6161+1 ≤ B):
 readable operations s ∧ peak operations s ≤ B:=by
 have sources:UniformLocalCacheContextCopies.Sources copies s.natReg (applyBlock boot s):=by
  intro p hp
  have h:(copies.all fun p=>p.2!=6190 && p.2!=6191 && p.2!=6193)=true:=by decide
  have a:p.2 ≠ 6190 ∧ p.2 ≠ 6191 ∧ p.2 ≠ 6193:=by simpa [and_assoc] using List.all_eq_true.mp h p hp
  simp [boot,applyBlock,Op.apply,writeNat,next,a.1,a.2.1,a.2.2]
 have zero:(applyBlock boot s).natReg 6190=0:=by simp [boot,applyBlock,Op.apply,writeNat,next]
 have middle:=UniformLocalCacheContextCopies.copy_safe copies s.natReg _ B sources zero safe
  (fun p _=>wb.2.1 p.2)
 have last:readable tail (copied s) ∧ peak tail (copied s) ≤ B:=by
  constructor
  · simp [tail,readable,Op.readable]
  · simpa [tail,peak,Op.peak,Op.apply,writeNat,next,copied_one,copied_seven,
     copied_outer s 6173 (Or.inl rfl),copied_outer s 6174 (Or.inr (Or.inl rfl)),
     copied_outer s 6161 (Or.inr (Or.inr rfl))] using
     (max_le pointer (max_le index (max_le time (Nat.zero_le B))))
 rw [operations,UniformLocalCacheContextMachine.readable_append,UniformLocalCacheContextMachine.peak_append,
  UniformLocalCacheContextMachine.readable_append,UniformLocalCacheContextMachine.peak_append]
 exact ⟨⟨⟨by simp [boot,readable,Op.readable],middle.1⟩,last.1⟩,
  max_le (max_le (by simpa [boot,peak,Op.peak] using small) middle.2) last.2⟩

/-- Actual13 charges every measured-cursor copy and every outer index/address
increment. Heap values and actual dependency tags are untouched. -/
theorem execution {n B:ℕ}(x:Fin n → ℂ)(s:State)(code:13 ≤ B)(pc:s.pc=0)(wb:WordBound B s)
 (pointer:s.natReg 6173+7 ≤ B)(index:s.natReg 6174+1 ≤ B)(time:s.natReg 6161+1 ≤ B):
 ∃u,BoundedExecution program n x B s 13 u ∧ u.pc=12 ∧
 (∀p∈copies,u.natReg p.1=s.natReg p.2) ∧
 u.natReg 6173=s.natReg 6173+7 ∧ u.natReg 6174=s.natReg 6174+1 ∧ u.natReg 6161=s.natReg 6161+1 ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders:=by
 have safe:=safe_operations s wb (by omega) pointer index time
 have first:=block_runs operations program 0 n B x s block_code pc wb
  (by rw [operations_length];omega) safe.1 safe.2
 rw [←advanced_eq] at first
 have hp:(advanced s).pc=12:=by rw [advanced_eq,applyBlock_pc,operations_length,pc]
 have stop:BoundedExecution program n x B (advanced s) 1 (advanced s):=.halt first.final_bound
  (by simp [step,hp,halt_at])
 obtain ⟨p,i,t⟩:=advanced_outer s
 obtain ⟨nh,sh,sr,out,roots⟩:=copied_heap s
 refine ⟨advanced s,?_,hp,fun p hp=>advanced_output s p.1 p.2 hp,p,i,t,nh,sh,sr,out,roots⟩
 simpa only [operations_length] using first.executes stop

attribute [irreducible] copied advanced
end
end ExactFourierCircuits.UniformLocalRequestAdvanceMachine
