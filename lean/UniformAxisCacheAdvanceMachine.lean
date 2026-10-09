import UniformAxisCacheStartupExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAdvanceMachine
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
noncomputable section
/-- Executed only after current-axis consumers have finished. The already
computed end addresses become the next frontiers; the next radix is physically loaded. -/
def advance:List Op:=[.binary .add 6801 6819 6900,.binary .add 6802 6821 6900,
 .binary .add 6906 6906 6901]
def program:Program:=advance.map Op.code++select.map Op.code++[.halt]
lemma advance_length:advance.length=3:=rfl
lemma program_length:program.length=9:=rfl
lemma advance_code:BlockAt advance program 0:=by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma select_code:BlockAt select program 3:=by
 intro i hi;change i<5 at hi;interval_cases i <;>rfl
lemma halt_at:program[8]?=some .halt:=rfl

lemma nat_succ (c:A.Constants)(n:ℕ)(j:Fin (C.ell n)):
 C.natStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val+
 UniformJointCacheExtent.natSize (Seed.radix n j)=
 C.natStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) (j.val+1):=by
 rw [UniformJointCacheAllocation.offsetSum_step,UniformAllAxisSeedPreparation.radixAt_eq]
 omega
lemma scalar_succ (c:A.Constants)(n:ℕ)(j:Fin (C.ell n)):
 C.scalarStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val+
 UniformJointCacheExtent.scalarSize (Seed.radix n j)=
 C.scalarStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) (j.val+1):=by
 rw [UniformJointCacheAllocation.offsetSum_step,UniformAllAxisSeedPreparation.radixAt_eq]
 omega

lemma advance_values (c:A.Constants)(n:ℕ)(j:Fin (C.ell n))(s:State)
 (control:Control n j.val s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (C.natStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  (C.scalarStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val) s):
 Control n (j.val+1) (applyBlock advance s) ∧Frontiers c n (j.val+1) (applyBlock advance s):=by
 have natEnd:=result.endNat.trans (UniformJointCacheAllocation.axis_ends _ _ _).1
 have scalarEnd:=result.endScalar.trans (UniformJointCacheAllocation.axis_ends _ _ _).2
 refine ⟨?_,?_,?_⟩
 · constructor <;>simp [advance,applyBlock,Op.apply,evalNat,writeNat,next,control.zero,control.one,
   control.two,control.nine,control.source,control.count,control.index]
 · simpa [advance,applyBlock,Op.apply,evalNat,writeNat,next,control.zero,natEnd] using nat_succ c n j
 · simpa [advance,applyBlock,Op.apply,evalNat,writeNat,next,control.zero,scalarEnd] using scalar_succ c n j

lemma advance_frame (s:State):Frame s (applyBlock advance s):=
 block_frame advance s (by simp [advance,ordinary,changed])
lemma advance_safe (n:ℕ)(j:Fin (C.ell n))(s:State)(control:Control n j.val s)
 (B:ℕ)(wb:WordBound B s):readable advance s ∧peak advance s ≤ B:=by
 have natEnd:=wb.2.1 6819
 have scalarEnd:=wb.2.1 6821
 have count:=wb.2.1 6905
 rw [control.count] at count
 constructor
 · simp [advance,readable,Op.readable,evalNat]
 · simp [advance,peak,Op.peak,Op.apply,evalNat,writeNat,next,control.zero,control.index,control.one]
   omega

/-- The next axis is selected by nine actual instructions, including the halt.
No next frontier or selected radix is supplied. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))(more:j.val+1<C.ell n)
 (x:Fin n→ℂ)(s:State)(control:Control n j.val s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (C.natStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  (C.scalarStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val) s)
 (retained:Seed.Retained n (C.ell n) s)(pc:s.pc=0)(wb:WordBound (A.envelope c n) s):
 ∃u,BoundedExecution program n x (A.envelope c n) s 9 u ∧u.pc=8 ∧
 Control n (j.val+1) u ∧Frontiers c n (j.val+1) u ∧
 u.natReg 6800=Seed.radix n ⟨j.val+1,more⟩ ∧
 u.natReg 6167=Seed.directoryBase n+2*(j.val+1) ∧u.natReg 4200=j.val+1 ∧Frame s u:=by
 have bounds:=arithmetic c n hn
 have safe:=advance_safe n j s control (A.envelope c n) wb
 have first:=block_runs advance program 0 n (A.envelope c n) x s advance_code pc wb
  (by rw [advance_length];omega) safe.1 safe.2
 let a:=applyBlock advance s
 have ap:a.pc=3:=by rw [UniformAxisCacheAllocationMachine.block_pc,pc,advance_length]
 have values:=advance_values c n j s control result
 let next:Fin (C.ell n):=⟨j.val+1,more⟩
 have width:a.natHeap (Seed.directoryBase n+next.val*2+1)=some (Seed.radix n next):=by
  rw [(advance_frame s).natHeap]
  simpa only [Nat.mul_comm] using retained.width next next.isLt
 have lastSafe:=select_safe c n hn next a values.1 width
 have last:=block_runs select program 3 n (A.envelope c n) x a select_code ap first.final_bound
  (by rw [select_length];omega) lastSafe.1 lastSafe.2
 let u:=applyBlock select a
 have up:u.pc=8:=by rw [UniformAxisCacheAllocationMachine.block_pc,ap,select_length]
 have halt:BoundedExecution program n x (A.envelope c n) u 1 u:=.halt last.final_bound
  (by simp only [UniformMachine.step,up,halt_at])
 have out:=select_values_of_width c n next a values.1 values.2 width
 refine ⟨u,?_,up,out.1,out.2.1,out.2.2.1,?_,out.2.2.2.2,(advance_frame s).trans (select_frame a)⟩
 · simpa only [advance_length,select_length] using first.executes (last.executes halt)
 · simpa only [next,Nat.mul_comm] using out.2.2.2.1
end
end ExactFourierCircuits.UniformAxisCacheAdvanceMachine
