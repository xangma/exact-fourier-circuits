import UniformAxisCacheStartupMachine
import UniformAxisCacheAllocationExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheStartupMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
noncomputable section

def changed:List ℕ:=[4200,6167,6800,6801,6802,6900,6901,6902,6903,6904,6905,6906,6907]
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,q∉changed→u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u t:State}(f:Frame s u)(g:Frame u t):Frame s t:=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
  g.outputs.trans f.outputs,g.roots.trans f.roots,fun q h=>(g.natReg q h).trans (f.natReg q h)⟩
def ordinary:Op→Prop
 | .literal d _|.binary _ d _ _|.load d _=>d∈changed
 | .store _ _=>False
lemma op_frame (o:Op)(s:State)(h:ordinary o):Frame s (o.apply s):=by
 cases o with
 | literal d v|binary op d l r|load d a=>
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  have ne:q≠d:=by intro e;subst q;exact hq h
  simp [Op.apply,writeNat,next,ne]
 | store a r=>exact False.elim h
lemma block_frame (os:List Op)(s:State)(h:∀o∈os,ordinary o):Frame s (applyBlock os s):=by
 induction os generalizing s with
 | nil=>exact Frame.refl s
 | cons o os ih=>exact (op_frame o s (h o (by simp))).trans (ih (o.apply s) (fun z hz=>h z (by simp [hz])))
lemma boot_frame (s:State):Frame s (applyBlock boot s):=
 block_frame boot s (by simp [boot,ordinary,changed])
lemma select_frame (s:State):Frame s (applyBlock select s):=
 block_frame select s (by simp [select,ordinary,changed])

lemma arithmetic (c:A.Constants)(n:ℕ)(hn:0<n):
 100 ≤ A.envelope c n ∧C.natStart c n ≤ A.envelope c n ∧
 C.scalarStart c n ≤ A.envelope c n ∧
 Seed.directoryBase n+2*C.ell n ≤ A.envelope c n ∧4*n ≤ A.envelope c n:=by
 have ends:=UniformJointCacheAllocation.ends_bound c n hn
 have positive:=UniformJointAllocation.positive c n
 have fixed:=UniformJointAllocation.fixed_large c
 have source:Seed.directoryBase n+2*C.ell n ≤ (n+2)^19:=(UniformAllAxisSeedPreparation.word_setup hn).2.2
 have pow:n+2 ≤ (n+2)^19:=by
  have h:=Nat.pow_le_pow_right (show 1 ≤ n+2 by omega) (show 1 ≤ 19 by decide)
  simpa only [pow_one] using h
 have coefficient:4 ≤ 100000*(UniformJointAllocation.fixed c+1):=by omega
 have four:4*(n+2) ≤ A.slab c n:=
  (Nat.mul_le_mul_right _ coefficient).trans (Nat.mul_le_mul_left _ pow)
 have power:(n+2)^19 ≤ A.slab c n:=by
  have coeff:1 ≤ 100000*(UniformJointAllocation.fixed c+1):=by omega
  simpa only [Nat.one_mul,A.slab] using Nat.mul_le_mul_right ((n+2)^19) coeff
 unfold UniformJointCacheAllocation.natEnd UniformJointCacheAllocation.scalarEnd at ends
 unfold A.envelope
 change 100 ≤ _ ∧UniformJointCacheAllocation.natStart c n ≤ _ ∧
  UniformJointCacheAllocation.scalarStart c n ≤ _ ∧_ ≤ _ ∧_ ≤ _
 omega

lemma boot_safe (c:A.Constants)(n:ℕ)(hn:0<n)(s:State)
 (seed:Seed.Header n (C.ell n) s)(slab:s.natReg 6020=A.slab c n)
 (wb:WordBound (A.envelope c n) s):
 readable boot s ∧peak boot s ≤ A.envelope c n:=by
 have bounds:=arithmetic c n hn
 have source:=wb.2.1 204
 have count:=wb.2.1 202
 rw [seed.directory] at source
 rw [seed.count] at count
 have index:UniformInitialPreparation.ell n < A.envelope c n:=by
  change UniformInitialPreparation.ell n+1 ≤ A.envelope c n at count
  omega
 have natBound:=bounds.2.1
 have scalarBound:=bounds.2.2.1
 change A.slab c n+2*Seed.axisCount n ≤ A.envelope c n at natBound
 change A.slab c n+9*Seed.prefixSum n (C.ell n) ≤ A.envelope c n at scalarBound
 constructor
 · simp [boot,readable,Op.readable,evalNat]
 · simp [boot,peak,Op.peak,Op.apply,evalNat,writeNat,next,seed.count,seed.offset,seed.directory,slab,Nat.mul_comm]
   have small:=bounds.1
   omega

lemma select_safe (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))(s:State)
 (control:Control n j.val s)
 (width:s.natHeap (Seed.directoryBase n+j.val*2+1)=some (Seed.radix n j)):
 readable select s ∧peak select s ≤ A.envelope c n:=by
 have bounds:=arithmetic c n hn
 have dir:=bounds.2.2.2.1
 have rad:Seed.radix n j ≤ A.envelope c n:=
  (UniformGlobalLocalPreparation.radix_le_length n j).trans
   ((UniformWorkingLength.workingLength_upper hn).le.trans bounds.2.2.2.2)
 have src:Seed.directoryBase n+j.val*2+1 ≤ A.envelope c n:=by omega
 constructor
 · simp [select,readable,Op.readable,Op.apply,evalNat,writeNat,next,
   control.index,control.two,control.source,control.one,width]
 · simp [select,peak,Op.peak,Op.apply,evalNat,writeNat,next,
   control.index,control.two,control.source,control.one,control.zero,width]
   omega

/-- A literal17-cell bootstrap: actual ordinary allocator/seed outputs become
current frontier addresses and the first radix is loaded from the produced directory. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(x:Fin n→ℂ)(s:State)
 (seed:Seed.Header n (C.ell n) s)(slab:s.natReg 6020=A.slab c n)
 (retained:Seed.Retained n (C.ell n) s)(pc:s.pc=0)(wb:WordBound (A.envelope c n) s):
 ∃u,BoundedExecution program n x (A.envelope c n) s 17 u ∧u.pc=16 ∧
 Control n 0 u ∧Frontiers c n 0 u ∧
 u.natReg 6800=Seed.radix n ⟨0,by change 0<UniformInitialPreparation.ell n+1;omega⟩ ∧
 u.natReg 6167=Seed.directoryBase n ∧u.natReg 4200=0 ∧Frame s u:=by
 have bounds:=arithmetic c n hn
 have firstSafe:=boot_safe c n hn s seed slab wb
 have first:=block_runs boot program 0 n (A.envelope c n) x s boot_code pc wb
  (by rw [boot_length];omega) firstSafe.1 firstSafe.2
 let a:=applyBlock boot s
 have ap:a.pc=11:=by rw [UniformAxisCacheAllocationMachine.block_pc,pc,boot_length]
 have values:=boot_values c n s seed slab
 let j:Fin (C.ell n):=⟨0,by change 0<UniformInitialPreparation.ell n+1;omega⟩
 have width:a.natHeap (Seed.directoryBase n+j.val*2+1)=some (Seed.radix n j):=by
  rw [(boot_frame s).natHeap]
  simpa only [Nat.mul_comm] using retained.width j j.isLt
 have lastSafe:=select_safe c n hn j a values.1 width
 have last:=block_runs select program 11 n (A.envelope c n) x a select_code ap first.final_bound
  (by rw [select_length];omega) lastSafe.1 lastSafe.2
 let u:=applyBlock select a
 have up:u.pc=16:=by rw [UniformAxisCacheAllocationMachine.block_pc,ap,select_length]
 have halt:BoundedExecution program n x (A.envelope c n) u 1 u:=.halt last.final_bound
  (by simp only [UniformMachine.step,up,halt_at])
 have out:=select_values_of_width c n j a values.1 values.2 width
 refine ⟨u,?_,up,out.1,out.2.1,out.2.2.1,?_,out.2.2.2.2,(boot_frame s).trans (select_frame a)⟩
 · simpa only [boot_length,select_length] using first.executes (last.executes halt)
 · simpa only [j,Nat.mul_zero,Nat.add_zero] using out.2.2.2.1
end
end ExactFourierCircuits.UniformAxisCacheStartupMachine
