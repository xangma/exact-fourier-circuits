import UniformAxisCacheTransition
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheBoot
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCachePreparationRetention
open UniformTensorMonomialMachine (setPC)

def resetOps:List Op:=[.literal 5921 0]
lemma resetOps_length:resetOps.length=1:=rfl

/-- The horizon accumulator is resetOpsd by a charged instruction before
the real startup loads the first selected radix and both allocation frontiers. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(p:Program)(base finish:ℕ)
 (initCode:BlockAt resetOps p base)
 (startupCode:CodeAt UniformAxisCacheStartupMachine.program p (base+1) finish)
 (codeBound:base+18≤A.envelope c n)(finishBound:finish≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(core:Core n x s)(slab:s.natReg 6020=A.slab c n)
 (pc:s.pc=base)(wb:WordBound (A.envelope c n) s):
 ∃u,BoundedRuns p n x (A.envelope c n) s 18 u∧u.pc=finish∧
 Selected c n 0 u∧Core n x u∧u.natReg 5921=0∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.scalarReg=s.scalarReg∧
 u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀q,q≠5921→q∉UniformAxisCacheStartupMachine.changed→u.natReg q=s.natReg q):=by
 have reset:=block_runs resetOps p base n (A.envelope c n) x s initCode pc wb
  (by rw [resetOps_length];omega) (by simp [resetOps,readable,Op.readable])
  (by simp [resetOps,peak,Op.peak])
 let a:=applyBlock resetOps s
 have ap:a.pc=base+1:=by simp [a,resetOps,applyBlock,Op.apply,writeNat,next,pc]
 have acore:Core n x a:=transport c n 0 hn x s a core ⟨rfl,rfl,rfl,rfl⟩
  (fun _ _=>rfl) (fun q hq=>by
   simp [a,resetOps,applyBlock,Op.apply,writeNat,next,show q≠5921 by omega])
 have aslab:a.natReg 6020=A.slab c n:=by
  simpa [a,resetOps,applyBlock,Op.apply,writeNat,next] using slab
 let start:=setPC a 0
 have bw:WordBound (A.envelope c n) start:=⟨by simp [start,setPC],reset.final_bound.2⟩
 obtain ⟨b,run,bp,control,frontiers,radix,source,index,frame⟩:=
  UniformAxisCacheStartupMachine.execution c n hn x start acore.header.withPC aslab acore.seed.withPC rfl bw
 let first:Fin (C.ell n):=⟨0,by change 0<UniformInitialPreparation.ell n+1;omega⟩
 have selected:Selected c n 0 b:=
  ⟨control,frontiers,radix.trans (UniformAllAxisSeedPreparation.radixAt_eq n first).symm,
   by simpa only [Nat.mul_zero,Nat.add_zero] using source,index⟩
 have retained:Core n x b:=transport c n 0 hn x start b acore.withPC
  ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
  (fun q _=>congrFun frame.natHeap q)
  (fun q hq=>frame.natReg q (by
   simp only [UniformAxisCacheStartupMachine.changed,List.mem_cons,List.not_mem_nil,or_false]
   omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed startupCode
  (by rw [UniformAxisCacheStartupMachine.program_length];omega) finishBound run
 have entry:placed (base+1) start=a:=by
  change {a with pc:=base+1}=a
  rw [←ap]
 rw [entry] at placedRun
 refine ⟨setPC b finish,?_,rfl,selected.withPC,retained.withPC,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only [resetOps_length,setPC] using reset.trans placedRun
 · change b.natReg 5921=0
   rw [frame.natReg 5921 (by simp [UniformAxisCacheStartupMachine.changed])]
   simp [start,a,setPC,resetOps,applyBlock,Op.apply,writeNat,next]
 · exact frame.natHeap
 · exact frame.scalarHeap
 · exact frame.scalarReg
 · exact frame.outputs
 · exact frame.roots
 · intro q ne hq
   change b.natReg q=s.natReg q
   rw [frame.natReg q hq]
   simp [start,a,setPC,resetOps,applyBlock,Op.apply,writeNat,next,ne]

end ExactFourierCircuits.UniformAxisCacheBoot
