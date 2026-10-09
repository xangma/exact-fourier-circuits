import UniformGlobalCalendarDispatchTables
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatchOutside
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs)
open UniformGlobalCalendarDispatch
noncomputable section

lemma writeRows_high (O used:ℕ) (records:ℕ→ℕ×ℕ) (j fuel:ℕ)
 (heap:ℕ→Option ℕ) (z:ℕ) (above:O+3*(used+j+fuel)≤z):
 UniformGlobalCalendarUnionRows.writeRows O used records j fuel heap z=heap z:=by
 induction fuel generalizing j heap with
 | zero=>rfl
 | succ fuel ih=>
   rw[UniformGlobalCalendarUnionRows.writeRows,ih _ _ (by omega)]
   simp (disch:=omega) [UniformGlobalCalendarUnionRows.storeRow]

lemma foldRows_high (r T used:ℕ) (es:List Event) (heap:ℕ→Option ℕ) (z:ℕ)
 (above:T+3*(used+callTotal r es)≤z):foldRows r T used es heap z=heap z:=by
 induction es generalizing used heap with
 | nil=>rfl
 | cons e es ih=>
   rw[foldRows,ih (used+callCount r e) _ (by rw[callTotal_cons] at above;omega)]
   cases phase:e.phase with
   | diagonal lane=>simp only[rowAction]
   | kernel=>
     apply writeRows_high
     have count:callCount r e=r-e.descriptor.widthCount:=by simp[callCount,phaseCalls,phase]
     rw[callTotal_cons,count] at above
     omega

lemma foldRows_outside (r T:ℕ) (es:List Event) (heap:ℕ→Option ℕ) (z:ℕ)
 (outside:z<T ∨T+3*callTotal r es≤z):foldRows r T 0 es heap z=heap z:=by
 rcases outside with below|above
 · exact foldRows_before r T 0 es heap z (by omega)
 · exact foldRows_high r T 0 es heap z (by omega)

/-- The literal281 dispatcher prints its own real phase directory and prepares
all9r fresh factor cells. Both helpers are charged inside this very program. -/
theorem boot_execution_outside {n A N r O T phaseBank B : ℕ} (x : Fin n→ℂ) (s : State)
 (h : Inputs A N r O T phaseBank s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 281 ≤ B) (phaseFit : phaseBank+56 ≤ B) (poolFit : O+9*r ≤ B) :
 ∃u, BoundedRuns program n x B s (45*r+189) u ∧ u.pc=10 ∧
 Header A N r O T 0 phaseBank 0 u ∧
 UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words u ∧
 UniformGlobalScalePoolMachine.Prefix O (9*r) u ∧
 (∀z,z<phaseBank ∨phaseBank+56 ≤ z → u.natHeap z=s.natHeap z) ∧
 (∀z,z<O ∨ O+9*r ≤ z → u.scalarHeap z=s.scalarHeap z) ∧
 u.rootOrders=s.rootOrders ∧u.outputs=s.outputs := by
 let b:=applyBlock boot s
 have bh : Header A N r O T 0 phaseBank 0 b:=boot_header h
 have br : BoundedRuns program n x B s 6 b:=block_runs boot program 0 n B x s boot_code pc wb
  (by change 6 ≤ B;omega)
  (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.phaseBankReg];omega)
 have bp : b.pc=6:=by rw [applyBlock_pc,pc];rfl
 have j1 : step program n x b=.running {b with pc:=52}:=by simp [step,bp,code_6]
 have phs : WordBound B {b with pc:=0}:=changePC_bound B b 0 br.final_bound (by omega)
 obtain ⟨p,pr,printed,ph,frames,_ptr⟩:=UniformGlobalCalendarPhaseDirectory.execution phaseBank B n x
  {b with pc:=0} (by simp [b,boot,applyBlock,Op.apply,writeNat,next,h.phaseBankReg]) rfl phs phaseFit (by omega)
 have placedP:=UniformBoundedAssembly.boundedExecution_placed phasePrinter_code
  (by rw [phasePrinter_length];omega) (by omega) pr
 change BoundedRuns program n x B {b with pc:=52} 172 {p with pc:=7} at placedP
 have first : BoundedRuns program n x B s 179 {p with pc:=7}:=
  br.trans (.next br.final_bound j1 placedP)
 have hp : Header A N r O T 0 phaseBank 0 p:=bh.transfer (by
  intro z lo hi;exact frames.natReg z (by omega) (by omega) (by omega) (by omega))
 let ready:=applyBlock initSetup {p with pc:=7}
 have setup : BoundedRuns program n x B {p with pc:=7} 2 ready:=block_runs initSetup program 7 n B x
  {p with pc:=7} initSetup_code rfl first.final_bound (by change 9 ≤ B;omega)
  (by simp [initSetup,readable,Op.readable])
  (by simp [initSetup,peak,Op.peak,Op.apply,writeNat,next,hp.pool,hp.radix,hp.one];omega)
 have rh : Header A N r O T 0 phaseBank 0 ready:=hp.transfer (by
  intro z lo hi;simp (disch := omega) [ready,initSetup,applyBlock,Op.apply,writeNat,next])
 have rp : ready.pc=9:=by rw [applyBlock_pc];rfl
 have j2 : step program n x ready=.running {ready with pc:=224}:=by simp [step,rp,code_9]
 have ihs : WordBound B {ready with pc:=0}:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨u,ir,_ip,pool,sf,ff⟩:=UniformGlobalScalePoolMachine.execution O r n B x {ready with pc:=0}
  (by simp [ready,initSetup,applyBlock,Op.apply,writeNat,next,hp.pool,hp.one])
  (by simp [ready,initSetup,applyBlock,Op.apply,writeNat,next,hp.radix,hp.one]) poolFit (by omega) rfl ihs
 have placedI:=UniformBoundedAssembly.boundedExecution_placed init_code
  (by rw [UniformGlobalScalePoolMachine.program_length];omega) (by omega) ir
 change BoundedRuns program n x B {ready with pc:=224} (45*r+7) {u with pc:=10} at placedI
 have last:=setup.trans (.next setup.final_bound j2 placedI)
 have uh : Header A N r O T 0 phaseBank 0 {u with pc:=10}:=rh.transfer (by
  intro z lo hi;exact ff.natReg z (by omega) (by omega) (by omega) (by omega))
 refine ⟨{u with pc:=10},?_,rfl,uh,?_,pool,?_,?_,?_,?_⟩
 · convert first.trans last using 1;omega
 · intro j hj
   exact (congrFun ff.natHeap _).trans (printed j hj)
 · intro z hz
   exact (congrFun ff.natHeap z).trans ((ph z hz).trans rfl)
 · intro z outside
   exact (sf z outside).trans ((congrFun frames.scalarHeap z).trans rfl)
 · exact ff.roots.trans (frames.roots.trans rfl)
 · exact ff.outputs.trans (frames.outputs.trans rfl)


/-- Whole literal281 execution from dirty work memory. It prints the real
phase directory, initializes all9r scalar cells and folds every selected
physical cache entry; the final negative branch and halt are included. -/
theorem execution_outside {n A N r O T phaseBank B : ℕ} (x : Fin n→ℂ) (s : State)
 (es : List Event) (h : Inputs A N r O T phaseBank s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 281 ≤ B) (count : es.length=N) (selection : Selections A 0 es s)
 (cached : ∀e∈es,CachedEvent r O phaseBank B e s)
 (selectionFit : A+2*N ≤ phaseBank) (phaseFit : phaseBank+56 ≤ T)
 (poolFit : O+9*r ≤ B) (rowFit : T+3*callTotal r es ≤ B) :
 ∃b u time, BoundedRuns program n x B s (45*r+189) b∧
 BoundedExecution program n x B s time u∧time ≤ 45*r+191+es.length*(9*r+48)∧u.pc=51∧
 Header A N r O T (callTotal r es) phaseBank N u∧
 UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words u∧
 (∀lane:Fin 9,∀i:Fin r,u.scalarHeap (O+lane.val*r+i.val)=some (UniformPairMachine.prepared
  (if lane.val=0 then foldValues es (fun _=>1) i.val else 1)))∧
 u.natHeap=foldRows r T 0 es b.natHeap∧
 (∀z,(z<phaseBank∨phaseBank+56≤z)→(z<T∨T+3*callTotal r es≤z)→u.natHeap z=s.natHeap z)∧
 (∀z,z<phaseBank→u.natHeap z=s.natHeap z)∧
 (∀z,z<O∨O+9*r ≤ z→u.scalarHeap z=s.scalarHeap z)∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 have tb : T ≤ B:=by omega
 obtain ⟨b,boot,bp,bh,decoder,pool,nf,sf,roots,outputs⟩:=boot_execution_outside x s h pc wb code (by omega) poolFit
 have natLow:∀z,z<phaseBank→b.natHeap z=s.natHeap z:=fun z hz=>nf z (Or.inl hz)
 have all : ∀e∈es,CachedEvent r O T B e b:=by
  intro e member
  exact ((cached e member).transfer natLow (fun z hz=>sf z (Or.inl hz))).widen (by omega)
 have selected : Selections A 0 es b:=Selections.transfer 0 selection (by omega) selectionFit natLow
 have target : UniformGlobalCalendarFactorMerge.Factors O r (fun _=>1) b.scalarHeap:=by
  intro i hi;exact pool i (by omega)
 obtain ⟨u,time,loop,cap,up,uh,out,heap,natFrame,scalarFrame,ur,uo⟩:=loop_execution x b es (fun _=>1) bh bp boot.final_bound code
  (by omega) selected all (by omega) phaseFit decoder target poolFit (by simpa only [Nat.zero_add] using rowFit)
 refine ⟨b,u,(45*r+189)+time,boot,boot.executes loop,by omega,up,(by simpa only [Nat.zero_add] using uh),?_,?_,heap,?_,?_,?_,ur.trans roots,uo.trans outputs⟩
 · exact printed_transfer decoder phaseFit natFrame
 · intro lane i
   by_cases zero : lane.val=0
   · simpa [zero] using out i.val i.isLt
   · rw [ite_eq_right zero,scalarFrame _ (Or.inr ?_)]
     simpa only [Nat.add_assoc] using pool (lane.val*r+i.val) (by
      have mul : lane.val*r ≤ 8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
      have:=i.isLt;omega)
     have mul : r ≤ lane.val*r:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right r (by omega : 1 ≤ lane.val)
     omega
 · intro z phaseOutside rowOutside
   rw[heap,foldRows_outside r T es b.natHeap z rowOutside]
   exact nf z phaseOutside
 · intro z below;exact (natFrame z (by omega)).trans (natLow z below)
 · intro z outside
   exact (scalarFrame z (by rcases outside with lo|hi;exact Or.inl lo;exact Or.inr (by omega))).trans (sf z outside)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatchOutside
