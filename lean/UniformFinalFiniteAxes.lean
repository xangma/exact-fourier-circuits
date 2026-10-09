import UniformFinalFiniteAxisAdvance

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalFiniteAxes
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformJointAllocation (slab envelope)
open UniformTensorMonomialMachine (setPC applyBlock Op)
open UniformFinalAxisRetention UniformFinalAxisPrinted UniformFinalFiniteAxisState
open scoped BigOperators
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program UniformActualGlobalConstants.constants UniformRecursiveSelfCallMachine.W

lemma reset_self (s:State):setPC s s.pc=s:=by cases s;rfl
lemma printed_pc {n:ℕ}(hn:0<n)(es:Fin (axisCount n)→List UniformGlobalCalendarDispatch.Event)
 (pos:∀i,(Σ _:Fin (UniformGlobalCalendarDispatch.callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 {k pc:ℕ}{s:State}(h:UniformCalendarPrintedPrefix.Printed hn es pos k s):
 UniformCalendarPrintedPrefix.Printed hn es pos k (setPC s pc):=by
 intro i hi
 have a:=h i hi
 exact ⟨a.rows,a.widths,a.permutations,a.directory,a.pool⟩
lemma frame_pc {n:ℕ}{hn:0<n}{s u:State}(h:Frame hn s u)(pc:ℕ):Frame hn s (setPC u pc):=
 ⟨h.natLow,h.natHigh,h.scalarLow,h.scalarHigh,
  fun i=>⟨(h.cache i).nat,(h.cache i).scalar⟩,h.registers,h.outputs,h.roots⟩

lemma axisBoot_kept (s:State)(q:ℕ)(a:q≠5922)(b:q≠5923)(c:q≠5924)(d:q≠5925):
 (applyBlock UniformGlobalClockConductor.axisBoot (setPC s 6)).natReg q=s.natReg q:=by
 simp[UniformGlobalClockConductor.axisBoot,applyBlock,Op.apply,writeNat,next,a,b,c,d,setPC]

lemma axisBoot_frame {n:ℕ}(hn:0<n)(s:State):
 Frame hn s (applyBlock UniformGlobalClockConductor.axisBoot (setPC s 6)):=by
 have heaps:=UniformGlobalClockControl.heap_frame (setPC s 6) UniformGlobalClockConductor.axisBoot (Or.inr (Or.inl rfl))
 exact ⟨fun z _=>congrFun heaps.1 z,fun z _ _=>congrFun heaps.1 z,
  fun z _=>congrFun heaps.2.1 z,fun z _=>congrFun heaps.2.1 z,
  fun i=>⟨fun z _ _=>congrFun heaps.1 z,fun z _ _=>congrFun heaps.2.1 z⟩,
  fun q _ a b c d=>axisBoot_kept s q a b c d,heaps.2.2.2.1,heaps.2.2.2.2⟩

theorem cache {n H seedDirectory g:ℕ}{hn:0<n}{x:Fin n→ℂ}
 {v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar}{s:State}
 (ready:UniformActualClockReady.Ready hn H seedDirectory x g v s)
 (i:Fin (axisCount n)):UniformAxisCacheContents.Contents constants n hn i s:=ready.cache i i.isLt

lemma nat_zero (c:UniformJointAllocation.Constants)(n:ℕ):
 UniformGlobalCalendarArena.natBase c n+UniformFourierAxisWorkspace.natPrefix n 0=UniformGlobalCalendarArena.natBase c n:=by
 simp only[UniformFourierAxisWorkspace.natPrefix,UniformJointCacheAllocation.offsetSum,Finset.range_zero,Finset.sum_empty,Nat.add_zero]
lemma scalar_zero (c:UniformJointAllocation.Constants)(n:ℕ):
 UniformGlobalCalendarArena.scalarBase c n+9*prefixSum n 0=UniformGlobalCalendarArena.scalarBase c n:=by
 simp only[prefixSum,Finset.range_zero,Finset.sum_empty,Nat.mul_zero,Nat.add_zero]

/-- The actual fixed finite axis loop, from its real clock branch through the
actual preparation and dispatch stages, ending at the real kernel entry. -/
theorem execution {n H g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(s:State)
 (ready:UniformActualClockReady.Ready hn H (directoryBase n) x g v s)(unfinished:g<H):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x (envelope constants n) s ticks u∧
 ticks≤(∑k∈Finset.range (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn (cache ready) g k)+6∧
 u.pc=756∧UniformCalendarPrintedPrefix.Printed hn (events hn (cache ready) g) (position hn (cache ready) g) (axisCount n) u∧
 UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC u 5)∧Frame hn s u∧
 (∀q,200≤q→q<210→u.natReg q=s.natReg q)∧
 u.natReg 6819=UniformGlobalCalendarArena.natBase constants n∧
 u.natReg 6821=UniformGlobalCalendarArena.scalarBase constants n:=by
 have code:=UniformActualGlobalClockProgram.code_bound n
 obtain ⟨start,pc,index,directory,natFrontier,scalarFrontier⟩:=UniformActualClockBoundaryExecution.tick_start x s ready.pc
  (by rw[ready.clock,ready.horizon];exact unfinished) ready.one code ready.bound
 let a:=applyBlock UniformGlobalClockConductor.axisBoot (setPC s 6)
 have frame:=axisBoot_frame hn s
 have old:UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC s 5):=by
  rw[←ready.pc,reset_self];exact ready
 have initial:AxisReady (H:=H) (g:=g) hn x v s (cache ready) 0 a:=by
  refine ⟨pc,index,?_,?_,?_,?_,UniformFinalAxisReadyTransport.ready old frame start.final_bound,frame,
   UniformCalendarPrintedPrefix.zero hn _ _ a,?_,?_⟩
  · exact (directory.trans (allocator_slab old).1).trans (Nat.add_zero _).symm
  · exact (natFrontier.trans ready.natArena).trans (nat_zero constants n).symm
  · exact (scalarFrontier.trans ready.scalarArena).trans (scalar_zero constants n).symm
  · intro h;omega
  · intro q lo hi;exact axisBoot_kept s q (by omega) (by omega) (by omega) (by omega)
  · intro h;omega
 obtain ⟨u,ticks,run,cheap,done⟩:=UniformGlobalFiniteClockInduction.axes x
  (AxisReady (H:=H) (g:=g) hn x v s (cache ready)) (UniformFinalFiniteAxisAdvance.axisCost hn (cache ready) g)
  a initial start.final_bound code
  (fun _ _ h=>⟨h.pc,h.index,h.ready.axes⟩)
  (fun k hk u state bound=>UniformFinalFiniteAxisAdvance.execution hn x v s u (cache ready) k hk state bound)
 have positive:0<axisCount n:=by have h:=ready.axisCount;omega
 have final:=done.allocatorFrontiers positive
 refine ⟨setPC u 756,5+ticks,start.trans run,by omega,rfl,printed_pc hn _ _ done.printed,
  done.ready,frame_pc done.retained 756,done.seed,?_,?_⟩
 · exact final.1
 · exact final.2

end
end ExactFourierCircuits.UniformFinalFiniteAxes
