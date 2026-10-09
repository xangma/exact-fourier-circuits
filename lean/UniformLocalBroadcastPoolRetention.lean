import UniformLocalBroadcastPoolMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLocalBroadcastPoolMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformLocalCacheChronology

noncomputable section

/-- High-address retention for the actual broadcast preparation. The extra
frame follows the three real producer write ranges; it changes no bytecode. -/
theorem borrowed_stage_high {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot)
 (x:Fin n→ℂ) (s:State) (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (fit:g+q.e+q.a ≤ q.width) (sourceEnd:q.j0+q.e ≤ q.width) (targetEnd:q.i0+q.a ≤ q.width)
 (width:q.width ≤ B) (borrowedEnd:Q+g ≤ B) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B)
 (code:241 ≤ B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedRuns program n x B s ticks u ∧ ticks ≤ 11*q.width+28 ∧ u.pc=38 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) u ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ (∀i,Q+g ≤ i→u.natHeap i=s.natHeap i) ∧
 u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 obtain ⟨a,first,ap,ab,aa,aheap,ascalar,aout,aroot⟩:=
  boot_stage D I Q T E pool mu bar C Z P V r g B q slot x s args source record
   fit sourceEnd targetEnd width borrowedEnd rowEnd slotEnd code pc bound
 let ae:=setPC a 0
 have aw:=changePC_bound B a 0 first.final_bound (by omega)
 have bh:UniformBorrowedCoordinateMachine.Headers q.j0 q.e q.i0 q.a g Q ae:=
  ⟨ab.source,ab.inputs,ab.target,ab.outputs,ab.gates,ab.borrowed⟩
 obtain ⟨bt,b,borrowed,bcheap,bpc,bcount,filled,bframe,boutside⟩:=
  UniformBorrowedCoordinateMachine.execution n x q.width q.j0 q.e q.i0 q.a g Q B ae
   bh rfl aw (by omega) width (sourceEnd.trans width) (targetEnd.trans width) borrowedEnd fit
 have placedBorrowed:=UniformBoundedAssembly.boundedExecution_placed borrowed_code
  (by rw [UniformBorrowedCoordinateMachine.program_length];omega) (by omega) borrowed
 rw [UniformSeedRankCrossPreparation.placed_zero a 21 ap] at placedBorrowed

 let u:=setPC b 38
 have physical:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) u:=by
  intro j hj
  change b.natHeap (Q+j)=some (borrowedValue q g fit j)
  rw [borrowedValue,dite_eq_left hj]
  have jl:j<(UniformBorrowedCoordinateMachine.borrowed q.width q.j0 q.e q.i0 q.a g).length:=by
   rw [UniformBorrowedCoordinateMachine.borrowed_length _ _ _ _ _ _ fit];exact hj
  change b.natHeap (Q+j)=some ((UniformBorrowedCoordinateMachine.borrowed q.width q.j0 q.e q.i0 q.a g)[j]'jl)
  exact filled j jl
 refine ⟨u,21+bt,?_,by omega,rfl,((borrowed_stable bframe).booted ab.withPC).withPC,
  ((borrowed_stable bframe).args aa.withPC).withPC,physical,?_,?_,bframe.1.trans ascalar,?_,?_⟩
 · simpa only [boot_length,u,setPC] using first.trans placedBorrowed
 · intro i hi;exact (boutside i (Or.inl hi)).trans (congrFun aheap i)
 · intro i hi;exact (boutside i (Or.inr hi)).trans (congrFun aheap i)
 · exact bframe.2.2.1.trans aout
 · exact bframe.2.2.2.1.trans aroot

theorem broadcast_stage_high {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot)
 (x:Fin n→ℂ) (s:State) (args:Args D I Q T E pool mu bar C Z P V r g s)
 (booted:Booted q slot g Q s) (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g)
 (physical:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) s)
 (borrowedEnd:Q+g ≤ T) (rawEnd:T+3*q.a ≤ B) (targetEnd:q.i0+q.a ≤ B)
 (cap:P+1 ≤ B) (code:241 ≤ B) (pc:s.pc=38) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (14*count q slot+14) u ∧ u.pc=65 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) u ∧ u.natReg 894=count q slot ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ (∀i,T+3*q.a ≤ i→u.natHeap i=s.natHeap i) ∧
 u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have safe:=broadcastSetup_safe s booted args.constants bound cap
 have setBroadcast:=block_runs broadcastSetup program 38 n B x s broadcastSetup_code pc
  bound (by rw [broadcastSetup_length];omega) safe.1 safe.2
 let c:=applyBlock broadcastSetup s
 have cp:c.pc=45:=by rw [applyBlock_pc,pc,broadcastSetup_length]
 have cb:Booted q slot g Q c:=(broadcastSetup_stable s).booted booted
 have ca:Args D I Q T E pool mu bar C Z P V r g c:=(broadcastSetup_stable s).args args
 have cnh: c.natHeap=s.natHeap:=(setup_heap broadcastSetup (by simp) s).1
 have phy:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) c:=by
  intro j hj
  rw [cnh]
  simpa only [borrowedValue,dite_eq_left hj,UniformBorrowedCoordinateMachine.embedding] using
   physical j hj
 let ce:=setPC c 0
 have cw:=changePC_bound B c 0 setBroadcast.final_bound (by omega)
 have ch:UniformCrossBroadcastTableMachine.Header (count q slot) g q.i0 Q T (P+(signIndex slot).val) ce:=by
  have h:=broadcastSetup_header s booted args
  exact ⟨h.count,h.gates,h.target,h.borrowed,h.output,h.coefficient⟩
 obtain ⟨d,broadcast,printed,bretained,doutside,dframe,dc,dpc⟩:=
  UniformCrossBroadcastTableMachine.execution n B (count q slot) g q.i0 Q T (P+(signIndex slot).val)
   x (borrowedValue q g fit) ce ch rfl (mc.trans ag) phy
   borrowedEnd (by omega) (by omega) cw (by omega)
 have placedBroadcast:=UniformBoundedAssembly.boundedExecution_placed broadcast_code
  (by rw [UniformCrossBroadcastTableMachine.program_length];omega) (by omega) broadcast
 rw [UniformSeedRankCrossPreparation.placed_zero c 45 cp] at placedBroadcast

 let u:=setPC d 65
 have heaps:=setup_heap broadcastSetup (by simp) s
 refine ⟨u,?_,rfl,((broadcast_stable dframe).booted cb.withPC).withPC,((broadcast_stable dframe).args ca.withPC).withPC,
  UniformCrossBroadcastTableMachine.rows_table printed,dc,?_,?_,dframe.1.trans heaps.2.1,
  dframe.2.2.1.trans heaps.2.2.2.1,dframe.2.2.2.1.trans heaps.2.2.2.2⟩
 · convert setBroadcast.trans placedBroadcast using 1 <;>try simp only [broadcastSetup_length,u,setPC] <;>omega
 · intro i hi;exact (doutside i (Or.inl (by omega))).trans (congrFun cnh i)
 · intro i hi;exact (doutside i (Or.inr (by omega))).trans (congrFun cnh i)

/-- Actual translated rows; this boundary keeps all earlier scalar banks. -/
theorem translation_stage_high {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ)
 (q:Row) (slot:Slot) (x:Fin n→ℂ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s) (booted:Booted q slot g Q s)
 (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g) (targetEnd:q.i0+q.a ≤ q.width)
 (extent:q.offset+q.width ≤ B) (raw:UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) s)
 (counted:s.natReg 894=count q slot) (borrowedEnd:Q ≤ T) (rawEnd:T+3*q.a ≤ E)
 (tableEnd:E+3*q.a ≤ B) (code:241 ≤ B) (pc:s.pc=65) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (19*count q slot+9) u ∧ u.pc=92 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossShearTableMachine.Table E (rows q slot g P fit) u ∧ u.natReg 894=count q slot ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ (∀i,E+3*q.a ≤ i→u.natHeap i=s.natHeap i) ∧
 u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have safe:=translationSetup_safe B s booted.zero bound
 have first:=block_runs translationSetup program 65 n B x s translationSetup_code pc bound
  (by rw [translationSetup_length];omega) safe.1 safe.2
 let e:=applyBlock translationSetup s
 have ep:e.pc=69:=by rw [applyBlock_pc,pc,translationSetup_length]
 have eb:Booted q slot g Q e:=(translationSetup_stable s).booted booted
 have ea:Args D I Q T E pool mu bar C Z P V r g e:=(translationSetup_stable s).args args
 have heaps:=setup_heap translationSetup (by simp) s
 have rawTable:UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) e:=by
  change UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) (applyBlock translationSetup s)
  simpa only [UniformCrossShearTableMachine.Table,UniformCrossShearTableMachine.RowFields,heaps.1] using raw
 have th:=translationSetup_headers s booted args counted
 let ee:=setPC e 0
 have ew:=changePC_bound B e 0 first.final_bound (by omega)
 obtain ⟨f,run,table,rawRetained,frame,outside,fp⟩:=
  UniformTranslatedMatchingRows.execution n B T E q.offset q.width (rawRows q slot g P fit) x ee
   rfl (by simpa only [ee,setPC,e,rawRows_length] using th.1) th.2.1 th.2.2.1 th.2.2.2 rawTable
   (raw_range q slot g P fit ag targetEnd) (by rw [rawRows_length];omega)
   (by omega) (by rw [rawRows_length];omega) (by rw [rawRows_length];omega) extent ew
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed translation_code
  (by rw [UniformTranslatedMatchingRows.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero e 69 ep] at placedRun
 let u:=setPC f 92
 refine ⟨u,?_,rfl,((translation_stable frame).booted eb.withPC).withPC,
  ((translation_stable frame).args ea.withPC).withPC,table,?_,?_,?_,frame.1.trans heaps.2.1,
  frame.2.2.1.trans heaps.2.2.2.1,frame.2.2.2.1.trans heaps.2.2.2.2⟩
 · convert first.trans placedRun using 1 <;>try simp only [translationSetup_length,rawRows_length,u,setPC] <;>omega
 · have ec:e.natReg 894=count q slot:=by
    simpa only [e,translationSetup,applyBlock,Op.apply,writeNat,next,Function.update_of_ne (by omega : 894≠4990),
     Function.update_of_ne (by omega : 894≠4991),Function.update_of_ne (by omega : 894≠4992),
     Function.update_of_ne (by omega : 894≠4993)] using counted
   exact (frame.2.2.2.2 894 (by omega)).trans ec
 · intro i hi;exact (outside i (Or.inl (by omega))).trans (congrFun heaps.1 i)
 · intro i hi;exact (outside i (Or.inr (by rw [rawRows_length];omega))).trans (congrFun heaps.1 i)

/-- One actual broadcast-cache preparation, from physically stored records. -/
theorem execution_high {R K n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ)
 (q:Row) (slot:Slot) (bank:Fin R→ℂ) (x:Fin n→ℂ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g)
 (sourceEnd:q.j0+q.e ≤ q.width) (targetEnd:q.i0+q.a ≤ q.width)
 (extent:q.offset+q.width ≤ r)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C Z P V mu bar B)
 (low:6 ≤ mu) (fresh:bar<pool)
 (borrowedEnd:Q+g ≤ T) (rawEnd:T+3*q.a ≤ E) (tableEnd:E+3*q.a ≤ B)
 (poolEnd:pool+9*r ≤ B) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B)
 (code:241 ≤ B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ 11*q.width+45*r+150*count q slot+74 ∧ u.pc=240 ∧
 UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r (rows q slot g P fit)
  bank (coefficients q slot g P fit) (rows q slot g P fit).length u ∧
 UniformCrossShearTableMachine.Table E (rows q slot g P fit) u ∧
 u.natReg 894=count q slot ∧ UniformMatchingConjugateLoadMachine.Sources K C Z P V bank u ∧
 UniformHadamardPairMachine.Constants u ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧
 (∀i,E+3*q.a ≤ i→u.natHeap i=s.natHeap i) ∧
 (∀i,(i<pool ∨ pool+9*r ≤ i)→i≠mu→i≠bar→u.scalarHeap i=s.scalarHeap i) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have width:q.width ≤ B:=by omega
 obtain ⟨a,firstTicks,first,cheapA,ap,ab,aa,physical,ah,ahigh,ascalar,aout,aroot⟩:=
  borrowed_stage_high D I Q T E pool mu bar C Z P V r g B q slot x s args source record fit sourceEnd
   targetEnd width (by omega) rowEnd slotEnd code pc bound
 have cap:P+1 ≤ B:=by
  have:=layout.constantsBelow;have:=layout.conjugatesBelow;have:=layout.destinations;have:=layout.bound;omega
 obtain ⟨b,second,bp,bb,ba,raw,bc,bh,bhigh,bscalar,bout,broot⟩:=
  broadcast_stage_high D I Q T E pool mu bar C Z P V r g B q slot x a aa ab fit ag physical
   borrowedEnd (by omega) (targetEnd.trans width) cap code ap first.final_bound
 obtain ⟨c,third,cp,cb,ca,table,cc,ch,chigh,cscalar,cout,croot⟩:=
  translation_stage_high D I Q T E pool mu bar C Z P V r g B q slot x b ba bb fit ag targetEnd
   (extent.trans (by omega)) raw bc (by omega) rawEnd tableEnd code bp second.final_bound
 have scalars:c.scalarHeap=s.scalarHeap:=cscalar.trans (bscalar.trans ascalar)
 have src:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank c:=
  UniformConjugatePackedMatchingPreparation.sources_transport sources scalars
 have const:UniformHadamardPairMachine.Constants c:=by
  simpa only [UniformHadamardPairMachine.Constants,scalars] using constants
 obtain ⟨u,pt,last,cheapP,up,values,rowsOut,uc,srcOut,constOut,nh,outside,outs,roots⟩:=
  pool_stage D I Q T E pool mu bar C Z P V r g B q slot bank x c ca cb fit ag targetEnd extent table cc
   src const layout low fresh (by omega) poolEnd code cp third.final_bound
 refine ⟨u,firstTicks+(14*count q slot+14)+(19*count q slot+9)+pt,?_,by omega,up,values,rowsOut,uc,
  srcOut,constOut,?_,?_,?_,outs.trans (cout.trans (bout.trans aout)),roots.trans (croot.trans (broot.trans aroot))⟩
 · exact ((first.trans second).trans third).executes last
 · intro i hi;exact (congrFun nh i).trans ((ch i hi).trans ((bh i hi).trans (ah i hi)))
 · intro i hi
   exact (congrFun nh i).trans ((chigh i hi).trans ((bhigh i (by omega)).trans (ahigh i (by omega))))
 · intro i hi hm hb;exact (outside i hi hm hb).trans (congrFun scalars i)


end
end ExactFourierCircuits.UniformLocalBroadcastPoolMachine
