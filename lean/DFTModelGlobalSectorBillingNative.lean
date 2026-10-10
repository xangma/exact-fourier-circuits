import UniformSectorPackingMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorBilling
open UniformMachine UniformTraversal UniformSectorPacking
open UniformSectorPackingMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)

/-- Same literal137 source execution, retaining the charged nine-step gather floor.
The construction is the existing native execution proof with one extra arithmetic conjunct. -/
theorem packing_execution (as:List PhysicalAxis) (L:Layout) (n:ℕ) (x:Fin n → ℂ)
 (v:Fin L.total → Scalar) (s:State) (hlen:as.length=L.ell) (hvolume:physicalVolume as=L.total)
 (hh:Header L s) (rows:Rows as 0 L.rows s) (widths:Widths as s) (perms:Permutations as s)
 (widthBelow:∀a∈as,a.widthsBase+a.geometry.widths.length  ≤  L.suffix)
 (permBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum  ≤  L.suffix)
 (source:SourceReady L v s) (hpc:s.pc=0) (hs:WordBound L.B s):
 ∃t ticks,9*L.total≤ticks ∧ ticks  ≤  213*L.total+20  ∧ BoundedExecution program n x L.B s ticks t  ∧
 t.pc=136  ∧ InverseReady L (physicalUnpacking as L hvolume) t  ∧
 (∀i:Fin L.total,t.scalarHeap (L.destination+i.val)=some (v (physicalUnpacking as L hvolume i)))  ∧
 (∀addr,addr < L.destination  ∨ L.destination+L.total  ≤  addr  → t.scalarHeap addr=s.scalarHeap addr)  ∧
 OutsideAllocation L s t  ∧ FinalFrame s t:=by
 obtain ⟨u,suffixRun,written,depth,product,upc,constants,header,outside,frame⟩:=
   suffix_preparation as L n x s hlen hvolume hh rows hpc hs
 have banks:Banks as 0 L u:=by
   have low:∀addr,addr < L.suffix  → u.natHeap addr=s.natHeap addr:=fun addr haddr=>outside addr (Or.inl haddr)
   refine ⟨rows_transfer as 0 L s u (by omega) rows low,
     widths_transfer as L s u widths widthBelow low,?_,widthBelow,permBelow,?_⟩
   · intro a ha j
     rw[low _ (by have h:=permBelow a ha;have hj:=j.isLt;omega)]
     exact perms a ha j
   · intro j hj
     simpa only[Nat.add_zero] using written j (by omega) hj
 have initRun:=initialize_bounded L n x u constants depth upc suffixRun.final_bound
 obtain ⟨ih,ic,cur,ipc,heap⟩:=initialized_properties L u header constants depth
 have ibanks:Banks as 0 L (initialized u):=banks_transfer as 0 L u _ (by omega) banks (fun addr _=>congrFun heap addr)
 have fits:Fits as initialPacking 0 L:=by
   simp only[Fits,initialPacking,Nat.zero_add,Nat.one_mul,hvolume]
   exact ⟨by rfl,by decide,by rfl,by rfl⟩
 obtain ⟨treeTicks,treeBound,trun,e⟩:=physical_tree as L n 0 0 x initialPacking (initialized u)
   (by omega) ih ic cur ibanks fits ipc initRun.final_bound
 let w:=tree as (initialized u)
 have before:Frame s w:=frame.trans ((blocks_frame u).2.2.1.trans e.frame)
 have inverse:InverseReady L (physicalUnpacking as L hvolume) w:=inverse_of_effect as L hvolume _ _ e
 have count:w.natReg 616=L.total:=by simpa only[Nat.zero_add,hvolume] using e.cursor.count
 obtain ⟨exit,exitFrame,gpc,gzero,gcount,gheap⟩:=gather_start L n x w e.constants e.cursor.depth e.pc trun.final_bound
 have gHeader:Header L (startGather w):=e.header.transport L w _ exitFrame
 have gConstants:Constants (startGather w):=by
   simpa only[startGather,writeNat,next,setPC,Constants,Function.update_of_ne (by decide:606 ≠ 611),
     Function.update_of_ne (by decide:607 ≠ 611),Function.update_of_ne (by decide:608 ≠ 611),
     Function.update_of_ne (by decide:609 ≠ 611),Function.update_of_ne (by decide:610 ≠ 611)] using e.constants
 have gi:InverseReady L (physicalUnpacking as L hvolume) (startGather w):=by intro i;rw[gheap];exact inverse i
 have gs:SourceReady L v (startGather w):=by intro i;rw[exitFrame.1,before.1];exact source i
 obtain ⟨gather,gh,gc,idx,tpc,gframe,values,gOutside⟩:=gather_loop L n 0 L.total x
   (physicalUnpacking as L hvolume) v (startGather w) (by omega) gHeader gConstants gzero
   (gcount.trans count) gi gs gpc exit.final_bound
 let t:=gatherLoop L.total (startGather w)
 have run:=suffixRun.trans (initRun.trans (trun.trans (exit.trans gather)))
 have halt:step program n x t=.halted t:=by rw[step,tpc];rfl
 have hb:=tree_budget_bound as
 have length:=axis_count_bound as
 have totalTicks:(10*L.ell+9)+(6+(treeTicks+(3+(9*L.total+1))))+1  ≤  213*L.total+20:=by
   rw[hlen] at length
   rw[hvolume] at hb length
   omega
 refine ⟨t,_,by omega,totalTicks,?_,tpc,?_,fun i=>values i (by omega),?_,?_,?_⟩
 · exact run.executes (.halt run.final_bound halt)
 · intro i
   rw[gframe.1,gheap]
   exact inverse i
 · intro addr haddr
   rw[gOutside addr (by simpa only[Nat.zero_add,Nat.add_zero] using haddr),exitFrame.1,before.1]
 · intro addr hSuffix hStack hInverse
   rw[gframe.1,gheap,
     e.natFrame addr (by simpa only[Nat.zero_mul,Nat.add_zero,Nat.mul_comm] using hStack)
       (fun ds=>by
         have bound:=packed_target_bound as ds
         rw[hvolume] at bound
         rcases hInverse with h|h <;> omega),congrFun heap addr]
   exact outside addr hSuffix
 · have overall:=before.trans exitFrame
   exact ⟨gframe.2.1.trans overall.2.2.1,gframe.2.2.1.trans overall.2.2.2.1,
     fun j hj=>(gframe.2.2.2.1 j hj).trans (overall.2.2.2.2 j hj),
     fun j hj=>(gframe.2.2.2.2 j hj).trans (congrFun overall.2.1 j)⟩


/-- Determinism transfers the floor to any genuine complete run from the same caller. -/
theorem packing_ticks_lower (as:List PhysicalAxis) (L:Layout) (n:ℕ) (x:Fin n → ℂ)
 (v:Fin L.total → Scalar) (s:State) (hlen:as.length=L.ell) (hvolume:physicalVolume as=L.total)
 (hh:Header L s) (rows:Rows as 0 L.rows s) (widths:Widths as s) (perms:Permutations as s)
 (widthBelow:∀a∈as,a.widthsBase+a.geometry.widths.length≤L.suffix)
 (permBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum≤L.suffix)
 (source:SourceReady L v s) (hpc:s.pc=0) (hs:WordBound L.B s)
 {ticks:ℕ} {t:State} (actual:BoundedExecution program n x L.B s ticks t) :
 9*L.total≤ticks := by
 obtain ⟨u,tau,lower,upper,run,rest⟩:=packing_execution as L n x v s hlen hvolume
   hh rows widths perms widthBelow permBelow source hpc hs
 exact (run.executes.deterministic actual.executes).1 ▸ lower

end ExactFourierCircuits.DFTModelGlobalSectorBilling
