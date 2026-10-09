import UniformBoundaryDiagonalMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section

structure FinalHeaders (r arena:ℕ) (s:State):Prop where
 radix:s.natReg 7007=r
 zero:s.natReg 7002=0
 one:s.natReg 7003=1
 descriptor:s.natReg 5848=arena+3*r+4

lemma slot_avoids (j:ℕ) (kept:5900≤j ∨5840≤j ∧j<5850):
 UniformSyntacticNatFrame.Avoids UniformLocalMatchingSlotDirectory.program j:=by
 have scan:UniformLocalMatchingSlotDirectory.program.all (fun i=>
  (UniformSyntacticNatFrame.natDst i).all (fun d=>decide (d<5900 ∧(d<5840 ∨5850≤d))))=true:=by decide +kernel
 intro i hi bad
 have h:=List.all_eq_true.mp scan i hi
 rw[bad] at h
 simp only[Option.all_some,decide_eq_true_eq] at h
 omega

lemma slot_kept {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformLocalMatchingSlotDirectory.program n x B s ticks u)
 (j:ℕ) (kept:5900≤j ∨5840≤j ∧j<5850):u.natReg j=s.natReg j:=
 UniformSyntacticNatFrame.boundedExecution_preserves (slot_avoids j kept) run

structure Working (seed r lane time pool arena:ℕ) (s:State):Prop where
 source:s.natReg 7006=seed
 radix:s.natReg 7007=r
 zero:s.natReg 7002=0
 one:s.natReg 7003=1
 lane:s.natReg 7001=lane
 pool:s.natReg 6020=pool
 arena:s.natReg 7051=arena
 time:s.natReg 5920=time

lemma Working.transfer {seed r lane time pool arena:ℕ}{s u:State}
 (h:Working seed r lane time pool arena s)
 (keep:∀j,5900≤j→j≠7009→j≠7010→u.natReg j=s.natReg j):
 Working seed r lane time pool arena u:=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (keep 7006 (by omega) (by omega) (by omega)).trans h.source
 · exact (keep 7007 (by omega) (by omega) (by omega)).trans h.radix
 · exact (keep 7002 (by omega) (by omega) (by omega)).trans h.zero
 · exact (keep 7003 (by omega) (by omega) (by omega)).trans h.one
 · exact (keep 7001 (by omega) (by omega) (by omega)).trans h.lane
 · exact (keep 6020 (by omega) (by omega) (by omega)).trans h.pool
 · exact (keep 7051 (by omega) (by omega) (by omega)).trans h.arena
 · exact (keep 5920 (by omega) (by omega) (by omega)).trans h.time

structure ValueFrame (s u:State):Prop where
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 registers:∀j,j≠32→j≠125→u.scalarReg j=s.scalarReg j
lemma ValueFrame.trans {s u v:State}(h:ValueFrame s u)(g:ValueFrame u v):ValueFrame s v:=
 ⟨g.outputs.trans h.outputs,g.roots.trans h.roots,fun j h32 h125=>(g.registers j h32 h125).trans (h.registers j h32 h125)⟩

lemma head_working {seedCell seed r lane time pool arena:ℕ}{s:State}
 (args:Args seedCell lane time pool arena s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r):
 Working seed r lane time pool arena (applyBlock head s):=by
 constructor <;>simp[head,applyBlock,Op.apply,writeNat,next,args.seed,args.lane,args.pool,args.arena,args.time,address,width]
lemma head_heaps (s:State):(applyBlock head s).natHeap=s.natHeap ∧
 (applyBlock head s).scalarHeap=s.scalarHeap ∧ValueFrame s (applyBlock head s):=⟨rfl,rfl,⟨rfl,rfl,fun _ _ _=>rfl⟩⟩

lemma prefix_execution {n B seedCell seed r lane time pool arena:ℕ}
 (x:Fin n→ℂ)(s:State)(args:Args seedCell lane time pool arena s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r)
 (sourceFit:seedCell+2≤B)(poolFit:pool+9*r≤B)(code:127≤B)(pc:s.pc=0)(wb:WordBound B s):∃u,
 BoundedRuns program n x B s (45*r+14) u ∧u.pc=18 ∧Working seed r lane time pool arena u ∧
 UniformGlobalScalePoolMachine.Prefix pool (9*r) u ∧
 (∀j,(j<pool ∨pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) ∧u.natHeap=s.natHeap ∧ValueFrame s u:=by
 have seedBound:seed≤B:=(wb.2.2.1 _ _ address).2
 have rBound:r≤B:=(wb.2.2.1 _ _ width).2
 let b:=applyBlock head s
 have boot:BoundedRuns program n x B s 7 b:=by
  have h:=block_runs head program 0 n B x s head_code pc wb (by rw[head_length];omega)
   (by simp[head,readable,Op.readable,Op.apply,writeNat,next,args.seed,address,width])
   (by simp[head,peak,Op.peak,Op.apply,writeNat,next,args.seed,args.pool,address,width];omega)
  simpa only[head_length] using h
 have bp:b.pc=7:=by rw[applyBlock_pc,pc,head_length]
 have bh:=head_working args address width
 let ready:=setPC b 0
 obtain ⟨p,pr,pp,ones,out,frame⟩:=UniformGlobalScalePoolMachine.execution pool r n B x ready
  (by simp[ready,b,head,setPC,applyBlock,Op.apply,writeNat,next,args.pool])
  (by simp[ready,b,head,setPC,applyBlock,Op.apply,writeNat,next,args.seed,address,width])
  poolFit (by omega) rfl (changePC_bound B b 0 boot.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed pool_code
  (by rw[UniformGlobalScalePoolMachine.program_length];omega) (by omega) pr
 rw[show placed 7 ready=b by change {b with pc:=7}=b;rw[←bp]] at moved
 let u:=setPC p 18
 change BoundedRuns program n x B b (45*r+7) u at moved
 have working:Working seed r lane time pool arena u:=bh.transfer (by
  intro j lo n9 n10;exact frame.natReg j (by omega) (by omega) (by omega) (by omega))
 have heaps:=head_heaps s
 refine ⟨u,?_,rfl,working,ones,?_,frame.natHeap.trans heaps.1,?_⟩
 · convert boot.trans moved using 1;omega
 · intro j outside
   exact (out j outside).trans (congrFun heaps.2.1 j)
 · exact heaps.2.2.trans ⟨frame.outputs,frame.roots,fun j _ h125=>frame.scalarReg j h125⟩

lemma copy_setup_working {seed r lane time pool arena:ℕ}{s:State}
 (h:Working seed r lane time pool arena s):Working seed r lane time pool arena (applyBlock copySetup s):=
 h.transfer (by intro j lo n9 n10;simp (disch:=omega) [copySetup,applyBlock,Op.apply,writeNat,next])
lemma copy_setup_heaps (s:State):(applyBlock copySetup s).natHeap=s.natHeap ∧
 (applyBlock copySetup s).scalarHeap=s.scalarHeap ∧ValueFrame s (applyBlock copySetup s):=⟨rfl,rfl,⟨rfl,rfl,fun _ _ _=>rfl⟩⟩

lemma copy_execution {n B seed r time pool arena:ℕ}(q:Fin 3)(omega:ℂ)(x:Fin n→ℂ)(s:State)
 (h:Working seed r q.val time pool arena s)
 (original:UniformLocalSeedTableMachine.Compact r seed omega s)
 (sourceBelow:seed+5*r≤pool)(poolFit:pool+9*r≤B)(code:127≤B)(pc:s.pc=18)(wb:WordBound B s):∃u,
 BoundedRuns program n x B s (8*r+9) u ∧u.pc=34 ∧Working seed r q.val time pool arena u ∧
 (∀j:Fin r,u.scalarHeap (pool+j.val)=some (prepared (UniformLocalSeedTableMachine.seedValue omega ⟨q.val,by omega⟩ j.val))) ∧
 (∀j,(j<pool ∨pool+r≤j)→u.scalarHeap j=s.scalarHeap j) ∧u.natHeap=s.natHeap ∧ValueFrame s u:=by
 have laneBound:q.val*r≤2*r:=Nat.mul_le_mul_right r (by have:=q.isLt;omega)
 let c:=applyBlock copySetup s
 have boot:BoundedRuns program n x B s 5 c:=by
  have run:=block_runs copySetup program 18 n B x s copySetup_code pc wb
   (by rw[copySetup_length];omega) (by simp[copySetup,readable,Op.readable])
   (by simp[copySetup,peak,Op.peak,Op.apply,writeNat,next,h.radix,h.source,h.zero,h.lane,h.pool];omega)
  simpa only[copySetup_length] using run
 have cp:c.pc=23:=by rw[applyBlock_pc,pc,copySetup_length]
 have ch:=copy_setup_working h
 have heaps:=copy_setup_heaps s
 let ready:=setPC c 0
 have src:UniformLocalSeedTableMachine.Strided.Source r (seed+q.val*r) 1 ready.scalarHeap:=by
  intro j hj
  refine ⟨prepared (UniformLocalSeedTableMachine.seedValue omega ⟨q.val,by omega⟩ j),?_⟩
  exact (congrFun heaps.2.1 _).trans (by simpa only[Nat.one_mul,Nat.add_assoc] using original ⟨q.val,by omega⟩ ⟨j,hj⟩)
 obtain ⟨v,run,copied,_source,out,frame,nat⟩:=UniformLocalSeedTableMachine.Strided.execution
  n x r (seed+q.val*r) pool 1 B ready src (by omega) (by omega) (by omega) (by omega) rfl
  (by simp[ready,c,copySetup,setPC,applyBlock,Op.apply,writeNat,next])
  (by simp[ready,c,copySetup,setPC,applyBlock,Op.apply,writeNat,next,h.radix,h.zero])
  (by simp[ready,c,copySetup,setPC,applyBlock,Op.apply,writeNat,next,h.source,h.lane,h.radix])
  (by simp[ready,c,copySetup,setPC,applyBlock,Op.apply,writeNat,next,h.pool,h.zero])
  (changePC_bound B c 0 boot.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed copy_code
  (by rw[UniformLocalSeedTableMachine.Strided.program_length];omega) (by omega) run
 rw[show placed 23 ready=c by change {c with pc:=23}=c;rw[←cp]] at moved
 let u:=setPC v 34
 change BoundedRuns program n x B c (8*r+4) u at moved
 have working:Working seed r q.val time pool arena u:=ch.transfer (by
  intro j lo n9 n10;exact nat j (Or.inr (by omega)))
 refine ⟨u,?_,rfl,working,?_,?_,frame.1.trans heaps.1,?_⟩
 · convert boot.trans moved using 1;omega
 · intro j
   exact (copied j.val j.isLt).trans ((congrFun heaps.2.1 _).trans
    (by simpa only[Nat.one_mul,Nat.add_assoc] using original ⟨q.val,by omega⟩ j))
 · intro j outside
   exact (out j outside).trans (congrFun heaps.2.1 j)
 · exact heaps.2.2.trans ⟨frame.2.1,frame.2.2.1,fun j h32 _=>frame.2.2.2 j h32⟩

lemma slot_setup_working {seed r lane time pool arena:ℕ}{s:State}
 (h:Working seed r lane time pool arena s):Working seed r lane time pool arena (applyBlock slotSetup s):=
 h.transfer (by intro j lo n9 n10;simp (disch:=omega) [slotSetup,applyBlock,Op.apply,writeNat,next])
lemma slot_setup_heaps (s:State):(applyBlock slotSetup s).natHeap=s.natHeap ∧
 (applyBlock slotSetup s).scalarHeap=s.scalarHeap ∧(applyBlock slotSetup s).scalarReg=s.scalarReg ∧
 (applyBlock slotSetup s).outputs=s.outputs ∧(applyBlock slotSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩

lemma slot_execution {n B seed r lane time pool arena:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Working seed r lane time pool arena s)(positive:2≤r)(natFit:arena+3*r+11≤B)
 (code:127≤B)(pc:s.pc=34)(wb:WordBound B s):∃u,
 BoundedExecution program n x B s (17*r+59) u ∧u.pc=126 ∧
 UniformLocalMatchingSlotDirectory.Entry (arena+3*r+4) time r pool r (arena+r) arena 1 u ∧
 UniformSectorPackingMachine.Rows [axis r arena positive] 0 (arena+3*r) u ∧
 UniformSectorPackingMachine.Widths [axis r arena positive] u ∧
 UniformSectorPackingMachine.Permutations [axis r arena positive] u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,j<arena→u.natHeap j=s.natHeap j) ∧FinalHeaders r arena u:=by
 have timeBound:time≤B:=by rw[←h.time];exact wb.2.1 5920
 have poolBound:pool≤B:=by rw[←h.pool];exact wb.2.1 6020
 let a:=applyBlock slotSetup s
 have boot:BoundedRuns program n x B s 12 a:=by
  have run:=block_runs slotSetup program 34 n B x s slotSetup_code pc wb
   (by rw[slotSetup_length];omega) (by simp[slotSetup,readable,Op.readable])
   (by simp[slotSetup,peak,Op.peak,Op.apply,writeNat,next,h.radix,h.zero,h.pool,h.arena,h.time];omega)
  simpa only[slotSetup_length] using run
 have ap:a.pc=46:=by rw[applyBlock_pc,pc,slotSetup_length]
 have ah:=slot_setup_working h
 have heaps:=slot_setup_heaps s
 let ready:=setPC a 0
 have args:UniformLocalMatchingSlotDirectory.Args time r pool arena (arena+r) (arena+2*r)
  (arena+3*r) arena (arena+3*r+4) 1 0 ready:=by
  constructor <;>simp[ready,a,slotSetup,setPC,applyBlock,Op.apply,writeNat,next,h.radix,h.zero,h.pool,h.arena,h.time]
  all_goals omega
 obtain ⟨z,run,_cost,zp,entry,row,widths,permutation,heap,registers,outputs,roots,natPrefix⟩:=
  UniformLocalMatchingSlotDirectory.execution x emptyEdges ready args (by intro i;exact Fin.elim0 i)
   empty_matching (empty_range r) positive (by omega) (by omega) (by omega) (by omega)
   (by omega) natFit (by omega) rfl (changePC_bound B a 0 boot.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed slot_code
  (by rw[UniformLocalMatchingSlotDirectory.program_length];omega) (by omega) run
 rw[show placed 46 ready=a by change {a with pc:=46}=a;rw[←ap]] at moved
 let u:=setPC z 126
 change BoundedRuns program n x B a (UniformMatchingAxisTableMachine.runtime r 0+25) u at moved
 have stop:BoundedExecution program n x B u 1 u:=.halt moved.final_bound (by simp[step,u,setPC,halt_at])
 refine ⟨u,?_,rfl,?_,?_,?_,?_,heap.trans heaps.2.1,registers.trans heaps.2.2.1,
  outputs.trans heaps.2.2.2.1,roots.trans heaps.2.2.2.2,?_,?_⟩
 · convert boot.executes (moved.executes stop) using 1
   simp only[UniformMatchingAxisTableMachine.runtime];omega
 · simpa only[u,setPC,UniformLocalMatchingSlotDirectory.Entry,Nat.sub_zero] using entry
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Rows] using row
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Widths] using widths
 · simpa only[u,setPC,axis,UniformSectorPackingMachine.Permutations] using permutation
 · intro j hj
   exact (natPrefix j hj).trans (congrFun heaps.1 j)
 · exact ⟨(slot_kept run 7007 (Or.inl (by omega))).trans ah.radix,
    (slot_kept run 7002 (Or.inl (by omega))).trans ah.zero,
    (slot_kept run 7003 (Or.inl (by omega))).trans ah.one,
    (slot_kept run 5848 (Or.inr ⟨by omega,by omega⟩)).trans args.directory⟩

structure CoreResult (n B r time pool arena:ℕ)(positive:2≤r)(q:Fin 3)(omega:ℂ)
 (x:Fin n→ℂ)(s u:State):Prop where
 execution:BoundedExecution program n x B s (70*r+82) u
 pc:u.pc=126
 entry:UniformLocalMatchingSlotDirectory.Entry (arena+3*r+4) time r pool r (arena+r) arena 1 u
 row:UniformSectorPackingMachine.Rows [axis r arena positive] 0 (arena+3*r) u
 widths:UniformSectorPackingMachine.Widths [axis r arena positive] u
 permutation:UniformSectorPackingMachine.Permutations [axis r arena positive] u
 copied:∀j:Fin r,u.scalarHeap (pool+j.val)=some (prepared (UniformLocalSeedTableMachine.seedValue omega ⟨q.val,by omega⟩ j.val))
 ones:∀lane:Fin 9,lane.val≠0→∀j:Fin r,u.scalarHeap (pool+lane.val*r+j.val)=some (prepared 1)
 natPrefix:∀j,j<arena→u.natHeap j=s.natHeap j
 scalarOutside:∀j,(j<pool ∨pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j
 frame:ValueFrame s u
 headers:FinalHeaders r arena u

/-- Real source reads, initialized nine-lane pool, literal scalar copy and
empty-matching80 publication, continuously in the actual127 program. -/
theorem execution {n B seedCell seed r time pool arena:ℕ}(q:Fin 3)(omega:ℂ)
 (x:Fin n→ℂ)(s:State)(args:Args seedCell q.val time pool arena s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r)
 (original:UniformLocalSeedTableMachine.Compact r seed omega s)
 (positive:2≤r)(sourceBelow:seed+5*r≤pool)(sourceFit:seedCell+2≤B)
 (natFit:arena+3*r+11≤B)(poolFit:pool+9*r≤B)(code:127≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,CoreResult n B r time pool arena positive q omega x s u:=by
 obtain ⟨p,pRun,pp,pHead,pOnes,pOutside,pNat,pFrame⟩:=
  prefix_execution x s args address width sourceFit poolFit code pc wb
 have originalP:UniformLocalSeedTableMachine.Compact r seed omega p:=by
  intro lane j
  have fit:lane.val*r+j.val<5*r:=by
   have mul:=Nat.mul_le_mul_right r (show lane.val+1≤5 by have:=lane.isLt;omega)
   have:=j.isLt;nlinarith
  exact (pOutside _ (Or.inl (by omega))).trans (original lane j)
 obtain ⟨v,vRun,vp,vHead,copied,vOutside,vNat,vFrame⟩:=
  copy_execution q omega x p pHead originalP sourceBelow poolFit code pp pRun.final_bound
 obtain ⟨u,uRun,up,entry,row,widths,perm,heap,regs,outputs,roots,nat,headers⟩:=
  slot_execution x v vHead positive natFit code vp vRun.final_bound
 refine ⟨u,?_,up,entry,row,widths,perm,?_,?_,?_,?_,
  pFrame.trans (vFrame.trans ⟨outputs,roots,fun j _ _=>congrFun regs j⟩),headers⟩
 · convert pRun.executes (vRun.executes uRun) using 1;omega
 · intro j;exact (congrFun heap _).trans (copied j)
 · intro lane nonzero j
   have lower:pool+r≤pool+lane.val*r+j.val:=by
    have mul:=Nat.mul_le_mul_right r (show 1≤lane.val by omega);omega
   have upper:lane.val*r+j.val<9*r:=by
    have mul:=Nat.mul_le_mul_right r (show lane.val+1≤9 by have:=lane.isLt;omega)
    have:=j.isLt;nlinarith
   exact (congrFun heap _).trans ((vOutside _ (Or.inr lower)).trans (by simpa only[Nat.add_assoc] using pOnes _ upper))
 · intro j hj;exact (nat j hj).trans ((congrFun vNat j).trans (congrFun pNat j))
 · intro j outside;exact (congrFun heap j).trans ((vOutside j (by omega)).trans (pOutside j outside))
end
end ExactFourierCircuits.UniformBoundaryDiagonalMachine
