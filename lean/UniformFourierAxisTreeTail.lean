import UniformFourierAxisPrepareHead
import UniformFourierAxisPrepareControl
import UniformCacheRangeSelectorPreservation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisTreeTail
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace R
export UniformCacheRangeSelector (Range Args RangeSource Layout selections total stride)
end R
namespace F
export UniformFourierAxisPrepareFooter (Args Result)
end F
namespace Control
export UniformFourierAxisPrepareControl (decisionState decision_execution decision_frame decision_pc decision_workspace footer_execution footer_frame footerWrites)
end Control
noncomputable section

def Kept(q:ℕ):Prop:=UniformFourierAxisPrepareHead.Protected q∨
 (6800≤q∧q≤6821∧q≠6801∧q≠6802)∨(7050≤q∧q≤7059)∨q=7000∨q=7080

structure Header(r N S j physical directory cacheN cacheS:ℕ)(s:State):Prop where
 workspace:UniformFourierAxisWorkspaceHeader.Header r N S s
 radix:s.natReg 6800=r
 axis:s.natReg 5922=j
 physical:s.natReg 6028=physical
 directory:s.natReg 5923=directory
 cacheNat:s.natReg 6819=cacheN
 cacheScalar:s.natReg 6821=cacheS

lemma Header.transfer {r N S j physical directory cacheN cacheS:ℕ}{s u:State}
 (h:Header r N S j physical directory cacheN cacheS s)
 (keep:∀q,(7050≤q∧q≤7059)∨q=5934∨q=5935∨q=6800∨q=5922∨q=6028∨q=5923∨q=6819∨q=6821→u.natReg q=s.natReg q):
 Header r N S j physical directory cacheN cacheS u:=
 ⟨UniformFourierAxisPrepareHead.workspace_transfer h.workspace (fun q hq=>keep q (by omega)),
 (keep _ (by omega)).trans h.radix,(keep _ (by omega)).trans h.axis,
 (keep _ (by omega)).trans h.physical,(keep _ (by omega)).trans h.directory,
 (keep _ (by omega)).trans h.cacheNat,(keep _ (by omega)).trans h.cacheScalar⟩

/-- Actual TREE tail142, including both literal range scans and the common halt.
The only table premises are stored counts/ranges/ABI time-kind data and word bounds. -/
theorem execution {n B r N S j physical directory cacheN cacheS tasks control tick rectangleCount:ℕ}
 (x:Fin n→ℂ)(rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)(s:State)
 (head:Header r N S j physical directory cacheN cacheS s)
 (args:R.Args r tasks control tick (UniformFourierAxisWorkspace.axisBank r N S).selected s)
 (source:R.RangeSource r tasks control rectangleCount rectangle nodes s.natHeap)
 (layout:R.Layout r tasks control rectangleCount (UniformFourierAxisWorkspace.axisBank r N S).selected B nodes)
 (rectangleValues:∀k,k<rectangleCount→(rectangle k).1+28≤B∧(rectangle k).2≤B)
 (nodeValues:∀q∈nodes,∀k,k<q.count→(q.records k).1+28≤B∧(q.records k).2≤B)
 (mode:s.natReg 7080=0)(pc:s.pc=138)(bound:WordBound B s)(code:389≤B)
 (physicalFit:physical+4*j≤B):
 ∃u ticks,BoundedExecution UniformFourierAxisPrepareMachine.program n x B s ticks u∧
 ticks≤21*(rectangleCount+R.total nodes)+16*nodes.length+52∧u.pc=388∧
 F.Result r N S (R.selections r control rectangleCount tick rectangle nodes).length j physical directory cacheN cacheS u∧
 u.natHeap=UniformCacheRangeSelector.S.writeSelections (UniformFourierAxisWorkspace.axisBank r N S).selected 0
  (R.selections r control rectangleCount tick rectangle nodes) s.natHeap∧
 u.scalarHeap=s.scalarHeap∧u.scalarReg=s.scalarReg∧u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 u.natReg 6703=tick∧(∀q,Kept q→u.natReg q=s.natReg q):=by
 have branch:=Control.decision_execution n B 0 x s pc mode bound code
 let b:=Control.decisionState 0 s
 have bp:b.pc=142:=Control.decision_pc 0 s
 have df:=Control.decision_frame 0 s
 have keepB(q:ℕ)(neq:q≠7081):b.natReg q=s.natReg q:=df.natReg q (by simpa using neq)
 have headB:=head.transfer (u:=b) (by intro q h;exact keepB q (by omega))
 have argsB:R.Args r tasks control tick (UniformFourierAxisWorkspace.axisBank r N S).selected b:=
  ⟨(keepB _ (by omega)).trans args.radix,(keepB _ (by omega)).trans args.tasks,
   (keepB _ (by omega)).trans args.control,(keepB _ (by omega)).trans args.tick,
   (keepB _ (by omega)).trans args.output⟩
 let b0:=setPC b 0
 have bw:WordBound B b0:=⟨by change 0≤B;omega,branch.final_bound.2⟩
 have sourceB:R.RangeSource r tasks control rectangleCount rectangle nodes b0.natHeap:=by
  change R.RangeSource r tasks control rectangleCount rectangle nodes b.natHeap
  rw[df.natHeap];exact source
 have args0:R.Args r tasks control tick (UniformFourierAxisWorkspace.axisBank r N S).selected b0:=
  ⟨argsB.radix,argsB.tasks,argsB.control,argsB.tick,argsB.output⟩
 obtain ⟨v,t,rangeRun,cheap,_vp,used,_tick,heap⟩:=UniformCacheRangeSelector.execution x rectangle nodes b0 args0 sourceB layout
  rectangleValues nodeValues (by omega) rfl bw
 have rangePlaced:=UniformBoundedAssembly.boundedExecution_placed UniformFourierAxisPrepareMachine.ranges_code
  (by rw[UniformCacheRangeSelector.program_length];omega) (by omega) rangeRun
 have start:placed 142 b0=b:=by
  simp only[b0,placed,setPC,Nat.add_zero]
  rw[←bp]
 rw[start] at rangePlaced
 let c:=setPC v 370
 have keepC(q:ℕ)(lo:q<6700∨6723<q)(hi:q<7100∨7129<q):c.natReg q=b.natReg q:=
  UniformCacheRangeSelector.execution_register rangeRun q lo hi
 have headC:=headB.transfer (u:=c) (by intro q h;exact keepC q (by omega) (by omega))
 have footerArgs:F.Args r N S (R.selections r control rectangleCount tick rectangle nodes).length j physical directory cacheN cacheS c:=
  ⟨headC.workspace,used,headC.radix,headC.axis,headC.physical,headC.directory,headC.cacheNat,headC.cacheScalar⟩
 obtain ⟨finish,result,_ff⟩:=Control.footer_execution n B r N S _ j physical directory cacheN cacheS x c footerArgs
  rfl rangePlaced.final_bound code physicalFit
 have rf:=UniformCacheRangeSelector.execution_frame rangeRun
 have ff:=Control.footer_frame c
 let u:=applyBlock UniformFourierAxisPrepareFooter.block c
 have up:u.pc=388:=by
  rw[UniformFourierAxisPrepareControl.block_pc,UniformFourierAxisPrepareFooter.block_length];rfl
 refine ⟨u,_,branch.executes (rangePlaced.executes finish),?_,up,result,?_,?_,?_,?_,?_,?_,?_⟩
 · simp only[UniformFourierAxisPrepareControl.decisionTicks,ite_true]
   omega
 · change c.natHeap=UniformCacheRangeSelector.S.writeSelections _ 0 _ s.natHeap
   change v.natHeap=UniformCacheRangeSelector.S.writeSelections _ 0 _ s.natHeap
   rw[heap]
   change UniformCacheRangeSelector.S.writeSelections _ 0 _ b.natHeap=UniformCacheRangeSelector.S.writeSelections _ 0 _ s.natHeap
   rw[df.natHeap]
 · exact ff.scalarHeap.trans (rf.scalarHeap.trans df.scalarHeap)
 · exact ff.scalarReg.trans (rf.scalarReg.trans df.scalarReg)
 · exact ff.outputs.trans (rf.outputs.trans df.outputs)
 · exact ff.roots.trans (rf.roots.trans df.roots)
 · exact (ff.natReg 6703 (by decide)).trans _tick
 · intro q h
   have keepF:u.natReg q=c.natReg q:=ff.natReg q (by
    simp only[Control.footerWrites,UniformFourierAxisPrepareControl.footerWrites,List.mem_cons,List.not_mem_nil,or_false]
    unfold Kept UniformFourierAxisPrepareHead.Protected at h;omega)
   exact keepF.trans ((keepC q (by unfold Kept UniformFourierAxisPrepareHead.Protected at h;omega)
    (by unfold Kept UniformFourierAxisPrepareHead.Protected at h;omega)).trans
    (keepB q (by unfold Kept UniformFourierAxisPrepareHead.Protected at h;omega)))
end
end ExactFourierCircuits.UniformFourierAxisTreeTail
