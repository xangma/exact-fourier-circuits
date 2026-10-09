import UniformResidualPermutationPreparation
import UniformResidualTraversalHeaders
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualPermutationPreparation
open UniformMachine UniformAssembly BinaryFrames UniformBinaryXorCoordinates
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section
theorem execution_images (n B q w U images stack output table:ℕ) (v:Vec (Fin (w+1))) (x:Fin n→ ℂ) (s:State)
 (pc:s.pc=0) (input:Inputs q (w+1) U images stack output table s)
 (qp:1≤ q) (nonzero:v≠0) (source:UniformRepeatedMaskMachine.Source U v s)
 (bound:WordBound B s) (code:188≤ B) (sourceEnd:U+(w+1)≤ images)
 (imagesBefore:images+q*(w+1)≤ stack) (stackBefore:stack+2*(q*(w+1))≤ output)
 (outputBefore:output+2^(q*(w+1))≤ table) (tableBound:table+2^q*2^q≤ B) :
 ∃p:Fin (w+1),∃hp:v p=1,∃u ticks,BoundedExecution program n x B s ticks u ∧
 ticks≤ runtimeBound q (w+1) ∧ u.pc=187 ∧ v p=1 ∧ u.natReg 4023=2^(q*(w+1)) ∧ u.natReg 4069=1 ∧ u.natReg 4067=output ∧
 (∀j:Fin (2^(q*(w+1))),u.natHeap (output+j.val)=some ((UniformResidualPermutation.permutation q w v p hp j).val)) ∧
 UniformXorTableMachine.Entries q table (2^q*2^q) u ∧
 UniformRepeatedMaskMachine.Source U v u ∧
 (∀i,i< q*(w+1)→ u.natHeap (images+i)=some (UniformResidualPermutation.image q w v p hp i)) ∧
 (∀z,z< images ∨ table+2^q*2^q≤ z→ u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ RegFrame s u ∧ UniformResidualFiberAddressMachine.Header (q*(w+1)) q (w+1) images stack output table u := by
 have qb:q≤ B:=by have h:=bound.2.1 4060;rw [input.descriptor.columns] at h;exact h
 have wb:w+1≤ B:=by have h:=bound.2.1 4061;rw [input.descriptor.width] at h;exact h
 have tableB:table≤ B:=(Nat.le_add_right table _).trans tableBound
 have outputB:output≤ B:=(Nat.le_add_right output _).trans (outputBefore.trans tableB)
 have stackB:stack≤ B:=(Nat.le_add_right stack _).trans (stackBefore.trans outputB)
 have imageExtent:images+q*(w+1)≤ B:=imagesBefore.trans stackB
 have imageTable:images+q*(w+1)≤ table:=imagesBefore.trans
  ((Nat.le_add_right stack _).trans (stackBefore.trans ((Nat.le_add_right output _).trans outputBefore)))
 have volume:2^(q*(w+1))≤ B:=(Nat.le_add_left _ output).trans (outputBefore.trans tableB)
 obtain ⟨p,described,dt,dr,dtb,dp,pbit,dk,di,dw,selected,reps,dsource,doutside,dsh,dsr,dout,droot⟩:=
  UniformResidualDescriptorBankMachine.execution n B q (w+1) U images v x s pc input.descriptor qp (by omega) nonzero source bound (by omega) sourceEnd imageExtent volume
 have df:=UniformResidualDescriptorBankMachine.execution_frame dr.executes
 have placedDescriptor:=UniformBoundedAssembly.boundedExecution_placed descriptor_code (by change 71≤ B;omega) (by omega) dr
 have same:placed 0 s=s:=by unfold placed;simp only [Nat.zero_add]
 rw [same] at placedDescriptor
 let atXor:State:={described with pc:=71}
 have keep (r:ℕ) (hr:4065< r) : atXor.natReg r=s.natReg r := df.natReg r (by omega)
 have xq:atXor.natReg 4060=q:=(df.natReg _ (by right;omega)).trans input.descriptor.columns
 have xt:atXor.natReg 4068=table:=(keep _ (by omega)).trans input.table
 have qX:atXor.natReg 4060≤ B:=by omega
 have tX:atXor.natReg 4068≤ B:=by omega
 have safeX:readable xorSetup atXor ∧ peak xorSetup atXor≤ B:=by
  simp [xorSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,xq,xt];omega
 have setup:=block_runs xorSetup program 71 n B x atXor xor_setup_code rfl placedDescriptor.final_bound (by change 74≤ B;omega) safeX.1 safeX.2
 let seeded:=applyBlock xorSetup atXor
 let child:State:={seeded with pc:=0}
 have cb:=changePC_bound B seeded 0 setup.final_bound (by omega)
 obtain ⟨tabled,tr,tp,size,entries,toutside,tf⟩:=UniformXorCallerInterface.table_execution_bounded_size n q table B x child rfl
  (by simp [child,seeded,xorSetup,applyBlock,Op.apply,evalNat,writeNat,next,xq])
  (by simp [child,seeded,xorSetup,applyBlock,Op.apply,evalNat,writeNat,next,xt]) cb (by omega) tableBound
 have placedTable:=UniformBoundedAssembly.boundedExecution_placed xor_code (by change 112≤ B;omega) (by omega) tr
 have sp:seeded.pc=74:=by simp [seeded,xorSetup,applyBlock,Op.apply,writeNat,next,atXor]
 have eq:placed 74 child=seeded:=by change {seeded with pc:=74}=seeded;rw [←sp]
 rw [eq] at placedTable
 let atDFS:State:={tabled with pc:=112}
 have retained (r:ℕ) (hr:4065< r ∧ r≠4069) : atDFS.natReg r=s.natReg r:=by
  have rt:=tf.2.2.2.2 r (by omega)
  simpa (disch:=omega) [atDFS,child,seeded,xorSetup,applyBlock,Op.apply,evalNat,writeNat,next,keep r hr.1] using rt
 have one:atDFS.natReg 4069=1:=by
  have rt:=tf.2.2.2.2 4069 (by omega)
  simpa [atDFS,child,seeded,xorSetup,applyBlock,Op.apply,evalNat,writeNat,next] using rt
 have ss:atDFS.natReg 4066=stack:=(retained _ (by omega)).trans input.stack
 have oo:atDFS.natReg 4067=output:=(retained _ (by omega)).trans input.output
 have tt:atDFS.natReg 4068=table:=(retained _ (by omega)).trans input.table
 have oneT:tabled.natReg 4069=1:=one
 have ssT:tabled.natReg 4066=stack:=ss
 have ooT:tabled.natReg 4067=output:=oo
 have ttT:tabled.natReg 4068=table:=tt
 have sizeBound:atDFS.natReg 3423≤ B:=placedTable.final_bound.2.1 3423
 have sizeD:atDFS.natReg 3423=2^q:=size
 have safeD:readable dfsSetup atDFS ∧ peak dfsSetup atDFS≤ B:=by
  simp [dfsSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,ss,oo,tt,sizeD];omega
 have install:=block_runs dfsSetup program 112 n B x atDFS dfs_setup_code rfl placedTable.final_bound (by change 116≤ B;omega) safeD.1 safeD.2
 let ready:=applyBlock dfsSetup atDFS
 let dfsChild:State:={ready with pc:=0}
 have kept (r:ℕ) (hr:r=4008 ∨ r=4009 ∨ r=4014) : dfsChild.natReg r=described.natReg r:=by
  have rt:=tf.2.2.2.2 r (by omega)
  simpa (disch:=omega) [dfsChild,ready,dfsSetup,atDFS,child,seeded,xorSetup,atXor,applyBlock,Op.apply,evalNat,writeNat,next] using rt
 have args:UniformResidualFiberTraversal.Inputs (q*(w+1)) q (w+1) images stack output table dfsChild:=by
  refine ⟨(kept _ (by omega)).trans dk,(kept _ (by omega)).trans di,?_,?_,?_,(kept _ (by omega)).trans dw,?_⟩
  all_goals simp [dfsChild,ready,dfsSetup,atDFS,applyBlock,Op.apply,evalNat,writeNat,next,oneT,ssT,ooT,ttT,size]
 have bank:∀i,i< q*(w+1)→ dfsChild.natHeap (images+i)=some (UniformResidualPermutation.image q w v p pbit i):=by
  intro i hi
  have old:=UniformResidualPermutation.unit_image_bank q w images v p pbit described selected reps (⟨i,hi⟩:Fin (q*(w+1)))
  have before:images+i< table:=(Nat.add_lt_add_left hi images).trans_le imageTable
  have outside:=toutside (images+i) (Or.inl before)
  simpa [dfsChild,ready,dfsSetup,atDFS,child,seeded,xorSetup,atXor,applyBlock,Op.apply,evalNat,writeNat,next,
   UniformResidualPermutation.image,hi] using outside.trans old
 have entriesNow:UniformXorTableMachine.Entries q table (2^q*2^q) dfsChild:=entries
 have db:=changePC_bound B ready 0 install.final_bound (by omega)
 obtain ⟨addressed,ar,ap,count,written,aoutside,ash,asr,aout,aroot,aheader⟩:=UniformResidualFiberTraversal.execution_headers n B (q*(w+1)) q (w+1)
  images stack output table (UniformResidualPermutation.image q w v p pbit) x dfsChild rfl args db (by omega)
  imagesBefore stackBefore outputBefore tableBound volume bank (UniformResidualPermutation.image_small q w v p pbit) entriesNow
 have aframe:=UniformResidualFiberTraversal.execution_frame ar.executes
 have actualOne:addressed.natReg 4069=1:=by
  have h:=aframe.natReg 4069 (by omega)
  simpa [dfsChild,ready,dfsSetup,atDFS,applyBlock,Op.apply,evalNat,writeNat,next,oneT] using h
 have actualOutputPointer:addressed.natReg 4067=output:=by
  have h:=aframe.natReg 4067 (by omega)
  simpa [dfsChild,ready,dfsSetup,atDFS,applyBlock,Op.apply,evalNat,writeNat,next,ooT] using h
 have placedDFS:=UniformBoundedAssembly.boundedExecution_placed dfs_code (by change 187≤ B;omega) (by omega) ar
 have rp:ready.pc=116:=by simp [ready,dfsSetup,applyBlock,Op.apply,writeNat,next,atDFS]
 have deq:placed 116 dfsChild=ready:=by change {ready with pc:=116}=ready;rw [←rp]
 rw [deq] at placedDFS
 let u:State:={addressed with pc:=187}
 have final:BoundedExecution program n x B u 1 u:=.halt placedDFS.final_bound (by simp [step,u,halt_at])
 refine ⟨p,pbit,u,dt+3+(4*q+10+(12*q+15)*(2^q*2^q))+4+(UniformResidualFiberAddressMachine.treeCost (w+1) (q*(w+1))+9)+1,
  ?_,?_,rfl,pbit,count,actualOne,actualOutputPointer,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · convert (placedDescriptor.trans (setup.trans (placedTable.trans (install.trans placedDFS)))).executes final using 1
   simp [xorSetup,dfsSetup];omega
 · unfold runtimeBound;omega
 · intro j
   have wr:=written j.val j.isLt
   rwa [UniformResidualPermutation.address_eq_permutation q w v p pbit j] at wr
 · intro j hj
   have frame:=aoutside (table+j) (by right;omega) (by right;omega)
   exact frame.trans (entries j hj)
 · intro i
   have frame:=aoutside (U+i.val) (by left;have h:=i.isLt;omega) (by left;have h:=i.isLt;omega)
   have tfHeap:=toutside (U+i.val) (by left;have h:=i.isLt;omega)
   exact frame.trans (tfHeap.trans (dsource i))
 · intro i hi
   exact (aoutside (images+i) (by left;omega) (by left;omega)).trans (bank i hi)
 · intro z hz
   have af:=aoutside z (by rcases hz with h|h <;> omega) (by rcases hz with h|h <;> omega)
   have tfh:=toutside z (by rcases hz with h|h <;> omega)
   have dfh:=doutside z (by rcases hz with h|h <;> omega)
   exact af.trans (tfh.trans dfh)
 · exact ash.trans (tf.1.trans dsh)
 · exact asr.trans (tf.2.1.trans dsr)
 · exact aout.trans (tf.2.2.1.trans dout)
 · exact aroot.trans (tf.2.2.2.1.trans droot)
 · intro r hr
   have ah:=aframe.natReg r (by omega)
   have th:=tf.2.2.2.2 r (by omega)
   have dh:=df.natReg r (by left;omega)
   have ah':addressed.natReg r=tabled.natReg r:=by
    simpa (disch:=omega) [dfsChild,ready,dfsSetup,atDFS,applyBlock,Op.apply,evalNat,writeNat,next] using ah
   have th':tabled.natReg r=described.natReg r:=by
    simpa (disch:=omega) [child,seeded,xorSetup,atXor,applyBlock,Op.apply,evalNat,writeNat,next] using th
   exact ah'.trans (th'.trans dh)
 · rcases aheader with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
   exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

end
end ExactFourierCircuits.UniformResidualPermutationPreparation
