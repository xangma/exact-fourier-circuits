import UniformRecursiveSmallExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSmallEntry
open UniformMachine UniformBinaryTensorCoordinates
namespace P
export UniformRecursiveSavingProgram (program address threshold)
end P
namespace S
export UniformRecursiveSmallBase (baseTicks Frame)
end S
namespace T
export UniformBinaryBatchCMachine (arrayBase transformed)
end T
noncomputable section

lemma runs_same_end {p:Program}{n t:ℕ}{x:Fin n→ℂ}{s u v:State}
 (h:Runs p n x s t u)(h':Runs p n x s t v):u=v:=by
 induction h generalizing v with
 | refl s=>cases h';rfl
 | next hs tail ih=>
   cases h' with
   | next hv tv=>rw [hs] at hv;cases hv;exact ih tv

lemma nonroot_stack (n B k A depth:ℕ)(x:Fin n→ℂ)(s t:State)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(dp:s.natReg 4151=depth)
 (bound:WordBound B s)(code:P.program.length≤B)(nonzero:depth≠0)
 (first:BoundedRuns P.program n x B s 4 t):t.natReg 4150=s.natReg 4150:=by
 have codeEntry:4≤B:=by
  have h:=(UniformRecursiveSavingExecution.part_bound .entry).trans code
  change 0+4≤B at h;omega
 have readyBound:=UniformRecursiveSmallExecution.start_bound .readyEntry B code
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have ab:A≤B:=by have h:=bound.2.1 4121;rwa [base] at h
 have safe:UniformNatBlockMachine.readable UniformRecursiveSavingExecution.entryOps s∧
  UniformNatBlockMachine.peak UniformRecursiveSavingExecution.entryOps s≤B:=by
  simp [UniformRecursiveSavingExecution.entryOps,UniformNatBlockMachine.readable,UniformNatBlockMachine.peak,
   UniformNatBlockMachine.Op.readable,UniformNatBlockMachine.Op.peak,UniformNatBlockMachine.Op.apply,
   evalNat,writeNat,next,bits,base];omega
 have run:=UniformNatBlockMachine.block_runs UniformRecursiveSavingExecution.entryOps P.program 0 n B x s
  UniformRecursiveSavingExecution.entry_code pc bound (by change 0+3≤B;omega) safe.1 safe.2
 let boot:=UniformNatBlockMachine.applyBlock UniformRecursiveSavingExecution.entryOps s
 let u:=UniformTensorMonomialMachine.setPC boot (P.address .readyEntry)
 have bpc:boot.pc=3:=by simp [boot,UniformRecursiveSavingExecution.entryOps,UniformNatBlockMachine.applyBlock,UniformNatBlockMachine.Op.apply,writeNat,next,pc]
 have bd:boot.natReg 4151=depth:=by simp [boot,UniformRecursiveSavingExecution.entryOps,UniformNatBlockMachine.applyBlock,UniformNatBlockMachine.Op.apply,evalNat,writeNat,next,dp]
 have one:boot.natReg 4153=1:=by simp [boot,UniformRecursiveSavingExecution.entryOps,UniformNatBlockMachine.applyBlock,UniformNatBlockMachine.Op.apply,evalNat,writeNat,next]
 have branch:BoundedRuns P.program n x B boot 1 u:=.next run.final_bound
  (by simp [step,bpc,UniformRecursiveSavingExecution.entry_branch,bd,one,show ¬depth<1 by omega,u,UniformTensorMonomialMachine.setPC])
  (.refl (UniformMachine.changePC_bound B boot _ run.final_bound readyBound))
 have same:t=u:=runs_same_end first.runs (by simpa only [UniformRecursiveSavingExecution.entryOps,List.length_cons,List.length_nil] using (run.trans branch).runs)
 rw [same]
 simp [u,boot,UniformTensorMonomialMachine.setPC,UniformRecursiveSavingExecution.entryOps,UniformNatBlockMachine.applyBlock,UniformNatBlockMachine.Op.apply,evalNat,writeNat,next]

/-- Real entry (including charged root-stack allocation when applicable),
followed by the proved small branch. Neither installed batch headers nor a
ready-entry state is a premise. Both complete frames are retained explicitly. -/
theorem execution (n B k A F depth:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(size:s.natReg 4122=2^k)
 (frontier:s.natReg 4123=F)(dp:s.natReg 4151=depth)(small:k<P.threshold)
 (data:∀w z,s.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z))
 (heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (code:P.program.length≤B)(thresholdBound:P.threshold≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B)(stackEnd:F+34*(k+1)≤B):∃u t,
 BoundedRuns P.program n x B s ((if depth=0 then 10 else 4)+S.baseTicks UniformRecursiveSelfCallMachine.W k) u ∧
 u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
 (∀w z,u.scalarHeap (T.arrayBase A k w.val+z.val)=some (T.transformed k (v w) z)) ∧
 (∀w z,(u.scalarHeap (T.arrayBase A k w.val+z.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
 UniformRecursiveSavingExecution.EntryFrame s t ∧S.Frame A (UniformRecursiveSelfCallMachine.W*2^k) t u ∧
 UniformBinaryCStageMachine.Constants u ∧u.natReg 4151=depth ∧
 u.natReg 4123=(if depth=0 then F+34*(k+1) else F) ∧
 (depth=0→u.natReg 4150=F) ∧(depth≠0→u.natReg 4150=s.natReg 4150):=by
 obtain ⟨t,first,tp,_,_,tk,ta,tv,td,tone,tf,ts,ef⟩:=UniformRecursiveSavingExecution.entry_execution
  n B k A (2^k) F depth x s pc bits base size frontier dp bound code stackEnd
 have tc:UniformBinaryCStageMachine.Constants t:=by
  rcases constants with ⟨a,b⟩;exact ⟨by rw [ef.scalarHeap];exact a,by rw [ef.scalarHeap];exact b⟩
 have present:∀w z,t.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z):=by
  intro w z;rw [ef.scalarHeap];exact data w z
 obtain ⟨u,last,up,out,values,frame,con⟩:=UniformRecursiveSmallExecution.execution n B k A depth x t v
  tp tone tk ta tv td small present heapBase tc first.final_bound code thresholdBound countBound extent
 have keep (j:ℕ)(hj:¬UniformRecursiveSmallBase.Changed j):u.natReg j=t.natReg j:=frame.natReg j hj
 have stack:=UniformRecursiveSmallExecution.frame_stack frame
 refine ⟨u,t,first.trans last,up,out,values,ef,frame,con,stack.2.1.trans td,?_,?_,?_⟩
 · exact (keep _ (by unfold UniformRecursiveSmallBase.Changed UniformRecursiveSmallPrologue.Changed UniformBinaryBatchCMachine.Changed UniformBinaryTensorCMachine.Changed;omega)).trans tf
 · intro zero;exact stack.1.trans (ts zero)
 · intro nonzero
   exact stack.1.trans (nonroot_stack n B k A depth x s t pc bits base dp bound code nonzero
    (by simpa only [nonzero,ite_false] using first))

end
end ExactFourierCircuits.UniformRecursiveSmallEntry
