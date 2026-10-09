import UniformRecursiveSmallPrologue
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSmallBase
open UniformMachine UniformAssembly UniformBinaryTensorCoordinates
open UniformTensorMonomialMachine (setPC)
namespace T
export UniformBinaryBatchCMachine (program arrayBase arrayCost transformed Changed Frame)
end T
noncomputable section

/-- Exact54-cell ordinary tensor batch, placed in the caller's real program.
Its terminal halt is the charged jump to the finish branch. -/
theorem batch_embedded (main:Program)(start exit n B k count A:ℕ)(x:Fin n→ℂ)
 (link:CodeAt T.program main start exit)(s:State)(v:Fin count→Fin (2^k)→Scalar)
 (pc:s.pc=start)(bits:s.natReg 4900=k)(arrays:s.natReg 4901=count)(base:s.natReg 4902=A)
 (size:s.natReg 4903=2^k)
 (data:∀w z,s.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z))
 (heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:start+T.program.length≤B)(ret:exit≤B)
 (extent:A+count*2^k≤B):∃u,
 BoundedRuns main n x B s (count*T.arrayCost k+5) u ∧u.pc=exit ∧
 (∀w z,u.scalarHeap (T.arrayBase A k w.val+z.val)=some (T.transformed k (v w) z)) ∧
 (∀w z,(u.scalarHeap (T.arrayBase A k w.val+z.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
 T.Frame A (count*2^k) s u ∧UniformBinaryCStageMachine.Constants u:=by
 have localCode:T.program.length≤B:=(Nat.le_add_left _ _).trans code
 have small:54≤B:=by simpa only [UniformBinaryBatchCMachine.program_length] using localCode
 obtain ⟨u,run,out,values,frame,con,_⟩:=UniformBinaryBatchCMachine.execution n B k count A x
  (setPC s 0) v rfl bits arrays base size data heapBase constants small extent
  (changePC_bound B s 0 bound (by omega))
 have placed:=UniformBoundedAssembly.boundedExecution_placed link code ret run
 have begin:UniformAssembly.placed start (setPC s 0)=s:=by
  change setPC s start=s;rw [←pc];cases s;rfl
 rw [begin] at placed
 exact ⟨setPC u exit,placed,rfl,out,values,
  ⟨frame.natHeap,frame.outputs,frame.roots,frame.natReg,frame.scalarReg,frame.scalarHeap⟩,con⟩

def Changed (j:ℕ):Prop :=UniformRecursiveSmallPrologue.Changed j∨T.Changed j
structure Frame (A volume:ℕ)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
 scalarReg:∀j,8≤j→u.scalarReg j=s.scalarReg j
 scalarHeap:∀a,a<A∨A+volume≤a→u.scalarHeap a=s.scalarHeap a
lemma compose_frame {A volume:ℕ}{s t u:State}(a:UniformRecursiveSmallPrologue.Frame s t)
 (b:T.Frame A volume t u)(pc:ℕ):Frame A volume s (setPC u pc):=by
 refine ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,?_,?_,?_⟩
 · intro j hj
   exact (b.natReg j (fun h=>hj (Or.inr h))).trans (a.natReg j (fun h=>hj (Or.inl h)))
 · intro j hj;exact (b.scalarReg j hj).trans (congrFun a.scalarReg j)
 · intro adr h;exact (b.scalarHeap adr h).trans (congrFun a.scalarHeap adr)

lemma finish_generic (main:Program)(loc root child n B depth:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:main[loc]?=some (.branchLT 4151 4153 root child))
 (pc:s.pc=loc)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (bound:WordBound B s)(rootBound:root≤B)(childBound:child≤B):
 BoundedRuns main n x B s 1 (setPC s (if depth=0 then root else child)):=by
 have eq:(depth<1)=(depth=0):=propext (by omega)
 exact .next bound (by simp only [step,pc,atCode,dp,one,eq];rfl)
  (.refl (changePC_bound B s _ bound (by split <;> assumption)))

def baseTicks (count k:ℕ):ℕ :=count*T.arrayCost k+12

/-- Continuous ready-test, header installation, full batch, and true stack
branch. Only raw parent headers/data and ordinary bounds are premises. -/
theorem execution_generic (main:Program)(ready setup base large finish root child threshold count n B k A depth:ℕ)
 (x:Fin n→ℂ)(s:State)(v:Fin count→Fin (2^k)→Scalar)
 (literalCode:main[ready]?=some (.natLiteral 4177 threshold))
 (branchCode:main[ready+1]?=some (.branchLT 4120 4177 setup large))
 (setupCode:UniformNatBlockMachine.BlockAt (UniformRecursiveSmallPrologue.setupOps count) main setup)
 (follow:setup+4=base)(batchLink:CodeAt T.program main base finish)
 (finishCode:main[finish]?=some (.branchLT 4151 4153 root child))
 (pc:s.pc=ready)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(dataBase:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(dp:s.natReg 4151=depth)(small:k<threshold)
 (data:∀w z,s.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z))
 (heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (readyEnd:ready+2≤B)(setupEnd:setup+4≤B)(batchEnd:base+T.program.length≤B)
 (finishBound:finish≤B)(rootBound:root≤B)(childBound:child≤B)(thresholdBound:threshold≤B)
 (countBound:count≤B)(extent:A+count*2^k≤B):∃u,
 BoundedRuns main n x B s (baseTicks count k) u ∧
 u.pc=(if depth=0 then root else child) ∧
 (∀w z,u.scalarHeap (T.arrayBase A k w.val+z.val)=some (T.transformed k (v w) z)) ∧
 (∀w z,(u.scalarHeap (T.arrayBase A k w.val+z.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
 Frame A (count*2^k) s u ∧UniformBinaryCStageMachine.Constants u:=by
 obtain ⟨t,prologue,tp,tk,tw,ta,tv,sf⟩:=UniformRecursiveSmallPrologue.execution main ready setup base large
  threshold count n B k A (2^k) x s literalCode branchCode setupCode follow pc one bits dataBase size small
  bound readyEnd setupEnd thresholdBound countBound
 have td:∀w z,t.scalarHeap (T.arrayBase A k w.val+z.val)=some (v w z):=by
  intro w z;rw [sf.scalarHeap];exact data w z
 have tc:UniformBinaryCStageMachine.Constants t:=by
  rcases constants with ⟨a,b⟩;exact ⟨by rw [sf.scalarHeap];exact a,by rw [sf.scalarHeap];exact b⟩
 obtain ⟨u,run,up,out,values,fr,con⟩:=batch_embedded main base finish n B k count A x batchLink
  t v tp tk tw ta tv td heapBase tc prologue.final_bound batchEnd finishBound extent
 have keep (j:ℕ)(hj:¬Changed j):u.natReg j=s.natReg j:=
  (fr.natReg j (fun h=>hj (Or.inr h))).trans (sf.natReg j (fun h=>hj (Or.inl h)))
 have dkeep:u.natReg 4151=depth:=(keep _ (by
  unfold Changed UniformRecursiveSmallPrologue.Changed T.Changed UniformBinaryTensorCMachine.Changed;omega)).trans dp
 have okeep:u.natReg 4153=1:=(keep _ (by
  unfold Changed UniformRecursiveSmallPrologue.Changed T.Changed UniformBinaryTensorCMachine.Changed;omega)).trans one
 have last:=finish_generic main finish root child n B depth x u finishCode up dkeep okeep
  run.final_bound rootBound childBound
 refine ⟨setPC u (if depth=0 then root else child),?_,rfl,out,values,compose_frame sf fr _,con⟩
 convert (prologue.trans run).trans last using 1
 unfold baseTicks
 omega

lemma baseTicks_bound {k threshold:ℕ}(small:k<threshold)(count:ℕ):
 baseTicks count k≤(36*threshold+16)*(count*2^k)+12:=by
 have h:=UniformBinaryBatchCMachine.base_cost_bound small count
 unfold baseTicks
 omega

end
end ExactFourierCircuits.UniformRecursiveSmallBase
