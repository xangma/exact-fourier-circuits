import UniformRecursiveRootExecution
import UniformRecursivePreparedRootPackage

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, PDF pp. 11–12; §3.4, prepared-scalar discussion, p. 18.
The numerical root execution is strengthened with dependency tags. Tags and concrete stack layouts are implementation bookkeeping, without a separate numbered paper lemma.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRootExecution
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformRecursiveNodePreparation
open UniformRecursiveChildInduction (cost)
open UniformRecursiveRootPackage (PreparedResult)
namespace P
export UniformRecursiveSavingProgram (program address threshold seedLength unitLength seedPrinterLength unitPrinterLength size)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable section

/- Paper: Implementation tag proof for the direct base branch of Theorem 2.6, p. 11; numerical action and prepared status are proved for the same terminal state. -/
lemma small_execution_prepared (n B k A F:ℕ)(x:Fin n→ℂ)(input:Fin W→Fin (2^k)→Scalar)(s:State)
 (small:k < P.threshold)(pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(frontier:s.natReg 4123=F)(dp:s.natReg 4151=0)
 (data:∀i z,s.scalarHeap (A+i.val*2^k+z.val)=some (input i z))
 (heapBase:3 ≤ A)(extent:A+W*2^k ≤ F)(code:P.program.length ≤ B)
 (room:F+34*(k+1)+R.reserve*(k+1)*2^k ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):PreparedResult n B k A F cost x input s:=by
 have stackEnd:F+34*(k+1) ≤ B:=by omega
 have fb:F ≤ B:=by omega
 have rb:R.reserve ≤ B:=UniformRecursiveBodyGeometry.reserve_le room
 have countBound:W ≤ B:=by
  have h:=Nat.mul_le_mul_left W (show 1 ≤ 2^k from Nat.two_pow_pos k)
  simp only [Nat.mul_one] at h
  omega
 obtain ⟨u,t,run,up,out,values,ef,frame,con,_,_,_,_⟩:=UniformRecursiveSmallEntry.execution
  n B k A F 0 x s input pc bits base size frontier dp small data heapBase constants bound code
  (UniformRecursiveReserve.threshold_fit.trans rb) countBound (extent.trans fb) stackEnd
 have runs:BoundedRuns P.program n x B s (10+UniformRecursiveSmallBase.baseTicks W k) u:=run
 have stop:=UniformRecursiveRootPackage.root_if u.pc _ _ up
 apply UniformRecursiveRootPackage.finalize_prepared n B k A F cost x input s u _ runs stop
 · intro i z
   change (u.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k i.val+z.val)).isSome=true
   rw [out i z];rfl
 · exact values
 · intro z _;rw [frame.natHeap,ef.natHeap]
 · intro z _ away;exact (frame.scalarHeap z away).trans (congrFun ef.scalarHeap z)
 · exact con
 · exact frame.outputs.trans ef.outputs
 · exact frame.roots.trans ef.roots
 · exact small_cost k small
 · intro prep i z
   change (u.scalarHeap (UniformBinaryBatchCMachine.arrayBase A k i.val+z.val)).map Scalar.dependent=some false
   rw [out i z]
   exact congrArg some (UniformRecursivePreparedValues.batch (input i) (prep i) z)

/-- The root large branch computes and allocates its actual stack before the
same whole-node execution. Strict child executions are supplied by the proved
well-founded theorem, not by a caller premise. -/
/- Paper: Theorem 2.6, pp. 11–12, with the additional prepared-input invariant. Strict recursive calls come from smaller_prepared, rather than a caller action premise. -/
lemma large_execution_prepared (n B A F q rest:ℕ)(x:Fin n→ℂ)(input:Fin W→Fin (2^(q*m+rest))→Scalar)(s:State)
 (large:P.threshold ≤ q*m+rest)(qp:1 ≤ q)(rp:rest < m)(smaller:q < q*m+rest)
 (pc:s.pc=0)(bits:s.natReg 4120=q*m+rest)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^(q*m+rest))(frontier:s.natReg 4123=F)(dp:s.natReg 4151=0)
 (data:∀i z,s.scalarHeap (A+i.val*2^(q*m+rest)+z.val)=some (input i z))
 (heapBase:3 ≤ A)(extent:A+W*2^(q*m+rest) ≤ F)(code:P.program.length ≤ B)
 (room:F+34*(q*m+rest+1)+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
 (square:(2^(q*m+rest))^2 ≤ B)(constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 PreparedResult n B (q*m+rest) A F cost x input s:=by
 let childFrontier:=F+34*(q*m+rest+1)
 have stackEnd:childFrontier ≤ B:=by dsimp only [childFrontier];omega
 have incomingRoom:childFrontier+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B:=room
 have rb:R.reserve ≤ B:=UniformRecursiveBodyGeometry.reserve_le incomingRoom
 obtain ⟨t,entry,tp,nk,na,tk,ta,tv,td,oneHeader,tf,ts,ef⟩:=UniformRecursiveSavingExecution.entry_execution
  n B (q*m+rest) A (2^(q*m+rest)) F 0 x s pc bits base size frontier dp bound code stackEnd
 have entry10:BoundedRuns P.program n x B s 10 t:=entry
 have current:t.natReg 4123=childFrontier:=tf
 have tStack:t.natReg 4150=F:=ts rfl
 have geom:=UniformRecursiveBodyGeometry.geometry B A childFrontier P.seedLength P.unitLength q rest F 0 childFrontier R.reserve
  qp rp smaller UniformRecursiveReserve.payload_fit UniformRecursiveReserve.width_fit incomingRoom
  (by dsimp only [childFrontier];omega) heapBase (by dsimp only [childFrontier];omega) square code
 have incoming:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest)) input t:=by
  intro i z;rw [ef.scalarHeap];exact data i z
 have ct:UniformBinaryCStageMachine.Constants t:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  rw [ef.scalarHeap];exact constants
 obtain ⟨u,ticks,g,run,up,out,values,_,_,nh,sh,cu,roots,outputs,ticksBound,preparedG⟩:=UniformRecursiveLargeNode.execution_prepared
  n B childFrontier P.seedLength P.unitLength A q rest F 0 childFrontier R.reserve F cost x t input rfl rfl
  (UniformRecursiveChildInduction.smaller_prepared (q*m+rest) n B F childFrontier x) geom large
  (UniformRecursiveReserve.threshold_fit.trans rb) tp tk ta tv current na nk tStack td oneHeader incoming (le_refl _)
  (by dsimp only [childFrontier];omega) (UniformRecursiveReserve.literals_fit.trans rb) ct entry10.final_bound
 have stop:=UniformRecursiveRootPackage.root_if u.pc _ _ up
 apply UniformRecursiveRootPackage.finalize_prepared n B (q*m+rest) A F cost x input s u (10+ticks) (entry10.trans run) stop
 · intro i z;rw [out i z];rfl
 · intro i z;rw [out i z,Option.map_some];exact congrArg some (congrFun (values i) z)
 · intro z hz
   exact (nh z hz (Or.inl (by simpa only [Nat.mul_zero,Nat.add_zero] using hz))).trans (congrFun ef.natHeap z)
 · intro z hz away;exact (sh z hz away).trans (congrFun ef.scalarHeap z)
 · exact cu
 · exact outputs.trans ef.outputs
 · exact roots.trans ef.roots
 · exact UniformRecursiveRootPackage.cap ticks _ _ _ ticksBound
    (UniformRecursiveTypedLargeCost.large_node_bound q rest qp rp large)
 · intro prep i z;rw [out i z];exact congrArg some (preparedG prep i z)

/-- The complete actual corrected recursive saving program, for every binary
exponent. Only physically supplied raw headers/data/constants and ordinary
allocation/word bounds are assumptions; no produced tape or child action is. -/
theorem execution_prepared (n B k A F:ℕ)(x:Fin n→ℂ)(input:Fin W→Fin (2^k)→Scalar)(s:State)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(size:s.natReg 4122=2^k)
 (frontier:s.natReg 4123=F)(dp:s.natReg 4151=0)
 (data:∀i z,s.scalarHeap (A+i.val*2^k+z.val)=some (input i z))
 (heapBase:3 ≤ A)(extent:A+W*2^k ≤ F)(code:P.program.length ≤ B)
 (room:F+34*(k+1)+R.reserve*(k+1)*2^k ≤ B)(square:(2^k)^2 ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):PreparedResult n B k A F cost x input s:=by
 by_cases small:k < P.threshold
 · exact small_execution_prepared n B k A F x input s small pc bits base size frontier dp data heapBase extent code room constants bound
 · have large:P.threshold ≤ k:=by omega
   obtain ⟨qp,qlt,rp,form⟩:=UniformRecursiveSavingExecution.recursive_geometry k large
   generalize hq:k/ExplicitSeedBudget.m=q at qp qlt form
   generalize hr:k%ExplicitSeedBudget.m=rest at rp form
   have decomposition:k=q*m+rest:=form
   rw [decomposition] at bits
   clear form
   subst k
   exact large_execution_prepared n B A F q rest x input s large qp rp qlt pc bits base size frontier dp data heapBase extent code room square constants bound
end
end ExactFourierCircuits.UniformRecursiveRootExecution
