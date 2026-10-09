import UniformRecursivePaddingRole
import UniformRecursivePaddingArrays
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingLoop
open UniformMachine UniformRecursivePaddingFrames UniformRecursivePaddingArrays
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
noncomputable section

theorem loop (n B U R A F q w r stack depth stackTop reserve saved prior index:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(L:List (Fin R))
 (vis:UniformRecursiveResidualDirectionLoop.Visit R index L)
 (s:State)(f:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q<q*(w+1)+r)(pc:s.pc=P.address .paddingTest)
 (parent:Parent (q*(w+1)+r) q A F r stack depth s)
 (metadata:Metadata F U saved index R s)
 (printed:Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data s)
 (present:Present A R (2^(q*(w+1)+r)) f s)
 (qp:1≤q)(m2:2≤w+1)(rp:r<w+1)(fits:ExplicitSeedBudget.roleBits≤q*w+r)
 (unitEnd:U+(record w).data.length≤F-6)(widthBound:(w+1)+1≤B)
 (arrayEnd:A+R*2^(q*(w+1)+r)≤F)(poolEnd:F+5*2^(q*(w+1)+r)≤B)
 (square:(2^(q*(w+1)+r))^2≤B)(low:6≤F)(dataBase:3≤A)
 (stackRoom:stack+34*(depth+q+2)≤ stackTop)(recordAbove:stackTop≤U)
 (room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q≤B)(rolesBound:R≤B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length≤B):
 ∃u ticks,∃g:Fin R→Fin (2^(q*(w+1)+r))→Scalar,∃outPrior,
 BoundedRuns P.program n x B s ticks u∧u.pc=P.address .loop∧u.natReg 2850=saved∧
 Parent (q*(w+1)+r) q A F r stack depth u∧
 Printed U (UniformRecursivePaddingControl.patchRecord (record w) q outPrior).data u∧
 Present A R (2^(q*(w+1)+r)) g u∧values g=action q w r R L (values f)∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠U+1→z≠U+3→z≠F-4→u.natHeap z=s.natHeap z)∧
 (∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r)≤z)→u.scalarHeap z=s.scalarHeap z)∧
 UniformBinaryCStageMachine.Constants u∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs∧
 ticks≤L.length*(roleCost q w r cost+6)+10:=by
 induction vis generalizing s f prior with
 | done=>
  obtain ⟨a,test,ap,_,_,tf⟩:=UniformRecursivePaddingControl.test_execution n B F R R x s pc
   parent.frontier parent.one low metadata.current metadata.endpoint bound code
  have ap':a.pc=P.address .paddingFinish:=by simpa only[Nat.lt_irrefl,ite_false] using ap
  have ak:a.natReg 5300=q*(w+1)+r:=(UniformRecursivePaddingFragments.test_bits n B F R R x s a pc
   parent.frontier parent.one metadata.current metadata.endpoint low bound code test).trans parent.nativeBits
  have pa:=parent.padding tf ak
  have ma:=metadata.transport (fun z _=>tf.natHeap z (by simp))
  obtain ⟨u,finish,up,cursor,ff⟩:=UniformRecursivePaddingControl.finish_execution n B F saved x a ap'
   pa.frontier low ma.saved test.final_bound code
  have uk:u.natReg 5300=q*(w+1)+r:=(UniformRecursivePaddingFragments.finish_bits n B F saved x a u ap'
   pa.frontier ma.saved low test.final_bound code finish).trans pa.nativeBits
  refine ⟨u,6+4,f,prior,test.trans finish,up,cursor,pa.padding ff uk,?_,?_,rfl,?_,?_,?_,?_,?_,by simp⟩
  · intro j hj;rw[ff.natHeap _ (by simp),tf.natHeap _ (by simp)];exact printed j hj
  · intro i z;rw[ff.scalarHeap,tf.scalarHeap];exact present i z
  · intro z _ _ _ _ _;rw[ff.natHeap _ (by simp),tf.natHeap _ (by simp)]
  · intro z _ _;rw[ff.scalarHeap,tf.scalarHeap]
  · unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw[ff.scalarHeap,tf.scalarHeap];exact constants
  · exact ff.roots.trans tf.roots
  · exact ff.outputs.trans tf.outputs
 | step j tail visit ih=>
  obtain ⟨a,test,ap,dst,_,tf⟩:=UniformRecursivePaddingControl.test_execution n B F j.val R x s pc
   parent.frontier parent.one low metadata.current metadata.endpoint bound code
  have ap':a.pc=P.address .paddingPatch:=by simpa only[j.isLt,ite_true] using ap
  have ak:a.natReg 5300=q*(w+1)+r:=(UniformRecursivePaddingFragments.test_bits n B F j.val R x s a pc
   parent.frontier parent.one metadata.current metadata.endpoint low bound code test).trans parent.nativeBits
  have pa:=parent.padding tf ak
  have ma:=metadata.transport (fun z _=>tf.natHeap z (by simp))
  have printA:Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data a:=by
   intro z hz;rw[tf.natHeap _ (by simp)];exact printed z hz
  have dataA:∀z,a.scalarHeap (A+j.val*2^(q*(w+1)+r)+z.val)=some (f j z):=by
   intro z;rw[tf.scalarHeap];exact present j z
  have ca:UniformBinaryCStageMachine.Constants a:=by
   unfold UniformBinaryCStageMachine.Constants at constants ⊢
   rw[tf.scalarHeap];exact constants
  obtain ⟨b,dt,Y,role,bp,pb,mb,printB,yp,yv,bn,bsh,cb,br,bo,bt⟩:=UniformRecursivePaddingRole.execution
   n B U R A F q w r stack depth stackTop reserve saved R prior cost x j a (f j) childIH smaller ap' pa ma dst printA dataA
   qp m2 rp fits unitEnd widthBound arrayEnd poolEnd square low dataBase stackRoom recordAbove room
   ((Nat.succ_le_of_lt j.isLt).trans rolesBound) ca test.final_bound code
  let h:Fin R→Fin (2^(q*(w+1)+r))→Scalar:=Function.update f j Y
  have presentA:Present A R (2^(q*(w+1)+r)) f a:=by
   intro i z;rw[tf.scalarHeap];exact present i z
  have presentB:Present A R (2^(q*(w+1)+r)) h b:=present_update j Y presentA arrayEnd yp bsh
  have val:values h=applyRole q w r R j (values f):=values_update j f Y yv
  obtain ⟨u,ut,g,outPrior,ur,up,cursor,pu,printU,gp,gv,un,ush,cu,uro,uo,ub⟩:=ih j.val b h bp pb mb printB presentB cb role.final_bound
  refine ⟨u,6+dt+ut,g,outPrior,(test.trans role).trans ur,up,cursor,pu,printU,gp,?_,?_,?_,cu,
   uro.trans (br.trans tf.roots),uo.trans (bo.trans tf.outputs),?_⟩
  · change values g=action q w r R tail (applyRole q w r R j (values f))
    rw[←val];exact gv
  · intro z hz away a b c
    exact (un z hz away a b c).trans ((bn z hz away a b c).trans (tf.natHeap z (by simp)))
  · intro z hz away
    have outside:z<A+j.val*2^(q*(w+1)+r)∨A+(j.val+1)*2^(q*(w+1)+r)≤z:=by
     have mul: (j.val+1)*2^(q*(w+1)+r)≤R*2^(q*(w+1)+r):=Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
     omega
    exact (ush z hz away).trans ((bsh z hz outside).trans (congrFun tf.scalarHeap z))
  · simp only[List.length_cons,Nat.succ_mul]
    omega
end
end ExactFourierCircuits.UniformRecursivePaddingLoop
