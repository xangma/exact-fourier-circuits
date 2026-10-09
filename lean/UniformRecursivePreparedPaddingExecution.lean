import UniformRecursivePaddingExecution
import UniformRecursivePreparedPaddingLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingExecution
open UniformMachine UniformRecursivePaddingFrames UniformRecursivePaddingArrays
open UniformFixedNetworkScheduleMachine (Printed Record)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
noncomputable section
theorem execution_prepared (n B U R A F q w r stack depth stackTop reserve saved start:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(f:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q<q*(w+1)+r)(pc:s.pc=P.address .paddingInit)
 (parent:Parent (q*(w+1)+r) q A F r stack depth s)
 (savedHeader:s.natReg 2865=saved)(destHeader:s.natReg 2854=start)(countHeader:s.natReg 2855=R-start)
 (pointer:s.natHeap (F-2)=some U)
 (printed:Printed U ((record w).withColumns q).data s)
 (present:Present A R (2^(q*(w+1)+r)) f s)(startBound:start ≤ R)
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r<w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (unitEnd:U+(record w).data.length ≤ F-6)(widthBound:(w+1)+1 ≤ B)
 (arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)(poolEnd:F+5*2^(q*(w+1)+r) ≤ B)
 (square:(2^(q*(w+1)+r))^2 ≤ B)(low:6 ≤ F)(dataBase:3 ≤ A)
 (stackRoom:stack+34*(depth+q+2) ≤  stackTop)(recordAbove:stackTop ≤ U)
 (room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)(rolesBound:R ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u ticks,∃g:Fin R→Fin (2^(q*(w+1)+r))→Scalar,∃outPrior,
 BoundedRuns P.program n x B s ticks u∧u.pc=P.address .loop∧u.natReg 2850=saved∧
 Parent (q*(w+1)+r) q A F r stack depth u∧
 Printed U (UniformRecursivePaddingControl.patchRecord (record w) q outPrior).data u∧
 Present A R (2^(q*(w+1)+r)) g u∧values g=action q w r R (remaining R start startBound) (values f)∧
 u.natHeap (F-1)=s.natHeap (F-1)∧u.natHeap (F-2)=s.natHeap (F-2)∧
 (∀z,z<F→(z<stack+34*depth∨stackTop ≤ z)→z≠U+1→z≠U+3→
  z≠F-6→z≠F-5→z≠F-4→z≠F-3→u.natHeap z=s.natHeap z)∧
 (∀z,z<F→(z<A∨A+R*2^(q*(w+1)+r) ≤ z)→u.scalarHeap z=s.scalarHeap z)∧
 UniformBinaryCStageMachine.Constants u∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs∧
 ticks ≤ (R-start)*(roleCost q w r cost+6)+21 ∧ (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have endBound:start+(R-start) ≤ B:=by omega
 obtain ⟨a,init,ap,mode,savedVal,current,endpoint,ifr⟩:=UniformRecursivePaddingControl.init_execution
  n B F saved start (R-start) x s pc parent.frontier parent.one savedHeader destHeader countHeader low bound code endBound
 have ak:a.natReg 5300=q*(w+1)+r:=(UniformRecursivePaddingFragments.init_bits
  n B F saved start (R-start) x s a pc parent.frontier parent.one savedHeader destHeader countHeader low bound code endBound init).trans parent.nativeBits
 have pa:=parent.padding ifr ak
 have ma:Metadata F U saved start R a:=by
  refine ⟨mode,savedVal,current,?_,?_⟩
  · simpa only[Nat.add_sub_of_le startBound] using endpoint
  · exact (ifr.natHeap _ (by simp only[List.mem_cons,List.mem_nil_iff,or_false];omega)).trans pointer
 have printA:Printed U (UniformRecursivePaddingControl.patchRecord (record w) q 0).data a:=by
  rw[←record_columns]
  intro j hj
  have len:((record w).withColumns q).data.length=(record w).data.length:=by rw[Record.data_length,Record.data_length];rfl
  have less:U+j<F-6:=by rw[len] at hj;omega
  rw[ifr.natHeap _ (by simp only[List.mem_cons,List.mem_nil_iff,or_false];omega)]
  exact printed j hj
 have presentA:Present A R (2^(q*(w+1)+r)) f a:=by
  intro i z;rw[ifr.scalarHeap];exact present i z
 have ca:UniformBinaryCStageMachine.Constants a:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  rw[ifr.scalarHeap];exact constants
 have vis:UniformRecursiveResidualDirectionLoop.Visit R start (remaining R start startBound):=
  UniformRecursiveResidualDirectionLoop.indices_visit R start (R-start) (by omega)
 obtain ⟨u,ut,g,outPrior,run,up,cursor,pu,printU,gp,gv,un,ush,cu,uro,uo,time,preparedG⟩:=UniformRecursivePaddingLoop.loop_prepared
  n B U R A F q w r stack depth stackTop reserve saved 0 start cost x (remaining R start startBound) vis a f
  childIH smaller ap pa ma printA presentA qp m2 rp fits unitEnd widthBound arrayEnd poolEnd square low dataBase
  stackRoom recordAbove room rolesBound ca init.final_bound code
 refine ⟨u,11+ut,g,outPrior,init.trans run,up,cursor,pu,printU,gp,gv,?_,?_,?_,?_,cu,
  uro.trans ifr.roots,uo.trans ifr.outputs,?_,preparedG⟩
 · have len:=UniformRecursivePaddingRole.record_length w
   rw[un (F-1) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega),
    ifr.natHeap _ (by simp only[List.mem_cons,List.mem_nil_iff,or_false];omega)]
 · have len:=UniformRecursivePaddingRole.record_length w
   rw[un (F-2) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega),
    ifr.natHeap _ (by simp only[List.mem_cons,List.mem_nil_iff,or_false];omega)]
 · intro z hz away a b c d e f
   exact (un z hz away a b e).trans (ifr.natHeap z (by simp only[List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨c,d,e,f⟩))
 · intro z hz away
   exact (ush z hz away).trans (congrFun ifr.scalarHeap z)
 · rw[remaining_length] at time
   omega
end
end ExactFourierCircuits.UniformRecursivePaddingExecution
