import UniformRecursiveResidualRoleSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualRecord
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformNativeScheduleMatrix
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualRoleSemantics (replaceRole roleMap)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section

def arrayValues (q rest:ℕ)(f:Fin W→Fin (2^(q*m+rest))→Scalar):
 Fin (W*2^(q*m+rest))→ℂ:=RoleWords.arrayValues (q*m+rest) (fun i z=>(f i z).value)

/-- Actual opcode0 consumes its original printed record and arbitrary fullW data.
The semantic conclusion is the exact typed schedule instruction, including
padding-role placement and high spectators. Only strictly smaller real bodies
remain as the well-founded induction hypothesis. -/
theorem execution (n B T tapeEnd A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(a:Invocation){old new:FramedScheduleWords.Label seedWidth}
 (role:Fin (fixedBlock a).width)(edge:FramedScheduleWords.NestedEdge old new)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (smaller:q < q*m+rest)(pc:s.pc=P.address .loop)
 (h:UniformRecursiveResidualEdge.Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q (.macro a (.edge old new role edge))).data s)
 (data:Present A W (2^(q*m+rest)) f s)(qp:1 ≤ q)(rp:rest < m)
 (fits:ExplicitSeedBudget.roleBits ≤ q*(m-1)+rest)
 (recordEnd:T+(Instruction.record q (.macro a (.edge old new role edge))).data.length ≤ F-6)
 (widthBound:m+1 ≤ B)(arrayEnd:A+W*2^(q*m+rest) ≤ F)
 (poolEnd:F+5*2^(q*m+rest) ≤ B)(square:(2^(q*m+rest))^2 ≤ B)
 (low:6 ≤ F)(dataBase:3 ≤ A)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ T)
 (room:F+5*2^(q*m+rest)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u ticks,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .loop ∧
 UniformRecursiveResidualEdge.Parent (q*m+rest) q A F
  (T+(Instruction.record q (.macro a (.edge old new role edge))).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest (.macro a (.edge old new role edge))).mulVec (arrayValues q rest f) ∧
 (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→z≠F-6→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 ticks ≤ edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
  (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q (.macro a (.edge old new role edge)))) cost+53:=by
 let emb:Fin (fixedBlock a).width↪Fin W:=(fixedBlock a).embedding.trans roleMap
 have recordEq : macroRecord q emb (.edge old new role edge)=Instruction.record q (.macro a (.edge old new role edge)):= by
  exact UniformRecursiveResidualRoleSemantics.padded_record q a role edge
 have sameLength:=congrArg (fun z:Record=>z.data.length) recordEq
 have limit:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F-6:=
  (congrArg (Nat.add T) sameLength).le.trans recordEnd
 have bank:Printed T (macroRecord q emb (.edge old new role edge)).data s:=by rw [recordEq];exact printed
 have m2:2 ≤ (m-1)+1:=by norm_num [m,ExplicitSeedBudget.m]
 obtain ⟨u,ticks,Y,run,up,uh,yp,yv,nh,sh,cu,roots,outputs,time⟩:=UniformRecursiveResidualEdge.execution
  n B T tapeEnd (fixedBlock a).width W A F q (m-1) rest stack depth stackTop reserve
  cost x emb role edge s (f (emb role)) childIH smaller pc h metadata live bank (data (emb role))
  qp m2 rp fits limit widthBound arrayEnd poolEnd square low dataBase stackRoom stackEnd room constants bound code
 change UniformRecursiveResidualEdge.Parent (q*m+rest) q A F
  (T+(macroRecord q emb (.edge old new role edge)).data.length) rest stack depth u at uh
 change ticks ≤ edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+53 at time
 change (∀z,z < F→(z < A+(emb role).val*2^(q*m+rest)∨A+((emb role).val+1)*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z) at sh
 let g:=replaceRole (emb role) Y f
 have gp:Present A W (2^(q*m+rest)) g u:=
  UniformRecursiveResidualRoleSemantics.replace_present W (2^(q*m+rest)) A F (emb role) f Y s u data yp arrayEnd sh
 have valueEq : arrayValues q rest g=(semantic q rest (.macro a (.edge old new role edge))).mulVec (arrayValues q rest f):=
  UniformRecursiveResidualRoleSemantics.edge_values q rest a role edge f Y yv
 refine ⟨u,ticks,g,run,up,?_,gp,valueEq,nh,?_,cu,roots,outputs,?_⟩
 · simpa only [sameLength] using uh
 · intro z hz away
   have roleEnd:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*m+rest)) (emb role)
   unfold UniformFixedNetworkShearChildMachine.roleBase at roleEnd
   simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] at sh
   apply sh z hz
   rcases away with before|after
   · left;omega
   · right;omega
 · have sameHead:=congrArg UniformFixedNetworkOpcodeMachine.headCost recordEq
   simpa only [sameHead] using time

end
end ExactFourierCircuits.UniformRecursiveResidualRecord
