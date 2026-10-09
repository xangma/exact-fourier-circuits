import UniformRecursiveResidualEdge
import UniformNativeRecordRoles
import UniformNativeScheduleSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualRoleSemantics
open OAI.ExactFourier UniformMachine
open UniformNativeCopiedInverse UniformNativeResidualSemantics
open UniformNativeScheduleMatrix UniformNativeRecordRoles
noncomputable section

def replaceRole {R V:ℕ}(i:Fin R)(Y:Fin V→Scalar)(f:Fin R→Fin V→Scalar):
 Fin R→Fin V→Scalar:=fun j z=>if j=i then Y z else f j z

lemma replace_present (R V A F:ℕ)(i:Fin R)(f:Fin R→Fin V→Scalar)(Y:Fin V→Scalar)(s u:State)
 (data:UniformFixedNetworkShearChildMachine.Present A R V f s)
 (selected:∀z,u.scalarHeap (A+i.val*V+z.val)=some (Y z))
 (extent:A+R*V≤F)
 (outside:∀z,z<F→(z<A+i.val*V∨A+(i.val+1)*V≤z)→u.scalarHeap z=s.scalarHeap z):
 UniformFixedNetworkShearChildMachine.Present A R V (replaceRole i Y f) u:=by
 intro j z
 by_cases eq:j=i
 · subst j;simpa only [replaceRole,ite_true] using selected z
 · rw [replaceRole,if_neg eq]
   have bounds:=UniformFixedNetworkShearChildMachine.role_bound A V j
   have point:A+j.val*V+z.val<F:=by
    unfold UniformFixedNetworkShearChildMachine.roleBase at bounds
    have h:=z.isLt;omega
   rw [outside _ point]
   · exact data j z
   · have h:=UniformFixedNetworkShearChildMachine.role_outside A i j eq z
     simpa only [UniformFixedNetworkShearChildMachine.roleBase,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h

lemma replace_values (R k rest:ℕ)(i:Fin R)(M:Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (f:Fin R→Fin (2^(k+rest))→Scalar)(Y:Fin (2^(k+rest))→Scalar)
 (values:∀z,(Y z).value=(spectatorMatrix k rest M).mulVec (fun t=>(f i t).value) z):
 RoleWords.arrayValues (k+rest) (fun j z=>(replaceRole i Y f j z).value)=
 (spectatorLift R k rest (Embedded.matrix (RoleFrameWords.roleEmbedding i) M)).mulVec
  (RoleWords.arrayValues (k+rest) (fun j z=>(f j z).value)):=by
 funext a
 obtain ⟨⟨j,t⟩,rfl⟩:=(RoleWords.roleAddresses R (k+rest)).surjective a
 obtain ⟨⟨s,z⟩,rfl⟩:=(spectatorSplit k rest).symm.surjective t
 rw [RoleWords.arrayValues_at,spectator_role_array]
 by_cases eq:j=i
 · subst j
   simp only [replaceRole,ite_true]
   rw [values,spectator_array]
 · simp only [replaceRole,eq,ite_false]

lemma active_congr {r R:ℕ}(p k:ℕ)(hw:R≤2^p)(e:Fin r↪Fin R)
 (T U:List (WordStep C (r*2^k)))(h:wordMatrix T=wordMatrix U):
 wordMatrix (TensorWords.embeddedWord (paddingAddress R p k hw)
  (PaddingWords.canonicalNetworkWord R k (TripleSchedule.Global.liftWord e T)))=
 wordMatrix (TensorWords.embeddedWord (paddingAddress R p k hw)
  (PaddingWords.canonicalNetworkWord R k (TripleSchedule.Global.liftWord e U))):=by
 simp only [TensorWords.embeddedWord_matrix,PaddingWords.canonicalNetworkWord,
  TypedKernelWords.relabelWord_matrix,TripleSchedule.Global.liftWord]
 rw [h]

lemma active_edge {r R n:ℕ}(p q:ℕ)(hw:R≤2^p)(emb:Fin r↪Fin R)
 {old new:FramedScheduleWords.Label n}(role:Fin r)(edge:FramedScheduleWords.NestedEdge old new):
 nativeMatrix (2^p) (q*n) (wordMatrix (TensorWords.embeddedWord (paddingAddress R p (q*n) hw)
  (PaddingWords.canonicalNetworkWord R (q*n)
   (TripleSchedule.Global.liftWord emb ((ColumnSchedule.edgeColumns q edge).word role)))))=
 Embedded.matrix (RoleFrameWords.roleEmbedding (paddingRole R p hw (emb role)))
  (nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge)):=by
 rw [active_congr p (q*n) hw emb _ _ (UniformNativeResidualBasis.role_basisWord_matrix q role edge).symm]
 exact native_active_lifted_role p (q*n) hw emb role _

open UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
abbrev roleMap:=paddingRole (TripleSchedule.Global.size ExplicitSeedBudget.h)
 ExplicitSeedBudget.roleBits MasterBudget.seed_actual_padding

lemma padded_record (q:ℕ)(a:Invocation){old new:FramedScheduleWords.Label seedWidth}
 (role:Fin (fixedBlock a).width)(edge:FramedScheduleWords.NestedEdge old new):
 macroRecord q ((fixedBlock a).embedding.trans roleMap) (.edge old new role edge)=
 Instruction.record q (.macro a (.edge old new role edge)):=by
 simp only [Instruction.record,macroRecord,Function.Embedding.trans_apply,paddingRole_value]

lemma edge_values (q rest:ℕ)(a:Invocation){old new:FramedScheduleWords.Label seedWidth}
 (role:Fin (fixedBlock a).width)(edge:FramedScheduleWords.NestedEdge old new)
 (f:Fin W→Fin (2^(q*m+rest))→Scalar)(Y:Fin (2^(q*m+rest))→Scalar)
 (values:∀z,(Y z).value=(spectatorMatrix (q*m) rest
  (nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))).mulVec
   (fun t=>(f (roleMap ((fixedBlock a).embedding role)) t).value) z):
 RoleWords.arrayValues (q*m+rest)
  (fun j z=>(replaceRole (roleMap ((fixedBlock a).embedding role)) Y f j z).value)=
 (semantic q rest (.macro a (.edge old new role edge))).mulVec
  (RoleWords.arrayValues (q*m+rest) (fun j z=>(f j z).value)):=by
 have matrix:=active_edge ExplicitSeedBudget.roleBits q MasterBudget.seed_actual_padding
  (fixedBlock a).embedding role edge
 have eq:semantic q rest (.macro a (.edge old new role edge))=
  spectatorLift W (q*m) rest
   (Embedded.matrix (RoleFrameWords.roleEmbedding (roleMap ((fixedBlock a).embedding role)))
    (nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))):=by
  change spectatorLift W (q*m) rest
   (nativeMatrix W (q*m) (wordMatrix (TensorWords.embeddedWord
    (paddingAddress (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits (q*m) MasterBudget.seed_actual_padding)
    (PaddingWords.canonicalNetworkWord (TripleSchedule.Global.size ExplicitSeedBudget.h) (q*m)
     (TripleSchedule.Global.liftWord (fixedBlock a).embedding ((ColumnSchedule.edgeColumns q edge).word role))))))=_
  exact congrArg (spectatorLift W (q*m) rest) matrix
 rw [eq]
 exact replace_values W (q*m) rest _ _ f Y values

end
end ExactFourierCircuits.UniformRecursiveResidualRoleSemantics
