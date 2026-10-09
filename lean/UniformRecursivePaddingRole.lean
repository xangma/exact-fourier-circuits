import UniformRecursivePaddingActualFragments
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingRole
open UniformMachine UniformRecursivePaddingFrames
open UniformFixedNetworkScheduleMachine (Record Printed macroRecord)
namespace C
export UniformRecursivePaddingControl (patchRecord)
end C
namespace D
export UniformRecursiveResidualDirectionLoop (directionCost)
end D
noncomputable section

def record (w:ℕ):Record:=UniformRecursiveNodePreparation.binaryUnitRecord (w+1)
lemma record_length (w:ℕ):(record w).data.length=8+(w+1)*(w+1):=by
 simp only [record,Record.data_length,UniformRecursiveNodePreparation.binaryUnitRecord,List.length_ofFn]
lemma record_cost (w:ℕ):UniformFixedNetworkOpcodeMachine.headCost (record w)=32:=rfl
def roleCost (q w r:ℕ)(cost:ℕ→ℕ):ℕ:=(w+1)*D.directionCost q w r 32 cost+58

lemma metadata_patch {F U saved role last w:ℕ}{s u:State}
 (h:Metadata F U saved role last s)(f:UniformRecursivePaddingControl.Frame [U+1,U+3] s u)
 (extent:U+(record w).data.length≤F-6)(low:6≤F):Metadata F U saved role last u:=by
 have len:=record_length w
 exact h.transport (by
  intro z hz
  apply f.natHeap
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl|rfl <;>omega)

lemma metadata_loop {F U saved role last w stack depth stackTop:ℕ}{s u:State}
 (h:Metadata F U saved role last s)
 (frame:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z)
 (extent:U+(record w).data.length≤F-6)(low:6≤F)(above:stackTop≤U):Metadata F U saved role last u:=by
 have len:=record_length w
 apply h.transport
 intro z hz
 simp only [List.mem_cons,List.mem_nil_iff,or_false] at hz
 rcases hz with rfl|rfl|rfl|rfl|rfl <;>exact frame _ (by omega) (Or.inr (by omega))

lemma printed_loop {F U q role w stack depth stackTop:ℕ}{s u:State}
 (h:Printed U (C.patchRecord (record w) q role).data s)
 (frame:∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z)
 (extent:U+(record w).data.length≤F-6)(low:6≤F)(above:stackTop≤U):
 Printed U (C.patchRecord (record w) q role).data u:=by
 apply UniformRecursiveNodeJoin.printed_transport U _ s u h
 intro z lower upper
 rw [UniformRecursivePaddingControl.patch_length_same] at upper
 exact frame z (by omega) (Or.inr (by omega))

theorem execution (n B U R A F q w r stack depth stackTop reserve saved last prior:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(role:Fin R)(s:State)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q<q*(w+1)+r)(pc:s.pc=P.address .paddingPatch)
 (parent:Parent (q*(w+1)+r) q A F r stack depth s)
 (metadata:Metadata F U saved role.val last s)(dst:s.natReg 4175=role.val)
 (printed:Printed U (C.patchRecord (record w) q prior).data s)
 (data:∀z,s.scalarHeap (A+role.val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1≤q)(m2:2≤w+1)(rp:r<w+1)(fits:ExplicitSeedBudget.roleBits≤q*w+r)
 (unitEnd:U+(record w).data.length≤F-6)(widthBound:(w+1)+1≤B)
 (arrayEnd:A+R*2^(q*(w+1)+r)≤F)(poolEnd:F+5*2^(q*(w+1)+r)≤B)
 (square:(2^(q*(w+1)+r))^2≤B)(low:6≤F)(dataBase:3≤A)
 (stackRoom:stack+34*(depth+q+2)≤ stackTop)(recordAbove:stackTop≤U)
 (room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q≤B)(roleBound:role.val+1≤B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length≤B):
 ∃u ticks,∃Y:Fin (2^(q*(w+1)+r))→Scalar,
 BoundedRuns P.program n x B s ticks u∧u.pc=P.address .paddingTest∧
 Parent (q*(w+1)+r) q A F r stack depth u∧Metadata F U saved (role.val+1) last u∧
 Printed U (C.patchRecord (record w) q role.val).data u∧
 (∀z,u.scalarHeap (A+role.val*2^(q*(w+1)+r)+z.val)=some (Y z))∧
 (∀z,(Y z).value=(UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformBinaryTensorCoordinates.physicalMatrix (q*(w+1)))).mulVec (fun y=>(X y).value) z)∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→z≠U+1→z≠U+3→z≠F-4→u.natHeap z=s.natHeap z)∧
 (∀z,z<F→(z<A+role.val*2^(q*(w+1)+r)∨A+(role.val+1)*2^(q*(w+1)+r)≤z)→u.scalarHeap z=s.scalarHeap z)∧
 UniformBinaryCStageMachine.Constants u∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs∧ticks≤roleCost q w r cost:=by
 let edge:=UniformRecursivePaddingUnitEdge.unitEdge (w+1)
 let emb:Fin R↪Fin R:=Function.Embedding.refl _
 let mac:=macroRecord q emb (.edge _ _ role edge)
 have macroEq:mac=C.patchRecord (record w) q role.val:=UniformRecursivePaddingUnitEdge.macro_unit q (w+1) emb role
 have patched:C.patchRecord (C.patchRecord (record w) q prior) q role.val=mac:=by
  rw [UniformRecursivePaddingControl.patch_twice,macroEq]
 have fg:UniformFixedNetworkOpcodeMachine.WellFormed (C.patchRecord (record w) q prior):=
  UniformRecursivePaddingControl.patch_good _ _ _ (UniformRecursivePaddingControl.binaryUnit_good _)
 have extent:U+(C.patchRecord (record w) q prior).data.length≤B:=by
  rw [UniformRecursivePaddingControl.patch_length_same]
  omega
 obtain ⟨a,patch,ap,fields,ak,bank,_,finish,pf⟩:=UniformRecursivePaddingControl.patch_reader_execution
  n B F U q role.val (q*(w+1)+r) (C.patchRecord (record w) q prior) x s pc parent.frontier parent.one low
  metadata.unit parent.columns dst parent.bits printed fg bound extent widthBound code
 have pa:=parent.padding pf ak
 have ma:=metadata_patch metadata pf unitEnd low
 have bankA:Printed U mac.data a:=by simpa only [patched] using bank
 have dim:a.natReg 2857=w+1:=fields.dimension
 have inv:a.natReg 2856=0:=fields.inverse
 have finishA:a.natReg 2865=U+mac.data.length:=by
  rw [macroEq,UniformRecursivePaddingControl.patch_length_same]
  simpa only [UniformRecursivePaddingControl.patch_length_same] using finish
 obtain ⟨b,init,bp,bi,bd,bf,biv,bnh,ifr⟩:=UniformRecursiveResidualControl.init_execution
  n B F (w+1) (U+mac.data.length) 0 x a ap pa.one dim finishA inv patch.final_bound code
 have pb:=pa.residual ifr
 have bc:b.natReg 2850=U:=(UniformRecursivePaddingFragments.residual_init_cursor
  n B F (w+1) (U+mac.data.length) 0 x a b ap pa.one dim finishA inv patch.final_bound code init).trans fields.cursor
 have cb:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F U r stack depth 0 edge.dimension
  (U+mac.data.length) mac.inverse b:=
  ⟨bc,pb.nativeBase,pb.original,pb.bits,pb.volume,pb.frontier,pb.rest,pb.stack,pb.depth,pb.one,
   bi,bd,bf,biv,pb.nativeBits,pb.nativeRest,pb.table,pb.columns,pb.width⟩
 have bankB:Printed U mac.data b:=by intro j hj;rw[bnh];exact bankA j hj
 have dataB:∀z,b.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z):=by
  intro z;rw[ifr.scalarHeap,pf.scalarHeap];exact data z
 have mb:Metadata F U saved role.val last b:=ma.transport (fun z _=>congrFun bnh z)
 have constB:UniformBinaryCStageMachine.Constants b:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  rw [ifr.scalarHeap,pf.scalarHeap];exact constants
 have visit:UniformRecursiveResidualDirectionLoop.Visit edge.dimension 0 (List.finRange edge.dimension):=by
  rw [←UniformRecursiveResidualDirectionLoop.indices_all]
  exact UniformRecursiveResidualDirectionLoop.indices_visit edge.dimension 0 edge.dimension (by omega)
 have recEnd:U+mac.data.length≤F:=by rw[macroEq,UniformRecursivePaddingControl.patch_length_same];omega
 obtain ⟨c,dt,Y,directions,cp,yp,yv,cc,cn,csh,constC,cr,co,ct⟩:=UniformRecursiveResidualDirectionLoop.loop
  n B U R R A F q w r stack depth stackTop reserve cost x emb role edge 0 (List.finRange edge.dimension) visit b X
  childIH smaller bp cb bankB dataB qp m2 rp fits recEnd widthBound arrayEnd poolEnd square (by omega) dataBase
  stackRoom (by omega) recordAbove room constB init.final_bound code
 have pcParent:=Parent.of_control cc
 have metaC:=metadata_loop mb cn unitEnd low recordAbove
 have printC:Printed U (C.patchRecord (record w) q role.val).data c:=
  printed_loop (by simpa only[macroEq] using bankB) cn unitEnd low recordAbove
 obtain ⟨d,edgeDone,dp,_,dnh,df⟩:=UniformRecursiveResidualControlJoin.edge_done_finish
  n B F 1 x c cp pcParent.one pcParent.frontier metaC.mode directions.final_bound code
 have pd:=pcParent.residual df
 have metaD:Metadata F U saved role.val last d:=metaC.transport (fun z _=>congrFun dnh z)
 have dp':d.pc=P.address .paddingNext:=by simpa only[Nat.lt_irrefl,ite_false] using dp
 obtain ⟨u,advance,up,current,af⟩:=UniformRecursivePaddingControl.next_execution n B F role.val x d dp'
  pd.frontier pd.one low metaD.current edgeDone.final_bound code roleBound
 have ubits: u.natReg 5300=q*(w+1)+r:=(UniformRecursivePaddingFragments.next_bits n B F role.val x d u
  dp' pd.frontier pd.one metaD.current low edgeDone.final_bound code roleBound advance).trans pd.nativeBits
 have pu:=pd.padding af ubits
 have metadataU:Metadata F U saved (role.val+1) last u:=by
  refine ⟨?_,?_,current,?_,?_⟩
  all_goals first
  | exact (af.natHeap _ (by simp only[List.mem_singleton];omega)).trans metaD.mode
  | exact (af.natHeap _ (by simp only[List.mem_singleton];omega)).trans metaD.saved
  | exact (af.natHeap _ (by simp only[List.mem_singleton];omega)).trans metaD.endpoint
  | exact (af.natHeap _ (by simp only[List.mem_singleton];omega)).trans metaD.unit
 have printU:Printed U (C.patchRecord (record w) q role.val).data u:=by
  intro j hj
  have hlen:(C.patchRecord (record w) q role.val).data.length=(record w).data.length:=UniformRecursivePaddingControl.patch_length_same _ _ _
  have neq:U+j≠F-4:=by rw[hlen] at hj;omega
  rw [af.natHeap _ (by simpa only[List.mem_singleton] using neq),dnh]
  exact printC j hj
 have outValues:∀z,(Y z).value=(UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformBinaryTensorCoordinates.physicalMatrix (q*(w+1)))).mulVec (fun y=>(X y).value) z:=by
  intro z
  exact (yv z).trans (congrFun (UniformRecursivePaddingUnitEdge.action_unit q w r (fun y=>(X y).value)) z)
 have head:UniformFixedNetworkOpcodeMachine.headCost (C.patchRecord (record w) q prior)=32:=rfl
 have macCost:UniformFixedNetworkOpcodeMachine.headCost mac=32:=by rw[macroEq];rfl
 refine ⟨u,10+UniformFixedNetworkOpcodeMachine.headCost (C.patchRecord (record w) q prior)+5+dt+4+6,Y,
  (((patch.trans init).trans directions).trans edgeDone).trans advance,up,pu,metadataU,printU,?_,outValues,?_,?_,?_,?_,?_,?_⟩
 · intro z;rw[af.scalarHeap,df.scalarHeap];exact yp z
 · intro z hz away a b c
   rw [af.natHeap z (by simpa only[List.mem_singleton] using c),dnh,cn z hz away,bnh,pf.natHeap z (by simp only[List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨a,b⟩)]
 · intro z hz away
   rw [af.scalarHeap,df.scalarHeap,csh z hz away,ifr.scalarHeap,pf.scalarHeap]
 · unfold UniformBinaryCStageMachine.Constants at constC ⊢
   rw[af.scalarHeap,df.scalarHeap];exact constC
 · exact af.roots.trans (df.roots.trans (cr.trans (ifr.roots.trans pf.roots)))
 · exact af.outputs.trans (df.outputs.trans (co.trans (ifr.outputs.trans pf.outputs)))
 · rw[macCost] at ct
   simp only [List.length_finRange,edge,UniformRecursivePaddingUnitEdge.dimension] at ct
   rw[head]
   unfold roleCost
   omega
end
end ExactFourierCircuits.UniformRecursivePaddingRole
