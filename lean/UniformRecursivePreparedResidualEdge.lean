import UniformRecursivePreparedResidualLoop
import UniformRecursiveResidualEdge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualEdge
open UniformMachine BinaryFrames FramedScheduleWords
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open UniformRecursiveResidualControlJoin (raw_entry_cursor edge_done_finish)
noncomputable section
theorem execution_prepared (n B T tapeEnd nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(s:State)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x)
 (smaller:q  <  q*(w+1)+r)(pc:s.pc=P.address .loop)
 (h:Parent (q*(w+1)+r) q A F T r stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T  <  tapeEnd)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1  ≤  q)(m2:2  ≤  w+1)(rp:r  <  w+1)(fits:ExplicitSeedBudget.roleBits  ≤  q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length  ≤  F-6)
 (widthBound:(w+1)+1  ≤  B)(arrayEnd:A+R*2^(q*(w+1)+r)  ≤  F)
 (poolEnd:F+5*2^(q*(w+1)+r)  ≤  B)(square:(2^(q*(w+1)+r))^2  ≤  B)
 (low:6  ≤  F)(dataBase:3  ≤  A)(stackRoom:stack+34*(depth+q+2)  ≤  stackTop)(stackEnd:stackTop  ≤  T)
 (room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q  ≤  B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length  ≤  B):
 ∃u ticks,∃Y:Fin (2^(q*(w+1)+r))→Scalar,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .loop ∧
 Parent (q*(w+1)+r) q A F (T+(macroRecord q emb (.edge old new role edge)).data.length) r stack depth u ∧
 (∀z,u.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (Y z)) ∧
 (∀z,(Y z).value=(UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r
  (UniformNativeResidualSemantics.nativeWordMatrix (UniformNativeResidualBasis.basisWord q edge))).mulVec
  (fun y=>(X y).value) z) ∧
 (∀z,z  <  F→(z  <  stack+34*depth∨stackTop  ≤  z)→z≠F-6→u.natHeap z=s.natHeap z) ∧
 (∀z,z  <  F→(z  <  A+(emb role).val*2^(q*(w+1)+r)∨A+((emb role).val+1)*2^(q*(w+1)+r)  ≤  z)→
  u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 ticks  ≤  edge.dimension*L.directionCost q w r
  (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+53 ∧ (UniformRecursivePreparedValues.Prepared X→UniformRecursivePreparedValues.Prepared Y):=by
 let record:=macroRecord q emb (.edge old new role edge)
 have fb:F  ≤  B:=by omega
 have recordLimit:T+record.data.length ≤ F-6:=recordEnd
 obtain ⟨a,t,entry,ap,acursor,idx,dim,finish,flag,mode,main,unit,cf,rf⟩:=raw_entry_cursor
  F T tapeEnd n B record x s pc h.frontier h.cursor h.one metadata live printed
  (UniformFixedNetworkOpcodeMachine.macro_wellFormed q emb (.edge old new role edge)) rfl bound code
  (by omega) widthBound low
 have ah:=parent_raw h cf rf acursor
 have apr:Printed T record.data a:=by
  intro z hz
  rw [rf.natHeap _ (by omega),cf.natHeap]
  exact printed z hz
 have ad:∀z,a.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z):=by
  intro z;rw [rf.scalarHeap,cf.scalarHeap];exact data z
 have ca:UniformBinaryCStageMachine.Constants a:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  exact ⟨(congrFun rf.scalarHeap 1).trans ((congrFun cf.scalarHeap 1).trans constants.1),
   (congrFun rf.scalarHeap 2).trans ((congrFun cf.scalarHeap 2).trans constants.2)⟩
 have ac:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth 0 edge.dimension
  (T+record.data.length) record.inverse a:=
  ⟨ah.cursor,ah.nativeBase,ah.original,ah.bits,ah.volume,ah.frontier,ah.rest,ah.stack,ah.depth,ah.one,idx,dim,finish,flag,ah.nativeBits,ah.nativeRest,ah.table,ah.columns,ah.width⟩
 have vis:UniformRecursiveResidualDirectionLoop.Visit edge.dimension 0 (List.finRange edge.dimension):=by
  rw [←L.indices_all];exact L.indices_visit edge.dimension 0 edge.dimension (by omega)
 obtain ⟨b,bt,Y,body,bp,yp,yv,bc,bn,bs,cb,bro,bo,btime,preparedY⟩:=UniformRecursiveResidualDirectionLoop.loop_prepared n B T nRoles R A F q w r stack depth stackTop reserve
  cost x emb role edge 0 (List.finRange edge.dimension) vis a X childIH smaller ap ac apr ad qp m2 rp fits
  (by omega) widthBound arrayEnd poolEnd square (by omega) dataBase stackRoom (by omega) stackEnd room ca entry.final_bound code
 have bm:b.natHeap (F-6)=some 0:=by
  rw [bn _ (by omega) (Or.inr (by omega))];exact mode
 obtain ⟨c,edgeRun,cp,ce,cn,ef⟩:=edge_done_finish n B F 0 x b bp bc.one bc.frontier bm body.final_bound code
 have cpc:c.pc=P.address .recordAdvance:=by simpa only [Nat.zero_lt_one,ite_true] using cp
 have cone:c.natReg 4153=1:=(ef.natReg _ (by unfold C.Changed;omega)).trans bc.one
 have cfinish:c.natReg 4130=T+record.data.length:=ce.trans bc.finish
 obtain ⟨u,advance,up,ptr,un,af⟩:=UniformRecursiveResidualControl.record_advance n B F (T+record.data.length) x c
  cpc cone cfinish edgeRun.final_bound code
 have eaf:=ef.trans af
 have ph:=parent_frame (parent_direction bc) eaf ptr
 refine ⟨u,46+bt+4+2,Y,((entry.trans body).trans edgeRun).trans advance,up,ph,?_,?_,?_,?_,?_,
  af.roots.trans (ef.roots.trans (bro.trans (rf.roots.trans cf.roots))),
  af.outputs.trans (ef.outputs.trans (bo.trans (rf.outputs.trans cf.outputs))),?_,preparedY⟩
 · intro z;rw [af.scalarHeap,ef.scalarHeap];exact yp z
 · intro z;rw [L.action_basis] at yv;exact yv z
 · intro z hz away ne
   exact (eaf.natHeap z ne).trans ((bn z hz away).trans ((rf.natHeap z ne).trans (congrFun cf.natHeap z)))
 · intro z hz away
   exact (congrFun eaf.scalarHeap z).trans ((bs z hz away).trans ((congrFun rf.scalarHeap z).trans (congrFun cf.scalarHeap z)))
 · unfold UniformBinaryCStageMachine.Constants at cb ⊢
   exact ⟨(congrFun eaf.scalarHeap 1).trans cb.1,(congrFun eaf.scalarHeap 2).trans cb.2⟩
 · simp only [List.length_finRange] at btime;omega
end
end ExactFourierCircuits.UniformRecursiveResidualEdge
