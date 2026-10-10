import DFTModelSavingNativeResidualResult

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeResidual
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open FramedScheduleWords (Label NestedEdge)
open UniformRecursiveResidualEdge (Parent)
open DFTModelSavingNativeDirection (paired_loop matched_runs rows rows_all)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width DFTModelSavingResidual.program DFTModelSavingDirection.rowBill

theorem execution (n B T tapeEnd nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(s s0:State)
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (childIH:DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
 (same:StateMatch s s0)(smaller:q< q*(w+1)+r)(pc:s.pc=P.address .loop)
 (h:Parent (q*(w+1)+r) q A F T r stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T< tapeEnd)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (data:∀a z,s.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X a z))
 (data0:∀a z,s0.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X0 a z))
 (qp:1≤ q)(m2:2≤ w+1)(rp:r< w+1)(fits:ExplicitSeedBudget.roleBits≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length≤ F-6)
 (widthBound:(w+1)+1≤ B)(arrayEnd:A+R*2^(q*(w+1)+r)≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r)≤ B)(square:(2^(q*(w+1)+r))^2≤ B)
 (low:6≤ F)(dataBase:3≤ A)(stackRoom:stack+34*(depth+q+2)≤ stackTop)(stackEnd:stackTop≤ T)
 (room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length≤ B)
 (rawTape:Tape ℕ)(copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) rawTape):
 ∃u u0 ticks,∃Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar,
 Result n B T nRoles R A F q w r stack depth stackTop cost x emb role edge X X0 I handler rawTape s s0 u u0 ticks Y Y0:=by
 have printed0:Printed T (macroRecord q emb (.edge old new role edge)).data s0:=by
  intro z hz;rw [same.natHeap];exact printed z hz
 obtain ⟨a,ea⟩:=entry n B T tapeEnd nRoles R A F q w r stack depth x emb role edge s pc h metadata live printed
  recordEnd widthBound low constants bound code (by omega)
 obtain ⟨a0,ea0⟩:=entry n B T tapeEnd nRoles R A F q w r stack depth (fun _=>0) emb role edge s0 (same.pc.trans pc)
  (parent_match same h) (by rw [same.natHeap];exact metadata) live printed0 recordEnd widthBound low
  (DFTModelSavingResidualNativeGroup.constants_match same constants) (same.wordBound bound) code (by omega)
 have matchedEntry:=matched_runs ea.run ea0.run same
 have ad:∀i z,a.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (X i z):=by
  intro i z;rw [ea.scalar];exact data i z
 have ad0:∀i z,a0.scalarHeap (A+i.val*2^(q*(w+1)+r)+z.val)=some (X0 i z):=by
  intro i z;rw [ea0.scalar];exact data0 i z
 have vis:UniformRecursiveResidualDirectionLoop.Visit edge.dimension 0 (List.finRange edge.dimension):=by
  rw [←UniformRecursiveResidualDirectionLoop.indices_all]
  exact UniformRecursiveResidualDirectionLoop.indices_visit edge.dimension 0 edge.dimension (by omega)
 obtain ⟨b,b0,bt,Y,Y0,body⟩:=paired_loop n B T nRoles R A F q w r stack depth stackTop reserve cost x emb role edge 0
  (List.finRange edge.dimension) vis a a0 X X0 I handler childIH matchedEntry smaller ea.pc ea.control ea0.control ea.printed
  ad ad0 qp m2 rp fits (by omega) widthBound arrayEnd poolEnd square (by omega) dataBase stackRoom (by omega) stackEnd room
  ea.constants ea.run.final_bound code rawTape copied
 have mode:b.natHeap (F-6)=some 0:=by
  rw [body.nat _ (by omega) (Or.inr (by omega))];exact ea.mode
 have mode0:b0.natHeap (F-6)=some 0:=by
  rw [body.zeroNat _ (by omega) (Or.inr (by omega))];exact ea0.mode
 obtain ⟨u,last⟩:=finish n B (q*(w+1)+r) q A F T r stack depth edge.dimension edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse
  x b body.pc body.control mode body.run.final_bound code
 obtain ⟨u0,last0⟩:=finish n B (q*(w+1)+r) q A F T r stack depth edge.dimension edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse
  (fun _=>0) b0 (body.matched.pc.trans body.pc) body.zeroControl mode0 body.zeroRun.final_bound code
 have cu:UniformBinaryCStageMachine.Constants u:=by
  have cb:=body.constants
  unfold UniformBinaryCStageMachine.Constants at cb ⊢
  exact ⟨(congrFun last.frame.scalarHeap 1).trans cb.1,(congrFun last.frame.scalarHeap 2).trans cb.2⟩
 have cu0:UniformBinaryCStageMachine.Constants u0:=by
  have cb:=body.zeroConstants
  unfold UniformBinaryCStageMachine.Constants at cb ⊢
  exact ⟨(congrFun last0.frame.scalarHeap 1).trans cb.1,(congrFun last0.frame.scalarHeap 2).trans cb.2⟩
 refine ⟨u,u0,46+bt+6,Y,Y0,(ea.run.trans body.run).trans last.run,(ea0.run.trans body.zeroRun).trans last0.run,
  matched_runs last.run last0.run body.matched,last.pc,last.parent,last0.parent,?_,?_,?_,?_,?_,?_,cu,cu0,
  last.frame.roots.trans (body.roots.trans ea.roots),last0.frame.roots.trans (body.zeroRoots.trans ea0.roots),
  last.frame.outputs.trans (body.outputs.trans ea.outputs),last0.frame.outputs.trans (body.zeroOutputs.trans ea0.outputs),
  ?_,?_,?_,?_,body.other,body.zeroOther⟩
 · intro i z;rw [last.frame.scalarHeap];exact body.present i z
 · intro i z;rw [last0.frame.scalarHeap];exact body.zeroPresent i z
 · intro z hz away ne;exact (last.frame.natHeap z ne).trans ((body.nat z hz away).trans (ea.nat z ne))
 · intro z hz away ne;exact (last0.frame.natHeap z ne).trans ((body.zeroNat z hz away).trans (ea0.nat z ne))
 · intro z hz away;exact (congrFun last.frame.scalarHeap z).trans ((body.scalar z hz away).trans (congrFun ea.scalar z))
 · intro z hz away;exact (congrFun last0.frame.scalarHeap z).trans ((body.zeroScalar z hz away).trans (congrFun ea0.scalar z))
 · have boundTime:=body.time
   simp only [List.length_finRange] at boundTime
   omega
 · rw [DFTModelSavingDirection.residual_run]
   change (DFTModelSavingDirection.steps handler r rawTape ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)
    (rawTape.look 6 0)).val=_
   obtain ⟨_,_,_,_,count⟩:=DFTModelSavingDirection.macro_headers q emb role edge rawTape copied
   rw [count,←rows_all]
   exact body.value
 · intro z
   have bv:=body.values
   rw [UniformRecursiveResidualDirectionLoop.action_basis] at bv
   exact bv z
 · intro z
   have bv:=body.zeroValues
   rw [UniformRecursiveResidualDirectionLoop.action_basis] at bv
   exact bv z

end
end ExactFourierCircuits.DFTModelSavingNativeResidual
