import DFTModelSavingNativeDirectionBilledExecution
import DFTModelSavingResidualBilledSlice
import DFTModelSavingCostBilledDirection

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine BinaryFrames DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
open UniformFixedNetworkScheduleMachine (macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width DFTModelSavingResidual.program DFTModelSavingDirection.rowBill

theorem row_work {nRoles R w:ℕ} (q r:ℕ) (emb:Fin nRoles↪Fin R)
 {old new:Label (w+1)} (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)
 (X X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar)(I:ℂ)(handler:Handler DFTModelSavingResidual.Port)
 (raw:Tape ℕ)(copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) raw)
 (p:Fin (w+1))(hp:edgeVectors edge j p=1)(first:∀i:Fin (w+1),i.val< p.val→edgeVectors edge j i=0)
 (fits:ExplicitSeedBudget.roleBits≤ q*w+r)(qp:1≤ q)(wide:2≤ w)(roles:R=UniformBatching.width)
 (K localTicks childTicks:ℕ)(coefficient:363*(w+1)+240*r+1347+104*UniformBatching.width≤ K)
 (localBound:2^(q*(w+1)+r)+BG.groupCount q w r≤ localTicks)
 (children:DFTModelSavingResidualNativeGroup.remainingWork q I handler
  (FV.input q w r fits (edgeVectors edge j) p hp (X (emb role)))
  (FV.input q w r fits (edgeVectors edge j) p hp (X0 (emb role))) 0≤ K*childTicks+K*BG.groupCount q w r)
 (initial:Node.T):
 (DFTModelSavingDirection.rowBill handler r j.val raw initial
  ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)).work+1≤ K*(localTicks+childTicks):=by
 let node:Node.T:=((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired X X0)
 let bits:=DFTModelSavingDirection.row (w+1) j.val raw
 let ctx:DFTModelSavingResidualSetup.Input.T:=((q,(w+1,(r,bits))),
  ((emb role).val,(raw.look 5 0,node)))
 have headers:=DFTModelSavingDirection.macro_headers q emb role edge raw copied
 have argsEq:DFTModelSavingDirection.decoded r j.val raw node=ctx:=by
  unfold DFTModelSavingDirection.decoded
  rw [headers.1,headers.2.1,headers.2.2.1]
 have source:=DFTModelSavingDirection.row_source q emb role edge raw copied j
 have nonzero:edgeVectors edge j≠0:=by
  intro eq;have norm:=UniformResidualFibers.edgeVector_norm edge j
  rw [eq] at norm;simp [BinaryFrames.dot] at norm
 have groupEq:(DFTModelSavingResidual.arguments (DFTModelSavingDirection.decoded r j.val raw node)).2.1=BG.groupCount q w r:=by
  rw [argsEq]
  exact (DFTModelSavingResidualGeometry.source_arguments q w r (edgeVectors edge j) bits (emb role).val
   (raw.look 5 0) (q*(w+1)+r) I (DFTModelRecursiveScalarSource.paired X X0) qp source nonzero fits).2.1
 have childEq:DFTModelSavingCost.residualChildrenWork handler (DFTModelSavingDirection.decoded r j.val raw node)=
  DFTModelSavingResidualNativeGroup.remainingWork q I handler
   (FV.input q w r fits (edgeVectors edge j) p hp (X (emb role)))
   (FV.input q w r fits (edgeVectors edge j) p hp (X0 (emb role))) 0:=by
  unfold DFTModelSavingCost.residualChildrenWork
  rw [argsEq]
  exact DFTModelSavingResidualNativeGroup.childrenWork_first q w r (edgeVectors edge j) bits (emb role) X X0 qp
   source p hp first fits (raw.look 5 0) (q*(w+1)+r) I handler
 apply DFTModelSavingCost.direction_row_billed_work q r emb role edge raw copied j (q*(w+1)+r) K localTicks childTicks I
  (DFTModelRecursiveScalarSource.paired X X0) initial handler qp wide
 · change R*2^(q*(w+1)+r)=_
   rw [roles]
 · exact coefficient
 · rw [groupEq];exact localBound
 · rw [childEq,groupEq];exact children

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
