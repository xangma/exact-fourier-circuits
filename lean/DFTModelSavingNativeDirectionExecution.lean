import DFTModelSavingNativeDirectionPackage
import DFTModelSavingDirectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeInverse)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width DFTModelSavingResidual.program

theorem paired_execution (n B T nRoles R A F q w r stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (I:ℂ) (handler:Handler DFTModelSavingResidual.Port)
 (ih:DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
 (smaller:q < q*(w+1)+r)(pc:s.pc=P.address .gather)(cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val)(base:s.natReg 3300=A)(original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r)(volume:s.natReg 4122=2^(q*(w+1)+r))
 (frontier:s.natReg 4123=F)(rest:s.natReg 4127=r)(st:s.natReg 4150=stack)
 (dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (data:∀a z,s.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X a z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B)
 (low:3 ≤ F)(stackRoom:stack+34*(depth+q+2) ≤ stackTop)(stackEnd:stackTop ≤ F)
 (recordAbove:stackTop ≤ T)(room:F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B)
 (X0:Fin R→Fin (2^(q*(w+1)+r))→Scalar) (s0:State) (same:StateMatch s s0)
 (data0:∀a z,s0.scalarHeap (A+a.val*2^(q*(w+1)+r)+z.val)=some (X0 a z))
 (rawTape: Tape ℕ)(copied:DFTModelSavingDirection.RawSource (macroRecord q emb (.edge old new role edge)) rawTape)
 (table:s.natReg 3389=F+3*2^(q*(w+1)+r))(dataBase:3≤A) :
 ∃u u0 ticks,∃Y Y0:Fin R→Fin (2^(q*(w+1)+r))→Scalar,
 PairDirectionResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j X X0 I handler rawTape s s0 u u0 ticks Y Y0 := by
 obtain ⟨p,hp,a,a0,ct,children,children0,matchedChildren,pairBank⟩:=paired_children
  n B T nRoles R A F q w r stack depth stackTop reserve cost x s emb role edge j (X (emb role)) I handler ih
  smaller pc cursor printed index base original bits volume frontier rest st dp one (data (emb role)) qp m2 rp fits
  recordEnd widthBound arrayEnd poolEnd square low stackRoom stackEnd recordAbove room constants bound code
  (X0 (emb role)) s0 same (data0 (emb role))
 obtain ⟨u,Y,actual⟩:=tail_execution n B T nRoles R A F q w r stack depth stackTop cost x s a ct emb role edge j
  (X (emb role)) p hp table qp m2 rp fits poolEnd square smaller recordEnd arrayEnd low dataBase code children
 obtain ⟨u0,Y0,zero⟩:=tail_execution n B T nRoles R A F q w r stack depth stackTop cost (fun _=>0) s0 a0 ct emb role edge j
  (X0 (emb role)) p hp (by rw [same.natReg];exact table) qp m2 rp fits poolEnd square smaller recordEnd arrayEnd low dataBase code children0
 obtain ⟨Z,Z0,closed⟩:=of_tails n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j X X0 I handler
  rawTape copied s s0 a a0 u u0 _ Y Y0 p hp children.first fits qp arrayEnd same data data0 actual zero pairBank
 exact ⟨u,u0,_,Z,Z0,closed⟩

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
