import DFTModelSavingNativePaddingExecution
import DFTModelSavingNativePaddingRole

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingExecution
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record)
noncomputable section
attribute [local irreducible] P.program

/-- Actual initialization and every actual unit-role call. Only the ordinary
strong-induction hypothesis for smaller same-program children remains. -/
theorem concrete (n B U R A F q w r stack depth stackTop reserve saved start : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (handler : Handler DFTModelSavingRecords.Port)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies
      (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
    (s s0 : State) (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar)
    (same : StateMatch s s0) (smaller : q<q*(w+1)+r)
    (pc : s.pc=P.address .paddingInit) (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (savedHeader : s.natReg 2865=saved) (destHeader : s.natReg 2854=start)
    (countHeader : s.natReg 2855=R-start) (pointer : s.natHeap (F-2)=some U)
    (printed : Printed U ((record w).withColumns q).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (present0 : Present A R (2^(q*(w+1)+r)) f0 s0)
    (startBound : start ≤ R) (qp : 1 ≤ q) (m2 : 2 ≤ w+1) (rp : r<w+1)
    (fits : ExplicitSeedBudget.roleBits ≤ q*w+r) (unitEnd : U+(record w).data.length ≤ F-6)
    (widthBound : (w+1)+1 ≤ B) (arrayEnd : A+R*2^(q*(w+1)+r) ≤ F)
    (poolEnd : F+5*2^(q*(w+1)+r) ≤ B) (square : (2^(q*(w+1)+r))^2 ≤ B)
    (low : 6 ≤ F) (dataBase : 3 ≤ A) (stackRoom : stack+34*(depth+q+2) ≤ stackTop)
    (recordAbove : stackTop ≤ U) (room : F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q ≤ B)
    (rolesBound : R ≤ B) (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) (code : P.program.length ≤ B) (widthActual : w+1=ExplicitSeedBudget.m) :
    ∃u u0 ticks g g0 prior,
      Result n B U R A F q w r stack depth stackTop saved start cost x I handler
        s s0 u u0 ticks prior f f0 g g0 := by
  apply execution n B U R A F q w r stack depth stackTop saved start cost x I handler
    ?_ s s0 f f0 same pc parent savedHeader destHeader countHeader pointer printed present present0
    startBound unitEnd recordAbove rolesBound low constants bound code
  intro role prior a a0 X X0 matched atPatch pa ma dest bank data data0 ca ba
  exact DFTModelSavingNativePaddingRole.execution n B U R A F q w r stack depth stackTop reserve
    saved R prior cost x role a a0 X X0 I handler childIH matched smaller atPatch pa ma dest bank data data0
    qp m2 rp fits unitEnd widthBound arrayEnd poolEnd square low dataBase stackRoom recordAbove room
    ((Nat.succ_le_of_lt role.isLt).trans rolesBound) ca ba code widthActual

end
end ExactFourierCircuits.DFTModelSavingNativePaddingExecution
