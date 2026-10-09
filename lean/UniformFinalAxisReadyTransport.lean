import UniformFinalAxisRetention
import UniformActualClockReady

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisReadyTransport
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformTensorMonomialMachine (setPC)
open UniformFinalAxisRetention
noncomputable section

lemma observed_eq {s u:State}(h:∀q,6020≤q→q<6038→u.natReg q=s.natReg q):
 UniformJointAllocationMachine.observed u=UniformJointAllocationMachine.observed s:=by
 unfold UniformJointAllocationMachine.observed
 congr 1 <;>exact h _ (by omega) (by omega)

lemma ready {n H seedDirectory g:ℕ}{hn:0<n}{x:Fin n→ℂ}
 {v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar}{s u:State}
 (old:UniformActualClockReady.Ready hn H seedDirectory x g v (setPC s 5))
 (frame:Frame hn s u)(bound:WordBound (UniformJointAllocation.envelope constants n) u):
 UniformActualClockReady.Ready hn H seedDirectory x g v (setPC u 5):=by
 have reg(q:ℕ)(h:UniformFourierAxisPrepareHead.Protected q)(a:q≠5922)(b:q≠5923)(c:q≠5924)(d:q≠5925):
  u.natReg q=s.natReg q:=frame.registers q h a b c d
 have large:=UniformJointAllocation.actual_arithmetic constants n hn
 have wb:WordBound (UniformJointAllocation.envelope constants n) (setPC u 5):=
  changePC_bound _ u 5 bound (by have code:=UniformActualGlobalClockProgram.code_bound n;have len:=UniformActualGlobalClockProgram.program_length;omega)
 have allocated:UniformJointAllocationMachine.observed u=UniformJointAllocationMachine.observed s:=
  observed_eq (fun q lo hi=>reg q (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega))
 have oldAll:UniformAxisCacheLoopState.All constants n hn (axisCount n) s:=
  UniformAxisCacheLoopState.All.transport old.cache rfl rfl
 have all:=frame.all oldAll
 have oldInput:UniformAxisCacheInputs.Inputs n x s:=
  UniformClockCacheInputsRetention.inputs constants hn x (setPC s 5) s old.inputs
   (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _ _=>rfl) rfl rfl
 have input:=frame.inputs oldInput
 refine ⟨rfl,wb,allocated.trans old.allocator,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,old.length,input.withPC,?_⟩
 · exact (congrArg (fun a=>a+1) (reg 102 (by unfold UniformFourierAxisPrepareHead.Protected;omega)
    (by omega) (by omega) (by omega) (by omega))).trans old.axisCount
 · exact (reg 103 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.volume
 · exact (reg 5921 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.horizon
 · exact (reg 5920 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.clock
 · exact (reg 5936 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.natArena
 · exact (reg 5937 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.scalarArena
 · exact (reg 5938 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.axes
 · exact (reg 5939 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.one
 · exact (reg 6904 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.seed
 · exact (reg 6909 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.initialNat
 · exact (reg 6910 (by unfold UniformFourierAxisPrepareHead.Protected;omega) (by omega) (by omega) (by omega) (by omega)).trans old.initialScalar
 · intro r hr j
   exact (frame.scalarHigh _ (by unfold UniformKernelSpectrumStorage.base UniformActualClockEntry.sourceBase;omega)).trans (old.source r hr j)
 · exact ⟨(frame.scalarLow 1 (by omega)).trans old.constants.1,(frame.scalarLow 2 (by omega)).trans old.constants.2⟩
 · exact UniformAxisCacheLoopState.All.transport all rfl rfl

end
end ExactFourierCircuits.UniformFinalAxisReadyTransport
