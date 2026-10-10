import DFTModelGlobalCompactPoolsEvent
import DFTModelGlobalClockPaired

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalCompactPoolsPaired
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformTensorMonomialMachine
open DFTModelAdmissibilityControl DFTModelAffine
open DFTModelGlobalClockDiagonal DFTModelGlobalClockPaired
noncomputable section

/-- Both actual131 executions remain at their original addresses. The typed
run consumes compact prepared per-axis tapes, never a dense native-address heap. -/
theorem actual_execution {W n:ℕ} (as:List UniformGlobalDiagonalRowsMachine.Entry)
    (L:UniformGlobalDiagonalRowsMachine.Layout) (lane:Fin 9)
    (g:UniformGlobalTensorDiagonalMachine.Geometry W) (v v0:ℕ→ℕ→Scalar)
    (banks:Tape DFTModelGlobalCompactPools.Pool.T) (t:Tape Datum.T) (x:Fin n→ℂ) (s s0:State)
    (same:StateMatch s s0)
    (sameB:g.B=L.B) (sameRows:g.row=L.rows) (length:as.length=L.ell)
    (sameAxes:g.ell=L.ell) (total:UniformGlobalDiagonalRowsMachine.amount as=L.total)
    (volume:g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
    (pBelow:L.permutation+L.total≤g.natStack)
    (cBelow:L.coefficient+L.total≤g.scalarStack)
    (sourceSeparate:g.source+W*g.volume≤L.coefficient ∨ L.coefficient+L.total≤g.source)
    (rowHeader:UniformGlobalDiagonalRowsMachine.Header L lane s)
    (directory:UniformGlobalDiagonalRowsMachine.Directory L.directory as 0 s)
    (pools:UniformGlobalDiagonalRowsMachine.Pools as s)
    (typedPools:DFTModelGlobalCompactPools.PoolValues as banks)
    (poolBound:∀a∈as,a.pool+9*a.radix≤L.coefficient)
    (tensorHeader:UniformGlobalTensorDiagonalMachine.Header g s)
    (source:UniformGlobalTensorDiagonalMachine.Source g v s)
    (baseline:UniformGlobalTensorDiagonalMachine.Source g v0 s0)
    (encoded:DFTModelGlobalClockPaired.Source g v v0 t) (two:∀a∈as,2≤a.radix)
    (code:131≤L.B) (pc:s.pc=0) (wb:WordBound L.B s) :
    ∃u u0,
      BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x L.B s
        (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u ∧
      BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n (fun _=>0) L.B s0
        (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u0 ∧
      StateMatch u u0 ∧ u.pc=130 ∧ SourceFrame L g s u ∧ SourceFrame L g s0 u0 ∧
      Output g (run DFTModelGlobalCompactPoolsEvent.program (W,((lane.val,banks),t))).val u u0 ∧
      (run DFTModelGlobalCompactPoolsEvent.program (W,((lane.val,banks),t))).valid ∧
      (run DFTModelGlobalCompactPoolsEvent.program (W,((lane.val,banks),t))).work≤
        200*(9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) ∧
      (run DFTModelGlobalCompactPoolsEvent.program (W,((lane.val,banks),t))).peak≤L.B := by
  obtain ⟨u,u0,run,run0,matched,up,frame,frame0,output,_,_,_⟩:=
    DFTModelGlobalClockPaired.actual_execution as L lane g v v0 t x s s0 same
      sameB sameRows length sameAxes total volume pBelow cBelow sourceSeparate
      rowHeader directory pools poolBound tensorHeader source baseline encoded two code pc wb
  have countFit:as.length≤L.B:=by
    have h:=g.natStackBound
    rw [sameAxes,sameB] at h
    omega
  have volumeFit:W*(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod≤L.B:=by
    have h:=g.destinationBound
    rw [sameB,volume] at h
    omega
  have poolFit:∀a∈as,9*a.radix≤L.B:=by
    intro a ha
    have h:=g.scalarStackBound
    rw [sameB] at h
    have p:=poolBound a ha
    omega
  obtain ⟨value,valid,work,peak⟩:=DFTModelGlobalCompactPoolsEvent.program_contract W L.B
    as lane L.permutation L.coefficient banks t typedPools g.positive two countFit volumeFit poolFit
  refine ⟨u,u0,run,run0,matched,up,frame,frame0,?_,valid,?_,peak⟩
  · rw [value];exact output
  · have vc:=volume_le_treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)
    have mul:=Nat.mul_le_mul_left W vc
    rw [total,length] at work
    nlinarith

end
end ExactFourierCircuits.DFTModelGlobalCompactPoolsPaired
