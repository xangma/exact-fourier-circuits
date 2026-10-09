import UniformFinalClockOuterCore

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOuterRetention
open UniformMachine
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants

lemma Frame.tableArgs {n:ℕ}{s u:State}(h:Frame n s u)
 (old:UniformPhysicalCRTTableHeaders.Args c n s):UniformPhysicalCRTTableHeaders.Args c n u:=by
 constructor
 all_goals first
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.alpha
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.inverse
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.storage
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.axes
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.volume
 | exact ((h.natReg _ (by unfold RequiredNat;omega)).trans old.seed).trans
    (h.natReg _ (by unfold RequiredNat;omega)).symm
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.sourceAlpha
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.sourceBeta
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.destAlpha
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.destInverse
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.work

lemma Frame.table {n:ℕ}{s u:State}{x:Fin n→ℂ}(hn:0<n)(h:Frame n s u)
 (old:UniformFinalPhysicalTablePrefix.Result n x s):UniformFinalPhysicalTablePrefix.Result n x u:=
 ⟨h.core hn old.core,h.data hn old.data,
 fun i hi=>(h.natReg _ (by unfold RequiredNat;omega)).trans (old.headers i hi),
 (h.natReg _ (by unfold RequiredNat;omega)).trans old.source,h.tableArgs old.tableArgs,
 fun j=>(h.alpha j).trans (old.alpha j),fun j=>(h.inverse j).trans (old.inverse j)⟩

lemma Frame.header {n:ℕ}{s u:State}(h:Frame n s u)
 (old:UniformFinalMovementCaller.Header n s):UniformFinalMovementCaller.Header n u:=by
 constructor
 all_goals first
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.volume
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.source
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.target
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.storage
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.alpha
 | exact (h.natReg _ (by unfold RequiredNat;omega)).trans old.inverse

lemma Frame.tables {n:ℕ}{s u:State}(h:Frame n s u)
 (old:UniformFinalMovementCaller.Tables n s):UniformFinalMovementCaller.Tables n u:=
 ⟨fun j=>(h.alpha j).trans (old.alpha j),fun j=>(h.inverse j).trans (old.inverse j)⟩

end
end ExactFourierCircuits.UniformFinalClockOuterRetention

namespace ExactFourierCircuits.UniformFinalPhysicalTablePrefix
open UniformMachine
lemma Result.withPC {n pc:ℕ}{x:Fin n→ℂ}{s:State}(h:Result n x s):Result n x {s with pc:=pc}:=
 ⟨h.core.withPC,h.data.withPC,h.headers,h.source,
  ⟨h.tableArgs.alpha,h.tableArgs.inverse,h.tableArgs.storage,h.tableArgs.axes,h.tableArgs.volume,
   h.tableArgs.seed,h.tableArgs.sourceAlpha,h.tableArgs.sourceBeta,h.tableArgs.destAlpha,
   h.tableArgs.destInverse,h.tableArgs.work⟩,h.alpha,h.inverse⟩
end ExactFourierCircuits.UniformFinalPhysicalTablePrefix

namespace ExactFourierCircuits.UniformFinalMovementCaller
open UniformMachine
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants
lemma Header.of_table {n:ℕ}{x:Fin n→ℂ}{s:State}
 (h:UniformFinalPhysicalTablePrefix.Result n x s):Header n s:=by
 refine ⟨h.core.metadata.saved.workingLength,?_,?_,h.tableArgs.storage,h.tableArgs.alpha,h.tableArgs.inverse⟩
 · simpa only [UniformFinalMovementGeometry.S,UniformJointAllocationMachine.factors,List.getElem_cons_succ,
    List.getElem_cons_zero,Nat.reduceMul] using h.headers 6 (by omega)
 · simpa only [UniformFinalMovementGeometry.T,UniformJointAllocationMachine.factors,List.getElem_cons_succ,
    List.getElem_cons_zero,Nat.reduceMul] using h.headers 5 (by omega)
lemma Tables.of_table {n:ℕ}{x:Fin n→ℂ}{s:State}
 (h:UniformFinalPhysicalTablePrefix.Result n x s):Tables n s:=⟨h.alpha,h.inverse⟩
end
end ExactFourierCircuits.UniformFinalMovementCaller
