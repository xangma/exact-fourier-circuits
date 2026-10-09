import UniformFourierAxisGeometry
import UniformBoundaryDiagonalCaller
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisGeometry
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
noncomputable section

def natBase(c:Constants)(n:ℕ)(j:Fin (ell n)):ℕ:=
 UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val
def scalarBase(c:Constants)(n:ℕ)(j:Fin (ell n)):ℕ:=
 UniformGlobalCalendarArena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val

lemma boundary_arguments(c:Constants)(n:ℕ)(j:Fin (ell n))(time:ℕ)(q:Fin 3)(s:State)
 (h:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (natBase c n j) (scalarBase c n j) s)
 (pool:s.natReg 6020=slab c n)
 (source:s.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val)
 (clock:s.natReg 5920=time)(lane:s.natReg 7001=q.val):
 UniformBoundaryDiagonalMachine.Args (UniformAllAxisSeedPreparation.directoryBase n+2*j.val)
  q.val time (slab c n) (WS.axis c n j).boundary s:=
 ⟨source,lane,clock,pool,h.boundary⟩

lemma boundary_workspace(c:Constants)(n:ℕ)(j:Fin (ell n))(s:State)
 (h:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (natBase c n j) (scalarBase c n j) s):
 UniformBoundaryDiagonalCaller.Workspace (WS.axis c n j).selected (WS.axis c n j).boundary
  (WS.axis c n j).phase (WS.axis c n j).rawRows (WS.axis c n j).pool s:=
 ⟨h.selected,h.boundary,h.phase,h.rows,h.pool⟩

/-- Real charged workspace headers and retained original seed words instantiate
all boundary138 inputs and bounds. No supplied Args/Workspace/fit witness. -/
theorem boundary_execution(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n))
 (time:ℕ)(q:Fin 3)(x:Fin n→ℂ)(s:State)
 (h:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (natBase c n j) (scalarBase c n j) s)
 (retained:UniformAllAxisSeedPreparation.Retained n (ell n) s)
 (pool:s.natReg 6020=slab c n)
 (source:s.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val)
 (clock:s.natReg 5920=time)(lane:s.natReg 7001=q.val)(pc:s.pc=0)(wb:WordBound (envelope c n) s):
 ∃u,UniformBoundaryDiagonalCaller.Result n (envelope c n) (UniformAllAxisSeedPreparation.radix n j)
  time (slab c n) (WS.axis c n j).selected (WS.axis c n j).boundary (WS.axis c n j).phase
  (WS.axis c n j).rawRows (WS.axis c n j).pool (geometry c hn j).radix q
  (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) x s u:=by
 have g:=geometry c hn j
 exact UniformBoundaryDiagonalCaller.retained_execution j q x s retained
  (boundary_arguments c n j time q s h pool source clock lane) (boundary_workspace c n j s h)
  g.radix g.sourceBelow g.sourceFit g.selectedBoundary g.boundaryFit g.boundaryPoolFit
  (by have:=g.code;omega) pc wb
end
end ExactFourierCircuits.UniformFourierAxisGeometry
