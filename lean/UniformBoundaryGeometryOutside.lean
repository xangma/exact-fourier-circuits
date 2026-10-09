import UniformBoundaryCallerOutside
import UniformFourierAxisBoundaryBindings
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisGeometry
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
noncomputable section

theorem boundary_execution_outside(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n))
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
  (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) x s u ∧
 (∀z,(z<(WS.axis c n j).selected∨(WS.axis c n j).phase≤z)→u.natHeap z=s.natHeap z):=by
 have g:=geometry c hn j
 obtain ⟨u,result,outside⟩:=UniformBoundaryCallerOutside.retained_execution_outside j q x s retained
  (boundary_arguments c n j time q s h pool source clock lane) (boundary_workspace c n j s h)
  g.radix g.sourceBelow g.sourceFit g.selectedBoundary g.boundaryFit g.boundaryPoolFit
  (by have:=g.code;omega) pc wb
 refine ⟨u,result,?_⟩
 intro z hz
 have layout:=UniformFourierAxisWorkspace.axis_geometry c n j
 exact outside z (by omega)

end
end ExactFourierCircuits.UniformFourierAxisGeometry
