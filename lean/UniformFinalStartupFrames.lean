import UniformCacheLowProtected
import UniformJointAllocationMachine
import UniformJointCacheWorkspaceMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStartupFrames
open UniformMachine UniformAxisCachePreparationRetention UniformAllAxisSeedPreparation
noncomputable section
lemma core_transport {n:ℕ}{x:Fin n→ℂ}{s u:State} (h:Core n x s)
 (nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap)
 (saved:∀q,100≤q→q≤106→u.natReg q=s.natReg q)
 (header:∀q,200≤q→q≤209→u.natReg q=s.natReg q)
 (outputs:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):Core n x u:=by
 have f:UniformSeedRankCrossPreparation.PreservedFrame n s u:=
  ⟨fun q _=>congrFun nh q,fun q _=>congrFun sh q,saved,outputs,roots⟩
 refine ⟨?_,f.protected.metadata h.metadata,f.protected.operands h.operands,f.retained h.seed,?_⟩
 · exact ⟨(header _ (by omega) (by omega)).trans h.header.index,
    (header _ (by omega) (by omega)).trans h.header.offset,
    (header _ (by omega) (by omega)).trans h.header.count,
    (header _ (by omega) (by omega)).trans h.header.one,
    (header _ (by omega) (by omega)).trans h.header.directory,
    (header _ (by omega) (by omega)).trans h.header.zero⟩
 · exact UniformLocalRectangleCoefficientMachine.conjugate_retained h.conjugate
    (fun q _=>congrFun sh q) (fun q _=>congrFun nh q)
end
end ExactFourierCircuits.UniformFinalStartupFrames
