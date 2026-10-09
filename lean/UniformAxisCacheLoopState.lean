import UniformAxisCacheAxisExecution
import UniformAxisCacheTail
import UniformAxisCacheAdvanceInputs
import UniformAxisCacheFinalEnds
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, local preparation accounting in Proposition 4.2 proof, PDF p. 20 (`prop:tensor-fourier`); §5.3, shared local scalar preparation, p. 23.

The paper does not prescribe cache heap layouts. Prefix retention, output/root preservation and final frontiers are implementation invariants for preparing all axes once before repeated synchronized slots.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheLoopState
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheContents UniformAxisCachePhysical
noncomputable section

def All (c:A.Constants) (n:ℕ) (hn:0<n) (upto:ℕ) (s:State):Prop:=
 ∀i:Fin (C.ell n),i.val<upto→ Contents c n hn i s

lemma All.transport {c n hn upto s u} (h:All c n hn upto s)
 (nh:u.natHeap=s.natHeap) (sh:u.scalarHeap=s.scalarHeap):All c n hn upto u:=
 fun i hi=>UniformAxisCacheContents.transport (h i hi) (Heaps.of_eq nh sh)

lemma All.step {c n hn j x s u} (h:All c n hn j.val s)
 (out:UniformAxisCacheAxisExecution.Result c n hn j x s u):All c n hn (j.val+1) u:=by
 intro i hi
 by_cases old:i.val<j.val
 · exact UniformAxisCacheContents.transport (h i old) (out.previous i old)
 · have same:i=j:=Fin.ext (by omega)
   subst i
   exact out.contents

lemma allocation_transport {r N S:ℕ} {s u:State}
 (h:UniformAxisCacheAllocationMachine.Result r N S s)
 (keep:∀q,6700≤ q→ q<6900→ u.natReg q=s.natReg q):UniformAxisCacheAllocationMachine.Result r N S u:=by
 constructor
 all_goals first
 | exact (keep _ (by omega) (by omega)).trans h.tasks
 | exact (keep _ (by omega) (by omega)).trans h.nodes
 | exact (keep _ (by omega) (by omega)).trans h.requests
 | exact (keep _ (by omega) (by omega)).trans h.control
 | exact (keep _ (by omega) (by omega)).trans h.leafForward
 | exact (keep _ (by omega) (by omega)).trans h.leafTranspose
 | exact (keep _ (by omega) (by omega)).trans h.durations
 | exact (keep _ (by omega) (by omega)).trans h.nodeStarts
 | exact (keep _ (by omega) (by omega)).trans h.requestStarts
 | exact (keep _ (by omega) (by omega)).trans h.endNat
 | exact (keep _ (by omega) (by omega)).trans h.pool
 | exact (keep _ (by omega) (by omega)).trans h.endScalar

def maxBudget (c:A.Constants) (n:ℕ):ℕ:=
 Finset.univ.sup (fun j:Fin (C.ell n)=>UniformAxisCacheAxisExecution.budget c n j+11)
lemma budget_le (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):
 UniformAxisCacheAxisExecution.budget c n j+11≤ maxBudget c n:=by
 unfold maxBudget
 exact Finset.le_sup (f:=fun i:Fin (C.ell n)=>UniformAxisCacheAxisExecution.budget c n i+11) (Finset.mem_univ j)

structure Final (c:A.Constants) (n:ℕ) (hn:0<n) (x:Fin n→ ℂ) (s u:State):Prop where
 input:Inputs n x u
 bank:UniformLocalRectangleWorkspaceHeaders.Bank n u
 all:All c n hn (C.ell n) u
 clock:u.natReg 5921=UniformFourierClockBounds.horizon n
 savedNat:u.natReg 6909=s.natReg 6909
 savedScalar:u.natReg 6910=s.natReg 6910
 natEnd:u.natReg 6819=UniformJointCacheAllocation.natEnd c n
 scalarEnd:u.natReg 6821=UniformJointCacheAllocation.scalarEnd c n
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

end
end ExactFourierCircuits.UniformAxisCacheLoopState
