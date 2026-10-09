import UniformAxisBoundaryBindings
import UniformAxisBoundarySelectedClock

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundarySemantics
noncomputable section
open UniformMachine UniformGlobalCalendarDispatch UniformCalendarAxisAction OAI.ExactFourier
open UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformAxisBoundarySelectedClock

/-- The actual retained boundary payload satisfies the common ordered-axis contract. -/
def boundary_action {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}
 {x:Fin n→ℂ}{s u:State}
 (actual:UniformFourierAxisPrepareBoundary.Result c n (depth (radix n j)) g hn j q x s u):
 Action (radix n j) (UniformAxisBoundaryBindings.events c n j q)
  (UniformReflectedFourierCalendar.specified (radix n j) g).matrix:=by
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2) (UniformFourierAxisGeometry.geometry c hn j).radix
 exact UniformCalendarAxisAction.congr (UniformAxisBoundaryEvents.action (radix n j) (slab c n)
  (UniformFourierAxisWorkspace.axis c n j).boundary (OAI.ExactFourier.zeta (radix n j)) q)
   (specified_boundary positive g q actual.family).symm

theorem boundary {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}
 {x:Fin n→ℂ}{s u:State}
 (actual:UniformFourierAxisPrepareBoundary.Result c n (depth (radix n j)) g hn j q x s u):
 Selections (UniformFourierAxisWorkspace.axis c n j).selected 0
  (UniformAxisBoundaryBindings.events c n j q) u ∧
 (∀e∈UniformAxisBoundaryBindings.events c n j q,
  CachedEvent (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
   (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e u) ∧
 Nonempty (Action (radix n j) (UniformAxisBoundaryBindings.events c n j q)
  (UniformReflectedFourierCalendar.specified (radix n j) g).matrix):=by
 have facts:=UniformAxisBoundaryBindings.factual actual
 exact ⟨facts.1,facts.2,⟨boundary_action actual⟩⟩

lemma inactive_clock {d g:ℕ}{u:State}
 (selected:UniformEpochSelectorMachine.Selected d g u)(mode:u.natReg 7080=2):2*d+5≤g:=by
 rcases selected with h|h|h|h|h|h
 · omega
 · omega
 · omega
 · omega
 · omega
 · exact h.1

def empty_action (r:ℕ):Action r [] 1 where
 position:=⟨fun i=>Fin.elim0 i.1,by intro i;exact Fin.elim0 i.1⟩
 rows:=by
  change []=List.ofFn _
  symm
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw[List.length_ofFn]
  rfl
 matrix:=by
  have kernel:Embedded.matrix
   (⟨fun i:Σ _:Fin (callTotal r []),Fin 2=>Fin.elim0 i.1,
     by intro i;exact Fin.elim0 i.1⟩:(Σ _:Fin (callTotal r []),Fin 2)↪Fin r)
   (Matrix.blockDiagonal' (fun _:Fin (callTotal r [])=>C))=1:=by
   have empty:Matrix.blockDiagonal' (fun _:Fin (callTotal r [])=>C)=1:=by
    ext ⟨i,j⟩;exact Fin.elim0 i
   rw[empty,Embedded.matrix_one]
  rw[kernel,Matrix.mul_one]
  exact Matrix.diagonal_one

/-- Mode two is derived from the real epoch result and renders the identity. -/
def inactive_action {c:Constants}{n g:ℕ}(hn:0<n){j:Fin (ell n)}
 {x:Fin n→ℂ}{s u:State}
 (actual:UniformFourierAxisPrepareInactive.Result c n (depth (radix n j)) g j x s u):
 Action (radix n j) [] (UniformReflectedFourierCalendar.specified (radix n j) g).matrix:=by
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2) (UniformFourierAxisGeometry.geometry c hn j).radix
 exact UniformCalendarAxisAction.congr (empty_action (radix n j))
  (specified_inactive positive g (inactive_clock actual.selected actual.mode)).symm

theorem inactive {c:Constants}{n g:ℕ}(hn:0<n){j:Fin (ell n)}
 {x:Fin n→ℂ}{s u:State}
 (actual:UniformFourierAxisPrepareInactive.Result c n (depth (radix n j)) g j x s u):
 Selections (UniformFourierAxisWorkspace.axis c n j).selected 0 [] u ∧
 (∀e∈([]:List Event),CachedEvent (radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e u) ∧
 Nonempty (Action (radix n j) [] (UniformReflectedFourierCalendar.specified (radix n j) g).matrix):=by
 exact ⟨True.intro,by simp,⟨inactive_action hn actual⟩⟩

end
end ExactFourierCircuits.UniformAxisBoundarySemantics
