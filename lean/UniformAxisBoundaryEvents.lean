import UniformFourierAxisPrepareBoundary
import UniformFourierAxisPrepareInactive
import UniformCalendarAxisAction
import UniformReflectedFourierCalendar

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundaryEvents
noncomputable section
open UniformMachine UniformGlobalCalendarDispatch OAI.ExactFourier
open UniformCalendarAxisAction UniformBoundaryDiagonalMachine

/-- The one actual boundary ABI is a diagonal event, with the retained seed lane. -/
def event (r pool arena:ℕ)(omega:ℂ)(q:Fin 3):Event where
 descriptor:=UniformBoundaryDiagonalCaller.descriptor r pool arena
 phase:=.diagonal 0
 factor:=family omega q
 records:=fun _=>(0,0)

lemma event_cached {r pool arena O T B:ℕ}{omega:ℂ}{q:Fin 3}{s:State}
 (positive:2≤r)(stored:Stored (UniformBoundaryDiagonalCaller.descriptor r pool arena) s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools [poolEntry r pool positive omega q] s)
 (entryFit:arena+3*r+11≤T)(poolFit:pool+9*r≤O):
 CachedEvent r O T B (event r pool arena omega q) s:=by
 constructor
 · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
 · exact stored
 · intro i hi
   have cell:=pools (poolEntry r pool positive omega q) (by simp) 0 ⟨i,hi⟩
   norm_num only[event,Source,UniformBoundaryDiagonalCaller.descriptor,poolEntry] at cell ⊢
   exact cell
 · change arena+3*r+4+7≤T
   omega
 · exact poolFit
 · change arena+2*(r-r)≤T
   omega
 · change 2*(r-r)≤r
   omega
 · intro i hi
   change i<r-r at hi
   omega

lemma selections {r pool arena A:ℕ}{omega:ℂ}{q:Fin 3}{s:State}
 (actual:Selected A 0 (UniformBoundaryDiagonalCaller.descriptor r pool arena) s):
 Selections A 0 [event r pool arena omega q] s:=⟨actual,True.intro⟩

def action (r pool arena:ℕ)(omega:ℂ)(q:Fin 3):
 Action r [event r pool arena omega q] (Matrix.diagonal (fun x:Fin r=>family omega q x.val)) where
 position:=⟨fun i=>Fin.elim0 i.1,by intro i;exact Fin.elim0 i.1⟩
 rows:=by
  change []=List.ofFn _
  symm
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw[List.length_ofFn]
  rfl
 matrix:=by
  have kernel:Embedded.matrix
    (⟨fun i:Σ _:Fin (callTotal r [event r pool arena omega q]),Fin 2=>Fin.elim0 i.1,
     by intro i;exact Fin.elim0 i.1⟩: (Σ _:Fin (callTotal r [event r pool arena omega q]),Fin 2)↪Fin r)
    (Matrix.blockDiagonal' (fun _:Fin (callTotal r [event r pool arena omega q])=>C))=1:=by
   have empty:Matrix.blockDiagonal' (fun _:Fin (callTotal r [event r pool arena omega q])=>C)=1:=by
    ext ⟨i,j⟩;exact Fin.elim0 i
   rw[empty,Embedded.matrix_one]
  rw[kernel,Matrix.mul_one]
  congr 1
  funext x
  simp only[foldValues,event,phaseFactor,mul_one]

end
end ExactFourierCircuits.UniformAxisBoundaryEvents
