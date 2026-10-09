import UniformAxisBoundaryClock

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundarySelectedClock
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformReflectedFourierCalendar
open UniformBoundaryDiagonalMachine UniformFourierAxisPrepareBoundary

def depth (r:ℕ):ℕ:=UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)

lemma toeplitz_length (r:ℕ)(omega:ℂ):
 (toeplitz r (NewtonFourier.invH omega) (by simp)).length=depth r:=
 UniformLocalCacheTiming.render_duration _ _ _

lemma selected_boundary {r:ℕ}(positive:0<r){omega:ℂ}(hroot:IsPrimitiveRoot omega r)
 (g:ℕ)(q:Fin 3)(actual:FamilyAt (depth r) g q):
 (selected positive hroot g).matrix=Matrix.diagonal (fun x:Fin r=>UniformBoundaryDiagonalMachine.family omega q x.val):=by
 have len:=toeplitz_length r omega
 rcases actual with ⟨clock,lane⟩|⟨clock,lane⟩|⟨clock,lane⟩
 · have eq:q=0:=Fin.ext lane
   subst q
   simp only[family_H]
   rcases clock with clock|clock
   · subst g
     exact UniformAxisBoundaryClock.full_start ..
   · rw[←len] at clock
     subst g
     exact UniformAxisBoundaryClock.full_finish ..
 · have eq:q=1:=Fin.ext lane
   subst q
   simp only[family_scale]
   rw[←len] at clock
   rcases clock with clock|clock <;>subst g
   · exact UniformAxisBoundaryClock.full_right_one ..
   · exact UniformAxisBoundaryClock.full_right_two ..
 · have eq:q=2:=Fin.ext lane
   subst q
   simp only[family_inverseDiagonal]
   rw[←len] at clock
   subst g
   exact UniformAxisBoundaryClock.full_delta ..

lemma selected_inactive {r:ℕ}(positive:0<r){omega:ℂ}(hroot:IsPrimitiveRoot omega r)
 (g:ℕ)(inactive:2*depth r+5≤g):(selected positive hroot g).matrix=1:=by
 rw[←toeplitz_length r omega] at inactive
 exact UniformAxisBoundaryClock.full_inactive _ _ _ _ _ _ _ _ g inactive

lemma specified_boundary {r:ℕ}(positive:0<r)(g:ℕ)(q:Fin 3)
 (actual:FamilyAt (depth r) g q):
 (specified r g).matrix=Matrix.diagonal (fun x:Fin r=>UniformBoundaryDiagonalMachine.family (zeta r) q x.val):=by
 simp only[specified,dite_eq_left positive]
 exact selected_boundary positive (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt positive)) g q actual

lemma specified_inactive {r:ℕ}(positive:0<r)(g:ℕ)(inactive:2*depth r+5≤g):
 (specified r g).matrix=1:=by
 simp only[specified,dite_eq_left positive]
 exact selected_inactive positive (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt positive)) g inactive

end
end ExactFourierCircuits.UniformAxisBoundarySelectedClock
