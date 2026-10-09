import UniformCalendarCallReindex
import UniformCalendarRenderMatching
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalMatchingPhase
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformReplayPrint UniformLayerSnapshot
open UniformGlobalCalendarMatchingPhase UniformGlobalCalendarPhases UniformGlobalMatchingScaleMachine
open UniformGlobalMatchingScaleBankBridge UniformColoring

theorem phase_congr {v R : ℕ} (bank : Fin R→ℂ)
 {W U : List (ShearCode (Fin v) R)} (eq : W=U) (hw : Matching W) (hu : Matching U) (p : Phase) :
 (phaseSnapshot bank W hw p).matrix=(phaseSnapshot bank U hu p).matrix:=by
 subst U
 rfl

/-- Reindexing the physical matching cannot change any of its native factors. -/
theorem nativeFactor_reindex {M N : ℕ} (E : Fin M→Edge) (F : Fin N→Edge)
 (mu : Fin M→ℂ) (nu : Fin N→ℂ) (hm : UniformMatchingAxisTableMachine.Matching E)
 (hn : UniformMatchingAxisTableMachine.Matching F) (e : Fin N≃Fin M)
 (eqE : ∀i,F i=E (e i)) (eqMu : ∀i,nu i=mu (e i)) (lane : Fin 9) (x : ℕ) :
 nativeFactor F nu lane x=nativeFactor E mu lane x:=by
 by_cases hit : ∃i,Incident (F i) x
 · obtain ⟨i,hi|hi⟩:=hit
   · rw [←hi,nativeFactor_left F nu hn lane i,eqE i,nativeFactor_left E mu hm lane (e i),eqMu i]
   · rw [←hi,nativeFactor_right F nu hn lane i,eqE i,nativeFactor_right E mu hm lane (e i),eqMu i]
 · rw [nativeFactor_unused F nu lane x (by intro i hi;exact hit ⟨i,hi⟩)]
   symm
   apply nativeFactor_unused
   intro i hi
   apply hit
   refine ⟨e.symm i,?_⟩
   simpa only [eqE,Equiv.apply_symm_apply] using hi

/-- Every phase is invariant under an actual occurrence enumeration change.
Ordered destination/source endpoints and coefficients are preserved. -/
theorem phase_reindex {v R : ℕ} (bank : Fin R→ℂ)
 (W U : List (ShearCode (Fin v) R)) (hw : Matching W) (hu : Matching U)
 (e : Fin U.length≃Fin W.length) (get : ∀i,U.get i=W.get (e i)) (p : Phase) :
 (phaseSnapshot bank U hu p).matrix=(phaseSnapshot bank W hw p).matrix:=by
 cases p with
 | diagonal lane =>
  simp only [phaseSnapshot,Snapshot.ofDiagonal_matrix]
  congr 1
  funext i
  apply nativeFactor_reindex (edges W) (edges U) (coefficients bank W) (coefficients bank U)
   (edges_matching W hw) (edges_matching U hu) e
  · intro j;simp only [edges,get j]
  · intro j;unfold coefficients;rw[get j]
 | kernel =>
  simp only [phaseSnapshot,Snapshot.matrix,Matrix.diagonal_one,one_mul]
  apply UniformCalendarCallReindex.calls_matrix (matchingCalls W hw) e
  intro i side
  change Embedded.pair (U.get i).dst (U.get i).src (U.get i).different side=
   Embedded.pair (W.get (e i)).dst (W.get (e i)).src (W.get (e i)).different side
  simp only [get i]

def reverseOrder {α : Type} (W : List α) : Fin W.reverse.length≃Fin W.length:=
 (finCongr (List.length_reverse (as:=W))).trans Fin.revPerm

lemma reverseOrder_get {α : Type} (W : List α) (i : Fin W.reverse.length) :
 W.reverse.get i=W.get (reverseOrder W i):=by
 simp only [List.get_eq_getElem,List.getElem_reverse,reverseOrder,Equiv.trans_apply,
  finCongr_apply,Fin.revPerm_apply,Fin.val_rev,Fin.val_cast]
 congr 1
 omega

theorem phase_reverse {v R : ℕ} (bank : Fin R→ℂ)
 (W : List (ShearCode (Fin v) R)) (hw : Matching W) (hr : Matching W.reverse) (p : Phase) :
 (phaseSnapshot bank W.reverse hr p).matrix=(phaseSnapshot bank W hw p).matrix:=
 phase_reindex bank W W.reverse hw hr (reverseOrder W) (reverseOrder_get W) p

end
end ExactFourierCircuits.UniformCanonicalMatchingPhase
