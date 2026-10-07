import ScalarNetwork

/- The three physical stages use different tensor axes and fresh auxiliary
   banks. This module certifies their scalar action for arbitrary dirty data. -/
namespace ExactFourierCircuits.TripleNetwork
open ScalarNetwork
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Bank (α : Type*) := Fin 3 → Triple α
abbrev Profile (α : Type*) (p : Fin 3) := {j : Fin 3 // j ≠ p} → Triple α

def axisCoordinates (p : Fin 3) : Bank α ≃ Triple α × Profile α p :=
  Equiv.funSplitAt p (Triple α)

@[ext] structure State (α : Type*) [DecidableEq α] where
  x : Bank α → ℂ
  y : Bank α → ℂ
  side : (p : Fin 3) → Profile α p → Edge α → ℂ
  center : (p : Fin 3) → Profile α p → Option α → ℂ

def slice (p : Fin 3) (profile : Profile α p) (s : State α) :
    Projection.DirtyState (Triple α → ℂ) (Edge α → ℂ) (Option α → ℂ) :=
  ⟨fun t => s.x ((axisCoordinates p).symm (t, profile)),
   fun t => s.y ((axisCoordinates p).symm (t, profile)), s.side p profile, s.center p profile⟩

def invocation (ε : ℂ) (p : Fin 3) (profile : Profile α p) (s : State α) :=
  Projection.eightRows ε (Matrix.mulVecLin (V (α := α))) (Matrix.mulVecLin G)
    (Matrix.mulVecLin J) (Matrix.mulVecLin R) (slice p profile s)

/-- Concurrent invocations at this axis have disjoint profile and auxiliary
    coordinates. Function.update preserves the other two stages' dirty banks. -/
def stage (ε : ℂ) (p : Fin 3) (s : State α) : State α :=
  ⟨fun d => (invocation ε p ((axisCoordinates p d).2) s).x ((axisCoordinates p d).1),
   fun d => (invocation ε p ((axisCoordinates p d).2) s).y ((axisCoordinates p d).1),
   Function.update s.side p (fun profile => (invocation ε p profile s).auxiliaryA),
   Function.update s.center p (fun profile => (invocation ε p profile s).auxiliaryC)⟩

theorem stage_identity (ε : ℂ) (p : Fin 3) (s : State α) :
    stage ε p s = ⟨s.x, s.y + ε • s.x, s.side, s.center⟩ := by
  have hi (profile : Profile α p) : invocation ε p profile s =
      ⟨(slice p profile s).x, (slice p profile s).y + ε • (slice p profile s).x,
       s.side p profile, s.center p profile⟩ := invocation_dirty_identity ε _
  apply State.ext
  · funext d
    simp only [stage, hi, slice, Prod.mk.eta, Equiv.symm_apply_apply]
  · funext d
    simp only [stage, hi, slice, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · simp only [stage, hi, Function.update_eq_self]
  · simp only [stage, hi, Function.update_eq_self]

def swap (s : State α) : State α := ⟨s.y, s.x, s.side, s.center⟩

/-- Stage two's logical ordered pair is the reverse of its physical Y/X pair. -/
def reverseEdge (e : Edge α) : Edge α :=
  ⟨(e.val.2, e.val.1), by simpa [neighboring, Finset.inter_comm] using e.property⟩

omit [Fintype α] in
@[simp] theorem reverseEdge_involutive (e : Edge α) : reverseEdge (reverseEdge e) = e := by
  cases e
  rfl

/-- Literal reversal of all eight updates, with reversed signs. This preserves
    the physical touch sequence required by the binary gate labels. -/
def reverseRows (ε : ℂ)
    (s : Projection.DirtyState (Triple α → ℂ) (Edge α → ℂ) (Option α → ℂ)) :=
  let a1 := s.auxiliaryA + V.mulVec s.x
  let c2 := s.auxiliaryC + G.mulVec s.x
  let y3 := s.y - ε • J.mulVec a1
  let y4 := y3 - ε • R.mulVec c2
  let c5 := c2 - G.mulVec s.x
  let a6 := a1 - V.mulVec s.x
  let y7 := y4 + ε • R.mulVec c5
  let y8 := y7 + ε • J.mulVec a6
  Projection.DirtyState.mk s.x y8 a6 c5

theorem reverseRows_identity (ε : ℂ)
    (s : Projection.DirtyState (Triple α → ℂ) (Edge α → ℂ) (Option α → ℂ)) :
    reverseRows ε s = ⟨s.x, s.y - ε • s.x, s.auxiliaryA, s.auxiliaryC⟩ := by
  have hx : R.mulVec (G.mulVec s.x) + J.mulVec (V.mulVec s.x) = s.x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply] using
        congrArg (fun T : (Triple α → ℂ) →ₗ[ℂ] (Triple α → ℂ) => T s.x)
          (incidence_linear_identity (α := α))
  apply Projection.DirtyState.ext
  · rfl
  · change s.y - ε • J.mulVec (s.auxiliaryA + V.mulVec s.x) -
      ε • R.mulVec (s.auxiliaryC + G.mulVec s.x) +
      ε • R.mulVec (s.auxiliaryC + G.mulVec s.x - G.mulVec s.x) +
      ε • J.mulVec (s.auxiliaryA + V.mulVec s.x - V.mulVec s.x) = _
    simp only [add_sub_cancel_right, Matrix.mulVec_add, smul_add]
    calc
      _ = s.y - ε • (R.mulVec (G.mulVec s.x) + J.mulVec (V.mulVec s.x)) := by
        simp only [smul_add]
        abel
      _ = _ := by rw [hx]
  · simp [reverseRows]
  · simp [reverseRows]

def reverseInvocation (ε : ℂ) (p : Fin 3) (profile : Profile α p) (s : State α) :=
  reverseRows ε
    ⟨(slice p profile s).x, (slice p profile s).y,
     fun e => s.side p profile (reverseEdge e), s.center p profile⟩

def reverseStage (ε : ℂ) (p : Fin 3) (s : State α) : State α :=
  ⟨fun d => (reverseInvocation ε p ((axisCoordinates p d).2) s).x ((axisCoordinates p d).1),
   fun d => (reverseInvocation ε p ((axisCoordinates p d).2) s).y ((axisCoordinates p d).1),
   Function.update s.side p (fun profile e =>
     (reverseInvocation ε p profile s).auxiliaryA (reverseEdge e)),
   Function.update s.center p (fun profile => (reverseInvocation ε p profile s).auxiliaryC)⟩

theorem reverseStage_identity (ε : ℂ) (p : Fin 3) (s : State α) :
    reverseStage ε p s = ⟨s.x, s.y - ε • s.x, s.side, s.center⟩ := by
  apply State.ext
  · funext d
    simp [reverseStage, reverseInvocation, reverseRows_identity, slice]
  · funext d
    simp [reverseStage, reverseInvocation, reverseRows_identity, slice]
  · simp [reverseStage, reverseInvocation, reverseRows_identity]
  · simp [reverseStage, reverseInvocation, reverseRows_identity]

def scalarNetwork (s : State α) : State α :=
  stage 1 2 (swap (reverseStage 1 1 (swap (stage 1 0 s))))

/-- The actual three-axis scalar network sends (X,Y) to (-Y,X) and restores
    every side and central role, independently of their initial values. -/
theorem scalarNetwork_identity (s : State α) :
    scalarNetwork s = ⟨-s.y, s.x, s.side, s.center⟩ := by
  rw [scalarNetwork, stage_identity, reverseStage_identity, stage_identity]
  apply State.ext <;> simp [swap]

omit [DecidableEq α] in
theorem profile_card (p : Fin 3) : Fintype.card (Profile α p) =
    (Nat.choose (Fintype.card α) 3) ^ 2 := by
  have hp : Fintype.card {j : Fin 3 // j ≠ p} = 2 := by
    simp [Fintype.card_subtype_compl]
  rw [Fintype.card_fun, triple_card, hp]

omit [DecidableEq α] in
theorem bank_card : Fintype.card (Bank α) = (Nat.choose (Fintype.card α) 3) ^ 3 := by
  rw [Fintype.card_fun, triple_card, Fintype.card_fin]

end
end ExactFourierCircuits.TripleNetwork
