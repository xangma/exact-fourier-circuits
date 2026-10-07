import KernelIdentities

/- General algebra for the projection and framed network in network.py.
   These statements do not certify the network's combinatorial data or budget. -/
namespace ExactFourierCircuits.Projection
noncomputable section

section Pullback
variable {H K ι : Type*} [AddCommGroup H] [AddCommGroup K]

def pullback (L : H →+ K) (f : K → ℂ) : H → ℂ := f ∘ L

def translate {T : Type*} [Add T] (z : T) (f : T → ℂ) : T → ℂ :=
  fun x => f (x + z)

def directionalC {T : Type*} [Add T] (z : T) (f : T → ℂ) : T → ℂ :=
  fun x => ExactFourierCircuits.a * f x + ExactFourierCircuits.b * f (x + z)

theorem pullback_translate (L : H →+ K) (z : H) (f : K → ℂ) :
    pullback L (translate (L z) f) = translate z (pullback L f) := by
  funext x
  simp [pullback, translate, map_add]

theorem pullback_directionalC (L : H →+ K) (z : H) (f : K → ℂ) :
    pullback L (directionalC (L z) f) = directionalC z (pullback L f) := by
  funext x
  simp [pullback, directionalC, map_add]

/-- On a direction of additive order two, swap*C has coefficients (b,a). -/
def inverseDirectionalC {T : Type*} [Add T] (z : T) (f : T → ℂ) : T → ℂ :=
  fun x => ExactFourierCircuits.b * f x + ExactFourierCircuits.a * f (x + z)

theorem pullback_inverseDirectionalC (L : H →+ K) (z : H) (f : K → ℂ) :
    pullback L (inverseDirectionalC (L z) f) = inverseDirectionalC z (pullback L f) := by
  funext x
  simp [pullback, inverseDirectionalC, map_add]

/-- The stated (b,a) operator is genuinely a two-sided inverse on two-torsion. -/
theorem directionalC_inverse (z : H) (hz : z + z = 0) (f : H → ℂ) :
    directionalC z (inverseDirectionalC z f) = f ∧
      inverseDirectionalC z (directionalC z f) = f := by
  constructor <;> funext x
  all_goals
    simp only [directionalC, inverseDirectionalC, add_assoc, hz, add_zero]
    unfold ExactFourierCircuits.a ExactFourierCircuits.b
    ring_nf
    simp [Complex.I_sq]
    ring

theorem pullback_injective (L : H →+ K) (hL : Function.Surjective L) :
    Function.Injective (pullback L) := by
  intro f g hfg
  funext y
  obtain ⟨x, rfl⟩ := hL y
  exact congrFun hfg x

def rolePullback (L : H →+ K) (f : ι → K → ℂ) : ι → H → ℂ :=
  fun i => pullback L (f i)

def pointwise {T : Type*} (gate : (ι → ℂ) → (ι → ℂ))
    (f : ι → T → ℂ) : ι → T → ℂ :=
  fun i x => gate (fun j => f j x) i

/-- Any pointwise scalar-role gate, hence any linear scalar-role shear, lifts. -/
theorem pullback_pointwise (L : H →+ K) (gate : (ι → ℂ) → (ι → ℂ))
    (f : ι → K → ℂ) :
    rolePullback L (pointwise gate f) = pointwise gate (rolePullback L f) := rfl
end Pullback

section Words
variable {X Y : Type*}

def runWord : List (X → X) → X → X
  | [], x => x
  | g :: gs, x => runWord gs (g x)

theorem intertwines_comp (P : X → Y) (g₁ g₂ : X → X) (G₁ G₂ : Y → Y)
    (h₁ : ∀ x, P (g₁ x) = G₁ (P x)) (h₂ : ∀ x, P (g₂ x) = G₂ (P x)) :
    ∀ x, P ((g₂ ∘ g₁) x) = (G₂ ∘ G₁) (P x) := by
  intro x
  simp only [Function.comp_apply, h₂, h₁]

/-- Gate-by-gate intertwining preserves any finite chronological word. -/
theorem intertwines_runWord (P : X → Y)
    (small : List (X → X)) (large : List (Y → Y))
    (h : List.Forall₂ (fun g G => ∀ x, P (g x) = G (P x)) small large) :
    ∀ x, P (runWord small x) = runWord large (P x) := by
  induction h with
  | nil => intro x; rfl
  | @cons g G gs Gs hgate htail ih =>
    intro x
    simp only [runWord]
    rw [ih, hgate]

def runStages (gates : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => gates n (runStages gates n x)

def framedGate (frames : ℕ → X ≃ X) (gates : ℕ → X → X) (n : ℕ) (x : X) : X :=
  (frames (n + 1)).symm (gates n (frames n x))

lemma frame_telescoping_apply (frames : ℕ → X ≃ X) (gates : ℕ → X → X)
    (n : ℕ) (x : X) :
    frames n (runStages (framedGate frames gates) n x) =
      runStages gates n (frames 0 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runStages, framedGate, Equiv.apply_symm_apply]
    rw [ih]

/-- All intermediate frames cancel; only the first and final frames remain. -/
theorem frame_telescoping (frames : ℕ → X ≃ X) (gates : ℕ → X → X)
    (n : ℕ) (x : X) :
    runStages (framedGate frames gates) n x =
      (frames n).symm (runStages gates n (frames 0 x)) := by
  apply (frames n).injective
  rw [Equiv.apply_symm_apply]
  exact frame_telescoping_apply frames gates n x
end Words

section DirtyAuxiliaries
variable {𝕜 X A C : Type*} [CommRing 𝕜]
  [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup A] [Module 𝕜 A]
  [AddCommGroup C] [Module 𝕜 C]

@[ext] structure DirtyState (X A C : Type*) where
  x : X
  y : X
  auxiliaryA : A
  auxiliaryC : C

/-- Eight chronological rows. Both auxiliary banks start with arbitrary data. -/
def eightRows (ε : 𝕜) (V : X →ₗ[𝕜] A) (G : X →ₗ[𝕜] C)
    (J : A →ₗ[𝕜] X) (R : C →ₗ[𝕜] X) (s : DirtyState X A C) : DirtyState X A C :=
  let y1 := s.y - ε • J s.auxiliaryA
  let y2 := y1 - ε • R s.auxiliaryC
  let a3 := s.auxiliaryA + V s.x
  let c4 := s.auxiliaryC + G s.x
  let y5 := y2 + ε • R c4
  let y6 := y5 + ε • J a3
  let c7 := c4 - G s.x
  let a8 := a3 - V s.x
  ⟨s.x, y6, a8, c7⟩

theorem eightRows_identity (ε : 𝕜) (V : X →ₗ[𝕜] A) (G : X →ₗ[𝕜] C)
    (J : A →ₗ[𝕜] X) (R : C →ₗ[𝕜] X)
    (h : R.comp G + J.comp V = LinearMap.id) (s : DirtyState X A C) :
    eightRows ε V G J R s = ⟨s.x, s.y + ε • s.x, s.auxiliaryA, s.auxiliaryC⟩ := by
  have hx : R (G s.x) + J (V s.x) = s.x := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      congrArg (fun T : X →ₗ[𝕜] X => T s.x) h
  apply DirtyState.ext
  · rfl
  · change s.y - ε • J s.auxiliaryA - ε • R s.auxiliaryC +
      ε • R (s.auxiliaryC + G s.x) + ε • J (s.auxiliaryA + V s.x) =
        s.y + ε • s.x
    calc
      _ = s.y + ε • (R (G s.x) + J (V s.x)) := by
        simp only [map_add, smul_add]
        abel
      _ = _ := by rw [hx]
  · simp [eightRows]
  · simp [eightRows]

def swapBanks (s : DirtyState X A C) : DirtyState X A C :=
  ⟨s.y, s.x, s.auxiliaryA, s.auxiliaryC⟩

/-- Three elementary bank shears yield (-y,x), while restoring all auxiliary data. -/
theorem scalar_exchange (V : X →ₗ[𝕜] A) (G : X →ₗ[𝕜] C)
    (J : A →ₗ[𝕜] X) (R : C →ₗ[𝕜] X)
    (h : R.comp G + J.comp V = LinearMap.id) (s : DirtyState X A C) :
    eightRows 1 V G J R
      (swapBanks (eightRows (-1) V G J R (swapBanks (eightRows 1 V G J R s)))) =
        ⟨-s.y, s.x, s.auxiliaryA, s.auxiliaryC⟩ := by
  rw [eightRows_identity 1 V G J R h,
      eightRows_identity (-1) V G J R h,
      eightRows_identity 1 V G J R h]
  ext <;> simp [swapBanks]
end DirtyAuxiliaries

end
end ExactFourierCircuits.Projection
