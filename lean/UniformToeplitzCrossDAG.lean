import UniformConvolutionDAG
import OAI.Computability.FourierCircuit.ToeplitzCross

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.3, Lemma 3.4, equations (3.5)–(3.10), PDF pp. 15–16 (loc:cross, loc:displacement-entry, loc:displacement, loc:reconstruction, loc:two-convolutions, loc:chunk-bounds).
This is the actual six-convolution displacement DAG, with coefficients read from a shared bank. Bank production and physical replay are separately proved; generic recurrence hypotheses are discharged for the Toeplitz specialization.
-/

set_option autoImplicit false

/-! Actual prepared-reference rank-three displacement compiler. Preparation of
its shared power/spectrum bank is a separate charged phase. -/
namespace ExactFourierCircuits.UniformToeplitzCrossDAG
open scoped BigOperators
open OAI.ExactFourier
open UniformReplayPrint
open UniformRadixTwoDAG (width count)

/-- Only scalar register addresses change; no scalar is inspected. -/
def mapCoefficient {r s : ℕ} (f : Fin r → Fin s) : Coefficient r → Coefficient s
  | .rational q => .rational q
  | .prepared i neg => .prepared (f i) neg

def mapGate {r s w w' : ℕ} (coeff : Fin r → Fin s) (refs : Fin w → Fin w') :
    UniformReplayPrint.Gate r w → UniformReplayPrint.Gate s w'
  | .add a b => .add (refs a) (refs b)
  | .sub a b => .sub (refs a) (refs b)
  | .scale c a => .scale (mapCoefficient coeff c) (refs a)

def mapProgram {r s n : ℕ} (coeff : Fin r → Fin s) :
    {t : ℕ} → UniformReplayPrint.Program r n t → UniformReplayPrint.Program s n t
  | 0,.nil => .nil
  | _+1,.step p g => .step (mapProgram coeff p) (mapGate coeff id g)

def appendProgram {r n m t : ℕ} (p : UniformReplayPrint.Program r n t)
    (f : Fin (m+1) → Fin (n+1+t)) :
    {u : ℕ} → UniformReplayPrint.Program r m u → UniformReplayPrint.Program r n (t+u)
  | 0,.nil => p
  | _+1,.step q g => .step (appendProgram p f q) (mapGate id (appendIndex f) g)

def emitProgram {r n t : ℕ} (p : UniformReplayPrint.Program r n t) :
    {a : ℕ} → (Fin a → UniformReplayPrint.Gate r (n+1+t)) → UniformReplayPrint.Program r n (t+a)
  | 0,_ => p
  | a+1,g => .step (emitProgram p (g ∘ Fin.castSucc)) (mapGate id keepIndex (g (Fin.last a)))

/- Paper: Lemma 3.4, pp. 16–17: shared inputs, serial composition and three-branch addition preserve an explicit DAG. Reference relocation is implementation bookkeeping. -/
structure DAG (r n a : ℕ) where
  size : ℕ
  program : UniformReplayPrint.Program r n size
  outputs : Fin a → Fin (n+1+size)

def DAG.mapCoefficients {r s n a : ℕ} (f : Fin r → Fin s) (D : DAG r n a) : DAG s n a :=
  ⟨D.size,mapProgram f D.program,D.outputs⟩

def DAG.comp {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a) : DAG r n b :=
  ⟨E.size+D.size,appendProgram E.program (Fin.snoc E.outputs ⟨n,by omega⟩) D.program,
    appendIndex (Fin.snoc E.outputs ⟨n,by omega⟩) ∘ D.outputs⟩

/-- Reverse an actual input vector without emitting arithmetic gates. -/
def DAG.reverseInputs {r n a : ℕ} (D : DAG r n a) : DAG r n a :=
  let f : Fin (n+1) → Fin (n+1) := Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)
  ⟨0+D.size,appendProgram .nil f D.program,appendIndex f ∘ D.outputs⟩

def DAG.reverseOutputs {r n a : ℕ} (D : DAG r n a) : DAG r n a :=
  ⟨D.size,D.program,D.outputs ∘ Fin.rev⟩

/-- Three graphs share their original inputs; neither inputs nor scalars are copied. -/
def DAG.sumThree {r n a : ℕ} (A B D : DAG r n a) : DAG r n a :=
  let f₁ : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₁ := appendProgram A.program f₁ B.program
  let oa := fun i => keepIndex (l := B.size) (A.outputs i)
  let ob := fun i => appendIndex f₁ (B.outputs i)
  let f₂ : Fin (n+1) → Fin (n+1+(A.size+B.size)) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₂ := appendProgram p₁ f₂ D.program
  let oa₂ := fun i => keepIndex (l := D.size) (oa i)
  let ob₂ := fun i => keepIndex (l := D.size) (ob i)
  let od := fun i => appendIndex f₂ (D.outputs i)
  let p₃ := emitProgram p₂ (fun i : Fin a => .add (oa₂ i) (ob₂ i))
  let p₄ := emitProgram p₃ (fun i : Fin a => .add (gateIndex i) (keepIndex (od i)))
  ⟨((A.size+B.size)+D.size+a)+a,p₄,gateIndex⟩

/-- Longest-path evaluation of the actual typed data operands. Scalar-register
reuse is preparation, rather than a data edge in this evaluation. -/
def gateDepth {r w : ℕ} (d : Fin w → ℕ) : UniformReplayPrint.Gate r w → ℕ
  | .add a b => max (d a) (d b)+1
  | .sub a b => max (d a) (d b)+1
  | .scale _ a => d a+1

def runDepth {r n : ℕ} : {t : ℕ} → UniformReplayPrint.Program r n t →
    (Fin n → ℕ) → Fin (n+1+t) → ℕ
  | 0,.nil,x => Fin.snoc x 0
  | _+1,.step p g,x => Fin.snoc (runDepth p x) (gateDepth (runDepth p x) g)

theorem gateDepth_map {r s w w' : ℕ} (c : Fin r → Fin s) (f : Fin w → Fin w')
    (g : UniformReplayPrint.Gate r w) (d : Fin w' → ℕ) :
    gateDepth d (mapGate c f g) = gateDepth (d ∘ f) g := by cases g <;> rfl

theorem gateDepth_le {r w : ℕ} (g : UniformReplayPrint.Gate r w) (d e : Fin w → ℕ)
    (a : ℕ) (h : ∀ i, d i ≤ a+e i) : gateDepth d g ≤ a+gateDepth e g := by
  cases g with
  | add i j => simp only [gateDepth]; have := h i; have := h j; omega
  | sub i j => simp only [gateDepth]; have := h i; have := h j; omega
  | scale c i => simp only [gateDepth]; have := h i; omega

theorem runDepth_shift {r n t : ℕ} (p : UniformReplayPrint.Program r n t)
    (x y : Fin n → ℕ) (a : ℕ) (h : ∀ i, x i ≤ a+y i) :
    ∀ i, runDepth p x i ≤ a+runDepth p y i := by
  induction p with
  | nil =>
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [runDepth]
    · simpa only [runDepth,Fin.snoc_castSucc] using h j
  | @step t p g ih =>
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [runDepth,Fin.snoc_last]; exact gateDepth_le g _ _ a ih
    · simpa only [runDepth,Fin.snoc_castSucc] using ih j

theorem runDepth_zero {r n t : ℕ} (p : UniformReplayPrint.Program r n t) (x : Fin n → ℕ) :
    runDepth p x ⟨n,by omega⟩=0 := by
  induction p with
  | nil => exact Fin.snoc_last _ _
  | @step t p g ih =>
    change (Fin.snoc (runDepth p x) (gateDepth (runDepth p x) g) : Fin (n+1+t+1) → ℕ)
      (Fin.castSucc (⟨n,by omega⟩ : Fin (n+1+t)))=0
    rw [Fin.snoc_castSucc,ih]

theorem runDepth_input {r n t : ℕ} (p : UniformReplayPrint.Program r n t)
    (x : Fin n → ℕ) (j : Fin n) : runDepth p x ⟨j.val,by have := j.isLt; omega⟩=x j := by
  induction p with
  | nil => exact Fin.snoc_castSucc _ _ j
  | @step t p g ih =>
    change (Fin.snoc (runDepth p x) (gateDepth (runDepth p x) g) : Fin (n+1+t+1) → ℕ)
      (Fin.castSucc (⟨j.val,by have := j.isLt; omega⟩ : Fin (n+1+t)))=x j
    rw [Fin.snoc_castSucc,ih]

theorem runDepth_mapProgram {r s n t : ℕ} (f : Fin r → Fin s)
    (p : UniformReplayPrint.Program r n t) (x : Fin n → ℕ) :
    runDepth (mapProgram f p) x = runDepth p x := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapProgram,runDepth,ih,gateDepth_map,Function.comp_id]

theorem runDepth_append {r n m t u : ℕ} (p : UniformReplayPrint.Program r n t)
    (q : UniformReplayPrint.Program r m u) (f : Fin (m+1) → Fin (n+1+t))
    (x : Fin n → ℕ) (y : Fin m → ℕ)
    (hf : ∀ i, runDepth p x (f i)=(Fin.snoc y 0 : Fin (m+1) → ℕ) i) :
    (∀ i, runDepth (appendProgram p f q) x (keepIndex i)=runDepth p x i) ∧
    (∀ i, runDepth (appendProgram p f q) x (appendIndex f i)=runDepth q y i) := by
  induction q with
  | nil => exact ⟨fun _ => rfl,fun i => (appendIndex_zero f i) ▸ hf i⟩
  | @step u q g ih =>
    constructor
    · intro i; simpa only [appendProgram,runDepth,keepIndex_succ,Fin.snoc_castSucc] using ih.1 i
    · intro i; refine Fin.lastCases ?_ (fun j => ?_) i
      · change runDepth (appendProgram p f (q.step g)) x (appendIndex (l := u+1) f (Fin.last (m+1+u))) =
          runDepth (q.step g) y (Fin.last (m+1+u))
        rw [show appendIndex (l := u+1) f (Fin.last (m+1+u)) = Fin.last (n+1+(t+u)) from appendIndex_last f]
        simp only [appendProgram,runDepth,Nat.add_eq,Fin.snoc_last,gateDepth_map]
        congr 1
        funext j
        exact ih.2 j
      · simpa only [appendProgram,runDepth,appendIndex_castSucc,Fin.snoc_castSucc] using ih.2 j

theorem runDepth_emit {r n t a : ℕ} (p : UniformReplayPrint.Program r n t)
    (g : Fin a → UniformReplayPrint.Gate r (n+1+t)) (x : Fin n → ℕ) :
    (∀ i, runDepth (emitProgram p g) x (keepIndex i)=runDepth p x i) ∧
    (∀ i, runDepth (emitProgram p g) x (gateIndex i)=gateDepth (runDepth p x) (g i)) := by
  induction a with
  | zero => exact ⟨fun _ => rfl,fun i => Fin.elim0 i⟩
  | succ a ih =>
    have ih := ih (g ∘ Fin.castSucc)
    constructor
    · intro i; simpa only [emitProgram,runDepth,keepIndex_succ,Fin.snoc_castSucc] using ih.1 i
    · intro i; refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [gateIndex_last]
        simp only [emitProgram,runDepth,Nat.add_eq,Fin.snoc_last,gateDepth_map]
        congr 1
        funext j
        exact ih.1 j
      · simpa only [emitProgram,runDepth,gateIndex_castSucc,Fin.snoc_castSucc,Function.comp_apply] using ih.2 j

/-- Bound every register of the literal program, not only its selected outputs. -/
/- Paper: Equation (3.10), p. 16: bound every actual gate level, including intermediate composition registers. -/
def DepthBound {r n a : ℕ} (D : DAG r n a) (d : ℕ) : Prop :=
  ∀ i, runDepth D.program (fun _ => 0) i ≤ d

theorem appendDepthBound {r n m t u : ℕ} (p : UniformReplayPrint.Program r n t)
    (q : UniformReplayPrint.Program r m u) (f : Fin (m+1) → Fin (n+1+t))
    (x : Fin n → ℕ) (y : Fin m → ℕ) (K L : ℕ)
    (hf : ∀ i, runDepth p x (f i)=(Fin.snoc y 0 : Fin (m+1) → ℕ) i)
    (hp : ∀ i, runDepth p x i ≤ K) (hq : ∀ i, runDepth q y i ≤ L) :
    ∀ i, runDepth (appendProgram p f q) x i ≤ max K L := by
  have he := runDepth_append p q f x y hf
  intro i
  by_cases hi : i.val<n+1+t
  · let j : Fin (n+1+t) := ⟨i.val,hi⟩
    have hij : keepIndex (l := u) j=i := rfl
    rw [← hij,he.1]
    exact (hp j).trans (Nat.le_max_left _ _)
  · let j : Fin (m+1+u) := ⟨m+1+(i.val-(n+1+t)),by have := i.isLt; omega⟩
    have hij : appendIndex f j=i := by
      apply Fin.ext
      simp only [appendIndex,j]
      rw [dite_eq_right (by omega)]
      change n+1+t+(m+1+(i.val-(n+1+t))-(m+1))=i.val
      omega
    rw [← hij,he.2]
    exact (hq j).trans (Nat.le_max_right _ _)

theorem emitDepthBound {r n t a : ℕ} (p : UniformReplayPrint.Program r n t)
    (g : Fin a → UniformReplayPrint.Gate r (n+1+t)) (x : Fin n → ℕ) (K L : ℕ)
    (hp : ∀ i, runDepth p x i ≤ K) (hg : ∀ i, gateDepth (runDepth p x) (g i) ≤ L) :
    ∀ i, runDepth (emitProgram p g) x i ≤ max K L := by
  have he := runDepth_emit p g x
  intro i
  by_cases hi : i.val<n+1+t
  · let j : Fin (n+1+t) := ⟨i.val,hi⟩
    have hij : keepIndex (l := a) j=i := rfl
    rw [← hij,he.1]
    exact (hp j).trans (Nat.le_max_left _ _)
  · let j : Fin a := ⟨i.val-(n+1+t),by have := i.isLt; omega⟩
    have hij : gateIndex j=i := by apply Fin.ext; dsimp [gateIndex,j]; omega
    rw [← hij,he.2]
    exact (hg j).trans (Nat.le_max_right _ _)

theorem DAG.depth_mapCoefficients {r s n a : ℕ} (f : Fin r → Fin s) (D : DAG r n a) (K : ℕ)
    (h : DepthBound D K) : DepthBound (D.mapCoefficients f) K := by
  intro i
  change runDepth (mapProgram f D.program) (fun _ => 0) i ≤ K
  rw [runDepth_mapProgram]
  exact h i

theorem DAG.depth_reverseOutputs {r n a : ℕ} (D : DAG r n a) (K : ℕ)
    (h : DepthBound D K) : DepthBound D.reverseOutputs K := h

theorem DAG.depth_reverseInputs {r n a : ℕ} (D : DAG r n a) (K : ℕ)
    (h : DepthBound D K) : DepthBound D.reverseInputs K := by
  let f : Fin (n+1) → Fin (n+1) := Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)
  have hf : ∀ i, runDepth (UniformReplayPrint.Program.nil : UniformReplayPrint.Program r n 0)
      (fun _ => 0) (f i)=(Fin.snoc (fun _ : Fin n => 0) 0 : Fin (n+1) → ℕ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [runDepth,f]
  have hn : ∀ i, runDepth (UniformReplayPrint.Program.nil : UniformReplayPrint.Program r n 0)
      (fun _ => 0) i ≤ 0 := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [runDepth]
  simpa only [DepthBound,reverseInputs,Nat.zero_max] using
    appendDepthBound .nil D.program f (fun _ => 0) (fun _ => 0) 0 K hf hn h

theorem DAG.depth_comp {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a) (K L : ℕ)
    (hE : DepthBound E K) (hD : DepthBound D L) : DepthBound (D.comp E) (K+L) := by
  let y : Fin a → ℕ := fun i => runDepth E.program (fun _ => 0) (E.outputs i)
  let f : Fin (a+1) → Fin (n+1+E.size) := Fin.snoc E.outputs ⟨n,by omega⟩
  have hf : ∀ i, runDepth E.program (fun _ => 0) (f i)=(Fin.snoc y 0 : Fin (a+1) → ℕ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f,Fin.snoc_last] using runDepth_zero E.program (fun _ => 0)
    · simp only [f,Fin.snoc_castSucc,y]
  have hq : ∀ i, runDepth D.program y i ≤ K+L := by
    intro i
    have hs := runDepth_shift D.program y (fun _ => 0) K (fun j => by simpa only [y,Nat.add_zero] using hE (E.outputs j)) i
    exact hs.trans (Nat.add_le_add_left (hD i) K)
  intro i
  exact (appendDepthBound E.program D.program f (fun _ => 0) y K (K+L) hf hE hq i).trans (by omega)

theorem DAG.depth_sumThree {r n a : ℕ} (A B D : DAG r n a) (K : ℕ)
    (hA : DepthBound A K) (hB : DepthBound B K) (hD : DepthBound D K) :
    DepthBound (A.sumThree B D) (K+2) := by
  let f₁ : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₁ := appendProgram A.program f₁ B.program
  have h₁ : ∀ i, runDepth A.program (fun _ => 0) (f₁ i)=
      (Fin.snoc (fun _ : Fin n => 0) 0 : Fin (n+1) → ℕ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f₁,Fin.val_last,Fin.snoc_last] using runDepth_zero A.program (fun _ => 0)
    · simpa only [f₁,Fin.val_castSucc,Fin.snoc_castSucc] using runDepth_input A.program (fun _ => 0) j
  have hp₁ : ∀ i, runDepth p₁ (fun _ => 0) i ≤ K := by
    simpa only [Nat.max_self] using appendDepthBound A.program B.program f₁ (fun _ => 0) (fun _ => 0) K K h₁ hA hB
  let f₂ : Fin (n+1) → Fin (n+1+(A.size+B.size)) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₂ := appendProgram p₁ f₂ D.program
  have h₂ : ∀ i, runDepth p₁ (fun _ => 0) (f₂ i)=
      (Fin.snoc (fun _ : Fin n => 0) 0 : Fin (n+1) → ℕ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f₂,Fin.val_last,Fin.snoc_last] using runDepth_zero p₁ (fun _ => 0)
    · simpa only [f₂,Fin.val_castSucc,Fin.snoc_castSucc] using runDepth_input p₁ (fun _ => 0) j
  have hp₂ : ∀ i, runDepth p₂ (fun _ => 0) i ≤ K := by
    simpa only [Nat.max_self] using appendDepthBound p₁ D.program f₂ (fun _ => 0) (fun _ => 0) K K h₂ hp₁ hD
  let ga : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size)) := fun i => .add
    (keepIndex (l := D.size) (keepIndex (l := B.size) (A.outputs i)))
    (keepIndex (l := D.size) (appendIndex f₁ (B.outputs i)))
  let p₃ := emitProgram p₂ ga
  have hp₃ : ∀ i, runDepth p₃ (fun _ => 0) i ≤ K+1 := by
    intro i
    have hg : ∀ j, gateDepth (runDepth p₂ (fun _ => 0)) (ga j) ≤ K+1 := by
      intro j; simp only [ga,gateDepth]; have := hp₂ (keepIndex (keepIndex (A.outputs j)))
      have := hp₂ (keepIndex (appendIndex f₁ (B.outputs j))); omega
    exact (emitDepthBound p₂ ga (fun _ => 0) K (K+1) hp₂ hg i).trans (by omega)
  let gb : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size+a)) := fun i => .add
    (gateIndex i) (keepIndex (appendIndex f₂ (D.outputs i)))
  intro i
  have hg : ∀ j, gateDepth (runDepth p₃ (fun _ => 0)) (gb j) ≤ K+2 := by
    intro j; simp only [gb,gateDepth]; have := hp₃ (gateIndex j)
    have := hp₃ (keepIndex (appendIndex f₂ (D.outputs j))); omega
  exact (emitDepthBound p₃ gb (fun _ => 0) (K+1) (K+2) hp₃ hg i).trans (by omega)

noncomputable section

theorem mapCoefficient_eval {r s : ℕ} (f : Fin r → Fin s) (bank : Fin s → ℂ)
    (c : Coefficient r) : (mapCoefficient f c).eval bank = c.eval (bank ∘ f) := by
  cases c <;> rfl

theorem mapGate_eval {r s w w' : ℕ} (coeff : Fin r → Fin s) (refs : Fin w → Fin w')
    (bank : Fin s → ℂ) (g : UniformReplayPrint.Gate r w) :
    (mapGate coeff refs g).eval bank = (g.eval (bank ∘ coeff)).map refs := by
  cases g <;> simp [mapGate,UniformReplayPrint.Gate.eval,mapCoefficient_eval,OAI.ExactFourier.Gate.map]

theorem mapProgram_eval {r s n t : ℕ} (coeff : Fin r → Fin s) (bank : Fin s → ℂ)
    (p : UniformReplayPrint.Program r n t) :
    (mapProgram coeff p).eval bank = p.eval (bank ∘ coeff) := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [mapProgram,UniformReplayPrint.Program.eval,ih,mapGate_eval]
    congr 1
    cases g <;> rfl

theorem appendProgram_eval {r n m t u : ℕ} (bank : Fin r → ℂ)
    (p : UniformReplayPrint.Program r n t) (f : Fin (m+1) → Fin (n+1+t))
    (q : UniformReplayPrint.Program r m u) :
    (appendProgram p f q).eval bank = (p.eval bank).append f (q.eval bank) := by
  induction q with
  | nil => rfl
  | step q g ih =>
    simp only [appendProgram,UniformReplayPrint.Program.eval,OAI.ExactFourier.Program.append,ih,mapGate_eval]
    rfl

theorem emitProgram_eval {r n t a : ℕ} (bank : Fin r → ℂ)
    (p : UniformReplayPrint.Program r n t) (g : Fin a → UniformReplayPrint.Gate r (n+1+t)) :
    (emitProgram p g).eval bank = (p.eval bank).emit (fun i => (g i).eval bank) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [emitProgram,UniformReplayPrint.Program.eval,OAI.ExactFourier.Program.emit,mapGate_eval]
    rw [ih]
    rfl

def DAG.eval {r n a : ℕ} (D : DAG r n a) (bank : Fin r → ℂ) (x : Fin n → ℂ) : Fin a → ℂ :=
  fun i => (D.program.eval bank).eval x (D.outputs i)

def DAG.toLinear {r n a : ℕ} (D : DAG r n a) (bank : Fin r → ℂ) : LinearDAG n a :=
  ⟨D.size,D.program.eval bank,D.outputs⟩

theorem DAG.eval_comp {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a)
    (bank : Fin r → ℂ) (x : Fin n → ℂ) :
    (D.comp E).eval bank x = D.eval bank (E.eval bank x) := by
  have hp : (D.comp E).toLinear bank = (D.toLinear bank).comp (E.toLinear bank) := by
    simp only [comp,toLinear,LinearDAG.comp,appendProgram_eval]
  exact (congrArg (fun P : LinearDAG n b => P.eval x) hp).trans
    (LinearDAG.eval_comp _ _ x)

theorem DAG.eval_mapCoefficients {r s n a : ℕ} (f : Fin r → Fin s) (D : DAG r n a)
    (bank : Fin s → ℂ) (x : Fin n → ℂ) :
    (D.mapCoefficients f).eval bank x = D.eval (bank ∘ f) x := by
  funext i
  change ((mapProgram f D.program).eval bank).eval x (D.outputs i) = _
  rw [mapProgram_eval]
  rfl

theorem DAG.eval_reverseOutputs {r n a : ℕ} (D : DAG r n a) (bank : Fin r → ℂ) (x : Fin n → ℂ) :
    D.reverseOutputs.eval bank x = D.eval bank x ∘ Fin.rev := rfl

theorem DAG.eval_reverseInputs {r n a : ℕ} (D : DAG r n a) (bank : Fin r → ℂ) (x : Fin n → ℂ) :
    D.reverseInputs.eval bank x = D.eval bank (x ∘ Fin.rev) := by
  let f : Fin (n+1) → Fin (n+1) := Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)
  have hf : ∀ i : Fin (n+1), (OAI.ExactFourier.Program.nil : OAI.ExactFourier.Program n 0).eval x (f i) =
      (Fin.snoc (x ∘ Fin.rev) 0 : Fin (n+1) → ℂ) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [f,OAI.ExactFourier.Program.eval]
    · simp [f,OAI.ExactFourier.Program.eval,Function.comp_def]
  funext i
  simp only [reverseInputs,DAG.eval,appendProgram_eval]
  exact ((OAI.ExactFourier.Program.nil : OAI.ExactFourier.Program n 0).eval_append
    (D.program.eval bank) f x (x ∘ Fin.rev) hf).2 (D.outputs i)
    |>.trans (by rfl)

theorem DAG.eval_sumThree {r n a : ℕ} (A B D : DAG r n a) (bank : Fin r → ℂ) (x : Fin n → ℂ) :
    (A.sumThree B D).eval bank x = fun i => A.eval bank x i+B.eval bank x i+D.eval bank x i := by
  let f₁ : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₁ := appendProgram A.program f₁ B.program
  have h₁ : ∀ i : Fin (n+1), (A.program.eval bank).eval x (f₁ i) =
      (Fin.snoc x 0 : Fin (n+1) → ℂ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f₁,Fin.val_last,Fin.snoc_last] using (A.program.eval bank).eval_zero x
    · simpa only [f₁,Fin.val_castSucc,Fin.snoc_castSucc] using (A.program.eval bank).eval_input x j
  have e₁ := (A.program.eval bank).eval_append (B.program.eval bank) f₁ x x h₁
  let f₂ : Fin (n+1) → Fin (n+1+(A.size+B.size)) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  have h₂ : ∀ i : Fin (n+1), (p₁.eval bank).eval x (f₂ i) =
      (Fin.snoc x 0 : Fin (n+1) → ℂ) i := by
    intro i; refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f₂,Fin.val_last,Fin.snoc_last] using (p₁.eval bank).eval_zero x
    · simpa only [f₂,Fin.val_castSucc,Fin.snoc_castSucc] using (p₁.eval bank).eval_input x j
  have e₂ := (p₁.eval bank).eval_append (D.program.eval bank) f₂ x x h₂
  let p₂ := appendProgram p₁ f₂ D.program
  let ga : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size)) := fun i => .add
    (keepIndex (l := D.size) (keepIndex (l := B.size) (A.outputs i)))
    (keepIndex (l := D.size) (appendIndex f₁ (B.outputs i)))
  let p₃ := emitProgram p₂ ga
  let gb : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size+a)) := fun i => .add (gateIndex i)
    (keepIndex (appendIndex f₂ (D.outputs i)))
  have e₃ := (p₂.eval bank).eval_emit (fun i => (ga i).eval bank) x
  have e₄ := (p₃.eval bank).eval_emit (fun i => (gb i).eval bank) x
  funext i
  change ((emitProgram p₃ gb).eval bank).eval x (gateIndex i) = _
  rw [emitProgram_eval]
  rw [e₄.2]
  simp only [gb,UniformReplayPrint.Gate.eval,OAI.ExactFourier.Gate.eval]
  rw [show (p₃.eval bank).eval x (gateIndex i) =
    ((ga i).eval bank).eval ((p₂.eval bank).eval x) by rw [show p₃.eval bank = (p₂.eval bank).emit
      (fun i => (ga i).eval bank) from emitProgram_eval bank p₂ ga]; exact e₃.2 i]
  rw [show (p₃.eval bank).eval x (keepIndex (appendIndex f₂ (D.outputs i))) =
    (p₂.eval bank).eval x (appendIndex f₂ (D.outputs i)) by rw [show p₃.eval bank = (p₂.eval bank).emit
      (fun i => (ga i).eval bank) from emitProgram_eval bank p₂ ga]; exact e₃.1 _]
  simp only [ga,UniformReplayPrint.Gate.eval,OAI.ExactFourier.Gate.eval]
  rw [show p₂.eval bank = (p₁.eval bank).append f₂ (D.program.eval bank) from appendProgram_eval bank p₁ f₂ D.program]
  rw [e₂.1,e₂.1,e₂.2]
  rw [show p₁.eval bank = (A.program.eval bank).append f₁ (B.program.eval bank) from appendProgram_eval bank A.program f₁ B.program]
  rw [e₁.1,e₁.2]
  rfl

end

@[reducible] def bankSize (k : ℕ) : ℕ := width k+6*width k

def coefficientEmbedding (k : ℕ) (b : Fin 6) : Fin (width k+width k) → Fin (bankSize k) :=
  Fin.addCases (fun i => i.castAdd (6*width k))
    (fun i => (finProdFinEquiv (b,i)).natAdd (width k))

/-- One canonical power bank is shared by all six convolution blocks. -/
def convolutionDAG (k n m : ℕ) (hm : m ≤ width k) : DAG (width k+width k) n m :=
  ⟨UniformConvolutionDAG.total k,UniformConvolutionDAG.paddedProgram k n,
    fun i => UniformConvolutionDAG.outputIndex k n ⟨i.val,i.isLt.trans_le hm⟩⟩

def firstSlot (b : Fin 3) : Fin 6 := ⟨2*b.val,by have := b.isLt; omega⟩
def secondSlot (b : Fin 3) : Fin 6 := ⟨2*b.val+1,by have := b.isLt; omega⟩

def kernelDAG (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) (b : Fin 3) :
    DAG (bankSize k) e a :=
  ((convolutionDAG k e a ha).mapCoefficients (coefficientEmbedding k (secondSlot b))).comp
    (((convolutionDAG k e e he).reverseInputs.reverseOutputs).mapCoefficients
      (coefficientEmbedding k (firstSlot b)))

/-- The topology is selected solely by integer sizes; all three branches are
printed even when prepared coefficients happen to vanish. -/
def crossDAG (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) : DAG (bankSize k) e a :=
  (kernelDAG k a e ha he 0).sumThree (kernelDAG k a e ha he 1) (kernelDAG k a e ha he 2)

theorem crossDAG_size (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) :
    (crossDAG k a e ha he).size = 6*(3*k*2^k+2*2^k)+2*a := by
  have hc : UniformConvolutionDAG.total k=3*k*2^k+2*2^k :=
    (UniformConvolutionDAG.records_length k).symm.trans (UniformConvolutionDAG.gate_count k)
  simp only [crossDAG,kernelDAG,convolutionDAG,DAG.comp,DAG.sumThree,DAG.mapCoefficients,
    DAG.reverseInputs,DAG.reverseOutputs,Nat.zero_add,hc]
  omega

def convolutionNatDepth (k a : ℕ) : ℕ :=
  if a < width k then 0 else
    if h : a-width k < UniformConvolutionDAG.total k then
      UniformConvolutionDAG.depth (.inr ((UniformConvolutionDAG.nodeFin k).symm ⟨a-width k,h⟩))
    else 0

theorem convolutionNatDepth_ref (k : ℕ) (r : UniformConvolutionDAG.Ref k) :
    convolutionNatDepth k (UniformConvolutionDAG.address r)=UniformConvolutionDAG.depth r := by
  cases r with
  | inl i => simp [convolutionNatDepth,UniformConvolutionDAG.address,i.isLt,UniformConvolutionDAG.depth]
  | inr j => simp [convolutionNatDepth,UniformConvolutionDAG.address,(UniformConvolutionDAG.nodeFin k j).isLt]

theorem convolutionPrintedDepth (k : ℕ) (j : Fin (UniformConvolutionDAG.total k)) :
    (UniformConvolutionDAG.instruction k j).depth (convolutionNatDepth k) =
      convolutionNatDepth k (width k+j.val) := by
  rw [UniformConvolutionDAG.instruction,UniformConvolutionDAG.Expr.depth_map]
  have h : (convolutionNatDepth k ∘ UniformConvolutionDAG.address) = @UniformConvolutionDAG.depth k := by
    funext r; exact convolutionNatDepth_ref k r
  rw [h,← UniformConvolutionDAG.depth_gate]
  simpa only [UniformConvolutionDAG.address,Equiv.apply_symm_apply] using (convolutionNatDepth_ref k (.inr ((UniformConvolutionDAG.nodeFin k).symm j))).symm

theorem lower_gateDepth {r n : ℕ} (g : UniformConvolutionDAG.Expr r ℕ)
    (h : ∀ a ∈ g.refs, a<n) (d : Fin n → ℕ) :
    gateDepth d (g.lower h) = g.depth (fun a => if ha : a<n then d ⟨a,ha⟩ else 0) := by
  cases g with
  | add a b =>
    have ha := h a (by simp [UniformConvolutionDAG.Expr.refs])
    have hb := h b (by simp [UniformConvolutionDAG.Expr.refs])
    simp [UniformConvolutionDAG.Expr.lower,gateDepth,UniformConvolutionDAG.Expr.depth,ha,hb]
  | sub a b =>
    have ha := h a (by simp [UniformConvolutionDAG.Expr.refs])
    have hb := h b (by simp [UniformConvolutionDAG.Expr.refs])
    simp [UniformConvolutionDAG.Expr.lower,gateDepth,UniformConvolutionDAG.Expr.depth,ha,hb]
  | scale c a =>
    have ha := h a (by simp [UniformConvolutionDAG.Expr.refs])
    simp [UniformConvolutionDAG.Expr.lower,gateDepth,UniformConvolutionDAG.Expr.depth,ha]

theorem exprDepth_congr {r : ℕ} {α : Type} (g : UniformConvolutionDAG.Expr r α) (d e : α → ℕ)
    (h : ∀ a ∈ g.refs, d a=e a) : g.depth d=g.depth e := by
  cases g with
  | add a b => exact congrArg₂ (fun a b => max a b+1) (h a (by simp [UniformConvolutionDAG.Expr.refs])) (h b (by simp [UniformConvolutionDAG.Expr.refs]))
  | sub a b => exact congrArg₂ (fun a b => max a b+1) (h a (by simp [UniformConvolutionDAG.Expr.refs])) (h b (by simp [UniformConvolutionDAG.Expr.refs]))
  | scale c a => exact congrArg (·+1) (h a (by simp [UniformConvolutionDAG.Expr.refs]))

theorem convolutionPrefixDepth (k n t : ℕ) (f : Fin (width k) → Fin (n+1))
    (ht : t ≤ UniformConvolutionDAG.total k) (a : ℕ) (ha : a < width k+t) :
    runDepth (UniformConvolutionDAG.programPrefix k n f t ht) (fun _ => 0)
      (UniformConvolutionDAG.typedIndex n t f a ha)=convolutionNatDepth k a := by
  induction t generalizing a with
  | zero =>
    have hb : a < width k := by omega
    rw [UniformConvolutionDAG.typedIndex_initial n f ⟨a,hb⟩]
    simp only [UniformConvolutionDAG.programPrefix,runDepth,convolutionNatDepth,hb,ite_true]
    have hzero : (Fin.snoc (fun _ : Fin n => (0 : ℕ)) 0 : Fin (n+1) → ℕ)=fun _ => 0 := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hzero]
  | succ t ih =>
    let j : Fin (UniformConvolutionDAG.total k) := ⟨t,by omega⟩
    have hg : gateDepth (runDepth (UniformConvolutionDAG.programPrefix k n f t (by omega)) (fun _ => 0))
        (UniformConvolutionDAG.loweredGate k n f j) = convolutionNatDepth k (width k+t) := by
      rw [UniformConvolutionDAG.loweredGate,lower_gateDepth,UniformConvolutionDAG.Expr.depth_map]
      rw [← convolutionPrintedDepth k j]
      apply exprDepth_congr
      intro b hb
      have hp := UniformConvolutionDAG.printed_refs_before k j b hb
      have hw := UniformConvolutionDAG.wireAddress_lt n t f b hp
      simp only [Function.comp_apply,dite_eq_left hw]
      exact ih (by omega) b hp
    by_cases heq : a=width k+t
    · subst a
      rw [UniformConvolutionDAG.typedIndex_last]
      simp only [UniformConvolutionDAG.programPrefix,runDepth,Nat.add_eq,Fin.snoc_last]
      exact hg
    · have hb : a < width k+t := by omega
      rw [UniformConvolutionDAG.typedIndex_castSucc n t f a hb]
      simp only [UniformConvolutionDAG.programPrefix,runDepth,Fin.snoc_castSucc]
      exact ih (by omega) a hb

theorem convolutionDAG_depth (k n m : ℕ) (hm : m ≤ width k) :
    DepthBound (convolutionDAG k n m hm) (4*k+2) := by
  intro i
  by_cases hi : i.val<n+1
  · by_cases hn : i.val=n
    · have he : i=⟨n,by omega⟩ := Fin.ext hn
      rw [he,runDepth_zero]
      omega
    · have hin : i.val<n := by omega
      have he : i=⟨(⟨i.val,hin⟩ : Fin n).val,by omega⟩ := rfl
      rw [he,runDepth_input]
      omega
  · let a := width k+(i.val-(n+1))
    have ha : a < width k+UniformConvolutionDAG.total k := by
      have hiBound : i.val<n+1+UniformConvolutionDAG.total k := i.isLt
      dsimp [a]; omega
    have he : UniformConvolutionDAG.typedIndex n (UniformConvolutionDAG.total k)
        (UniformConvolutionDAG.padInputs k n) a ha=i := by
      apply Fin.ext
      simp only [UniformConvolutionDAG.typedIndex,UniformConvolutionDAG.wireAddress,a]
      rw [dite_eq_right (by omega)]
      omega
    change runDepth (UniformConvolutionDAG.programPrefix k n (UniformConvolutionDAG.padInputs k n)
      (UniformConvolutionDAG.total k) (le_refl _)) (fun _ => 0) i ≤ _
    rw [← he,convolutionPrefixDepth]
    unfold convolutionNatDepth
    split_ifs with hn ht
    · omega
    · exact UniformConvolutionDAG.depth_bound _
    · omega

theorem kernelDAG_depth (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) (b : Fin 3) :
    DepthBound (kernelDAG k a e ha he b) (8*k+4) := by
  have hv := DAG.depth_mapCoefficients (coefficientEmbedding k (secondSlot b))
    (convolutionDAG k e a ha) (4*k+2) (convolutionDAG_depth k e a ha)
  have hw := DAG.depth_mapCoefficients (coefficientEmbedding k (firstSlot b))
    (convolutionDAG k e e he).reverseInputs.reverseOutputs (4*k+2)
    (DAG.depth_reverseOutputs _ _ (DAG.depth_reverseInputs _ _ (convolutionDAG_depth k e e he)))
  simpa only [kernelDAG,show (4*k+2)+(4*k+2)=8*k+4 by omega] using DAG.depth_comp _ _ (4*k+2) (4*k+2) hw hv

/-- Every register of the actual printed rank-three graph has depth at most
8k+6, including both final sum layers. -/
theorem crossDAG_depth (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) :
    DepthBound (crossDAG k a e ha he) (8*k+6) := by
  exact DAG.depth_sumThree _ _ _ (8*k+4) (kernelDAG_depth k a e ha he 0)
    (kernelDAG_depth k a e ha he 1) (kernelDAG_depth k a e ha he 2)

/-- Actual dirty replay of the same printed graph and its selected outputs. -/
def crossReplay (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) :=
  UniformReplayPrint.replayCode (crossDAG k a e ha he).program (crossDAG k a e ha he).outputs

/-- Plain integer operand records of the actual typed program. -/
def gateRecord {r w : ℕ} : UniformReplayPrint.Gate r w → UniformConvolutionDAG.Expr r ℕ
  | .add a b => .add a.val b.val
  | .sub a b => .sub a.val b.val
  | .scale c a => .scale c a.val

def programRecords {r n : ℕ} : {t : ℕ} → UniformReplayPrint.Program r n t →
    List (UniformConvolutionDAG.Expr r ℕ)
  | 0,.nil => []
  | _+1,.step p g => programRecords p ++ [gateRecord g]

theorem programRecords_length {r n t : ℕ} (p : UniformReplayPrint.Program r n t) :
    (programRecords p).length=t := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [programRecords,List.length_append,List.length_singleton,ih]

def physicalUseCount {r n a : ℕ} (D : DAG r n a) (port : ℕ) : ℕ :=
  if port=n then 0 else
    ((programRecords D.program).flatMap UniformConvolutionDAG.Expr.refs).count port+
      ((List.finRange a).map (fun i => (D.outputs i).val)).count port

def allRefs {r n t : ℕ} (p : UniformReplayPrint.Program r n t) : List ℕ :=
  (programRecords p).flatMap UniformConvolutionDAG.Expr.refs

def outputRefs {r n a : ℕ} (D : DAG r n a) : List ℕ :=
  (List.finRange a).map (fun i => (D.outputs i).val)

def appendWire {n m t : ℕ} (f : Fin (m+1) → Fin (n+1+t)) (a : ℕ) : ℕ :=
  if h : a < m+1 then (f ⟨a,h⟩).val else n+1+t+(a-(m+1))

theorem gateRecord_refs_bound {r w : ℕ} (g : UniformReplayPrint.Gate r w)
    (a : ℕ) (ha : a ∈ (gateRecord g).refs) : a < w := by
  cases g with
  | add i j =>
    simp only [gateRecord,UniformConvolutionDAG.Expr.refs,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> exact Fin.isLt _
  | sub i j =>
    simp only [gateRecord,UniformConvolutionDAG.Expr.refs,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> exact Fin.isLt _
  | scale c i =>
    simp only [gateRecord,UniformConvolutionDAG.Expr.refs,List.mem_singleton] at ha
    subst a; exact i.isLt

theorem allRefs_bound {r n t : ℕ} (p : UniformReplayPrint.Program r n t) (a : ℕ)
    (ha : a ∈ allRefs p) : a < n+1+t := by
  induction p with
  | nil => simp [allRefs,programRecords] at ha
  | @step t p g ih =>
    simp only [allRefs,programRecords,List.flatMap_append,List.flatMap_singleton,List.mem_append] at ha
    rcases ha with ha|ha
    · exact (ih ha).trans_le (by omega)
    · exact (gateRecord_refs_bound g a ha).trans_le (by omega)

theorem gateRecord_lower {r w : ℕ} (g : UniformConvolutionDAG.Expr r ℕ)
    (h : ∀ a ∈ g.refs, a < w) : gateRecord (g.lower h)=g := by cases g <;> rfl

theorem appendIndex_val {n m t u : ℕ} (f : Fin (m+1) → Fin (n+1+t))
    (i : Fin (m+1+u)) : (appendIndex f i).val=appendWire f i.val := by
  unfold appendIndex appendWire
  split_ifs <;> rfl

theorem gateRecord_append {r n m t u : ℕ} (f : Fin (m+1) → Fin (n+1+t))
    (g : UniformReplayPrint.Gate r (m+1+u)) :
    gateRecord (mapGate id (appendIndex f) g)=(gateRecord g).map (appendWire f) := by
  cases g with
  | add a b => simp only [mapGate,gateRecord,UniformConvolutionDAG.Expr.map,appendIndex_val]
  | sub a b => simp only [mapGate,gateRecord,UniformConvolutionDAG.Expr.map,appendIndex_val]
  | scale c a => cases c <;> simp only [mapGate,gateRecord,UniformConvolutionDAG.Expr.map,mapCoefficient,id_eq,appendIndex_val]

theorem appendProgram_records {r n m t u : ℕ} (p : UniformReplayPrint.Program r n t)
    (f : Fin (m+1) → Fin (n+1+t)) (q : UniformReplayPrint.Program r m u) :
    programRecords (appendProgram p f q)=programRecords p ++
      (programRecords q).map (fun g => g.map (appendWire f)) := by
  induction q with
  | nil => simp [appendProgram,programRecords]
  | step q g ih => simp only [appendProgram,programRecords,ih,List.map_append,List.map_singleton,
      gateRecord_append,List.append_assoc]

theorem allRefs_append {r n m t u : ℕ} (p : UniformReplayPrint.Program r n t)
    (f : Fin (m+1) → Fin (n+1+t)) (q : UniformReplayPrint.Program r m u) :
    allRefs (appendProgram p f q)=allRefs p ++(allRefs q).map (appendWire f) := by
  simp only [allRefs,appendProgram_records,List.flatMap_append,List.flatMap_map,
    UniformConvolutionDAG.Expr.refs_map,List.map_flatMap]

theorem gateRecord_keep {r n t u : ℕ} (g : UniformReplayPrint.Gate r (n+1+t)) :
    gateRecord (mapGate id (keepIndex (l := u)) g)=gateRecord g := by
  cases g with
  | add a b => rfl
  | sub a b => rfl
  | scale c a => cases c <;> rfl

theorem emitProgram_records {r n t a : ℕ} (p : UniformReplayPrint.Program r n t)
    (g : Fin a → UniformReplayPrint.Gate r (n+1+t)) :
    programRecords (emitProgram p g)=programRecords p ++List.ofFn (fun i => gateRecord (g i)) := by
  induction a with
  | zero => simp [emitProgram]
  | succ a ih =>
    rw [emitProgram,programRecords,ih,List.ofFn_succ',List.concat_eq_append,List.append_assoc]
    rw [gateRecord_keep]
    rfl

theorem convolutionPrefix_records (k n t : ℕ) (f : Fin (width k) → Fin (n+1))
    (ht : t ≤ UniformConvolutionDAG.total k) :
    programRecords (UniformConvolutionDAG.programPrefix k n f t ht)=
      List.ofFn (fun j : Fin t => (UniformConvolutionDAG.instruction k
        ⟨j.val,j.isLt.trans_le ht⟩).map (UniformConvolutionDAG.wireAddress n f)) := by
  induction t with
  | zero => simp [UniformConvolutionDAG.programPrefix,programRecords]
  | succ t ih =>
    rw [UniformConvolutionDAG.programPrefix,programRecords,ih,List.ofFn_succ',List.concat_eq_append]
    congr 1
    simp only [List.singleton_inj,UniformConvolutionDAG.loweredGate,gateRecord_lower]
    rfl

theorem allRefs_convolution (k n : ℕ) :
    allRefs (UniformConvolutionDAG.paddedProgram k n)=
      ((UniformConvolutionDAG.records k).flatMap UniformConvolutionDAG.Expr.refs).map
        (UniformConvolutionDAG.wireAddress n (UniformConvolutionDAG.padInputs k n)) := by
  simp only [allRefs,UniformConvolutionDAG.paddedProgram,UniformConvolutionDAG.program,
    convolutionPrefix_records,List.ofFn_eq_map,List.flatMap_map,UniformConvolutionDAG.Expr.refs_map,
    UniformConvolutionDAG.records,List.map_flatMap]

noncomputable section

theorem count_map_unique (l : List ℕ) (f : ℕ → ℕ) (b c : ℕ)
    (h : ∀ a ∈ l, f a=b ↔ a=c) : (l.map f).count b=l.count c := by
  simp only [List.count_eq_countP,List.countP_map]
  apply List.countP_congr
  intro a ha
  simpa only [Function.comp_apply,beq_iff_eq] using h a ha

theorem count_map_zero (l : List ℕ) (f : ℕ → ℕ) (b : ℕ)
    (h : ∀ a ∈ l, f a≠b) : (l.map f).count b=0 := by
  apply List.count_eq_zero_of_not_mem
  intro hm
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
  exact h a ha he

theorem convolution_address_injective (k : ℕ) :
    Function.Injective (@UniformConvolutionDAG.address k) := by
  intro a b h
  cases a with
  | inl i => cases b with
    | inl j => exact congrArg Sum.inl (Fin.ext h)
    | inr j => have := i.isLt; change i.val=width k+(UniformConvolutionDAG.nodeFin k j).val at h; omega
  | inr i => cases b with
    | inl j => have := j.isLt; change width k+(UniformConvolutionDAG.nodeFin k i).val=j.val at h; omega
    | inr j =>
      apply congrArg Sum.inr
      apply (UniformConvolutionDAG.nodeFin k).injective
      apply Fin.ext
      change width k+(UniformConvolutionDAG.nodeFin k i).val=width k+(UniformConvolutionDAG.nodeFin k j).val at h
      omega

theorem convolution_logical_count (k : ℕ) (r : UniformConvolutionDAG.Ref k) :
    ((UniformConvolutionDAG.records k).flatMap UniformConvolutionDAG.Expr.refs).count
      (UniformConvolutionDAG.address r) = (UniformConvolutionDAG.successors r).length := by
  classical
  simp only [UniformConvolutionDAG.records,List.count_flatMap,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  have hj : ∀ j : Fin (UniformConvolutionDAG.total k),
      ((UniformConvolutionDAG.instruction k j).refs).count (UniformConvolutionDAG.address r)=
      if (UniformConvolutionDAG.nodeFin k).symm j ∈ UniformConvolutionDAG.successors r then 1 else 0 := by
    intro j
    rw [UniformConvolutionDAG.instruction,UniformConvolutionDAG.Expr.refs_map]
    rw [((UniformConvolutionDAG.gate_refs_nodup _).map (convolution_address_injective k)).count]
    have hm : UniformConvolutionDAG.address r ∈
        ((UniformConvolutionDAG.gate ((UniformConvolutionDAG.nodeFin k).symm j)).refs).map UniformConvolutionDAG.address ↔
        r ∈ (UniformConvolutionDAG.gate ((UniformConvolutionDAG.nodeFin k).symm j)).refs := by
      simp only [List.mem_map]
      constructor
      · rintro ⟨s,hs,he⟩; exact (convolution_address_injective k he) ▸ hs
      · intro hs; exact ⟨r,hs,rfl⟩
    simp only [hm,← UniformConvolutionDAG.successors_spec]
  simp_rw [hj]
  rw [Finset.sum_boole]
  have hs : (Finset.univ.filter (fun j : Fin (UniformConvolutionDAG.total k) =>
      (UniformConvolutionDAG.nodeFin k).symm j ∈ UniformConvolutionDAG.successors r)) =
      (UniformConvolutionDAG.successors r).toFinset.map (UniformConvolutionDAG.nodeFin k).toEmbedding := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,List.mem_toFinset]
    constructor
    · intro h
      exact ⟨(UniformConvolutionDAG.nodeFin k).symm j,h,Equiv.apply_symm_apply _ _⟩
    · rintro ⟨i,hi,he⟩
      subst j
      simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hi
  rw [hs,Finset.card_map,List.toFinset_card_of_nodup (UniformConvolutionDAG.successors_nodup r)]
  simp

theorem convolution_allRefs_bound (k : ℕ) (a : ℕ)
    (ha : a ∈ (UniformConvolutionDAG.records k).flatMap UniformConvolutionDAG.Expr.refs) :
    a < width k+UniformConvolutionDAG.total k := by
  obtain ⟨g,hg,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
  exact (UniformConvolutionDAG.printed_refs_before k j a ha).trans_le (by have := j.isLt; omega)

theorem convolution_input_uses (k n : ℕ) (hn : n ≤ width k) (i : Fin n) :
    (allRefs (UniformConvolutionDAG.paddedProgram k n)).count i.val =
      (UniformConvolutionDAG.successors (.inl ⟨i.val,i.isLt.trans_le hn⟩)).length := by
  rw [allRefs_convolution]
  have hu : ∀ a ∈ (UniformConvolutionDAG.records k).flatMap UniformConvolutionDAG.Expr.refs,
      UniformConvolutionDAG.wireAddress n (UniformConvolutionDAG.padInputs k n) a=i.val ↔ a=i.val := by
    intro a _
    unfold UniformConvolutionDAG.wireAddress UniformConvolutionDAG.padInputs
    split_ifs with ha hb
    · rfl
    · have := i.isLt; change ¬a < n at hb; change n=i.val ↔ a=i.val; omega
    · have := i.isLt; omega
  rw [count_map_unique _ _ _ _ hu]
  exact convolution_logical_count k (.inl ⟨i.val,i.isLt.trans_le hn⟩)

theorem convolution_node_uses (k n : ℕ) (j : UniformConvolutionDAG.Node k) :
    (allRefs (UniformConvolutionDAG.paddedProgram k n)).count
      (n+1+(UniformConvolutionDAG.nodeFin k j).val) = (UniformConvolutionDAG.successors (.inr j)).length := by
  rw [allRefs_convolution]
  have hu : ∀ a ∈ (UniformConvolutionDAG.records k).flatMap UniformConvolutionDAG.Expr.refs,
      UniformConvolutionDAG.wireAddress n (UniformConvolutionDAG.padInputs k n) a=
        n+1+(UniformConvolutionDAG.nodeFin k j).val ↔ a=width k+(UniformConvolutionDAG.nodeFin k j).val := by
    intro a _
    unfold UniformConvolutionDAG.wireAddress
    split_ifs with ha
    · have := (UniformConvolutionDAG.padInputs k n ⟨a,ha⟩).isLt; have := ha; omega
    · omega
  rw [count_map_unique _ _ _ _ hu]
  exact convolution_logical_count k (.inr j)

/-- Actual original-input and generated-port multiplicities. The distinguished
literal-zero slot is outside these two physical port classes. -/
def InputBound {r n a : ℕ} (D : DAG r n a) (δ : ℕ) : Prop :=
  ∀ i : Fin n, (allRefs D.program).count i.val ≤ δ

def InternalBound {r n a : ℕ} (D : DAG r n a) (δ : ℕ) : Prop :=
  ∀ i : Fin D.size, (allRefs D.program).count (n+1+i.val)+(outputRefs D).count (n+1+i.val) ≤ δ

def FreshOutputs {r n a : ℕ} (D : DAG r n a) : Prop :=
  Function.Injective D.outputs ∧ ∀ i, n < (D.outputs i).val

def TerminalOutputs {r n a : ℕ} (D : DAG r n a) : Prop :=
  ∀ i, (allRefs D.program).count (D.outputs i).val=0

theorem convolutionDAG_fresh (k n m : ℕ) (hm : m ≤ width k) :
    FreshOutputs (convolutionDAG k n m hm) := by
  constructor
  · intro i j h
    have hv := congrArg Fin.val h
    simp only [convolutionDAG,UniformConvolutionDAG.outputIndex,UniformConvolutionDAG.nodeFin_normalize] at hv
    exact Fin.ext (by omega)
  · intro i
    change n<n+1+(UniformConvolutionDAG.nodeFin k (.normalize ⟨i.val,i.isLt.trans_le hm⟩)).val
    omega

theorem convolutionDAG_terminal (k n m : ℕ) (hm : m ≤ width k) :
    TerminalOutputs (convolutionDAG k n m hm) := by
  intro i
  exact (convolution_node_uses k n (.normalize ⟨i.val,i.isLt.trans_le hm⟩)).trans (by rfl)

theorem convolutionDAG_inputBound (k n m : ℕ) (hn : n ≤ width k) (hm : m ≤ width k) :
    InputBound (convolutionDAG k n m hm) 2 := by
  intro i
  exact (convolution_input_uses k n hn i).trans_le (UniformConvolutionDAG.successors_bound _)

theorem outputRefs_count_of_injective {r n a : ℕ} (D : DAG r n a) (h : Function.Injective D.outputs)
    (port : ℕ) : (outputRefs D).count port ≤ 1 := by
  have hi : Function.Injective (fun i : Fin a => (D.outputs i).val) := Fin.val_injective.comp h
  have hn : (outputRefs D).Nodup := (List.nodup_finRange a).map hi
  rw [hn.count]
  split_ifs <;> omega

theorem convolutionDAG_nonterminal_output_count (k n m : ℕ) (hm : m ≤ width k)
    (j : UniformConvolutionDAG.Node k) (hj : ∀ i, j≠.normalize i) :
    (outputRefs (convolutionDAG k n m hm)).count (n+1+(UniformConvolutionDAG.nodeFin k j).val)=0 := by
  apply List.count_eq_zero_of_not_mem
  intro h
  obtain ⟨u,_,hu⟩ := List.mem_map.mp h
  have hh := congrArg (fun t => t-(n+1)) hu
  simp only [convolutionDAG,UniformConvolutionDAG.outputIndex,Nat.add_sub_cancel_left] at hh
  have hf : UniformConvolutionDAG.Node.normalize ⟨u.val,u.isLt.trans_le hm⟩ = j :=
    (UniformConvolutionDAG.nodeFin k).injective (Fin.ext hh)
  exact hj _ hf.symm

theorem convolutionDAG_internalBound (k n m : ℕ) (hm : m ≤ width k) :
    InternalBound (convolutionDAG k n m hm) 2 := by
  intro i
  let i' : Fin (UniformConvolutionDAG.total k) := ⟨i.val,i.isLt⟩
  let j := (UniformConvolutionDAG.nodeFin k).symm i'
  have he : i.val=(UniformConvolutionDAG.nodeFin k j).val :=
    (congrArg Fin.val ((UniformConvolutionDAG.nodeFin k).apply_symm_apply i')).symm
  rw [he]
  change (allRefs (UniformConvolutionDAG.paddedProgram k n)).count (n+1+(UniformConvolutionDAG.nodeFin k j).val)+
    (outputRefs (convolutionDAG k n m hm)).count (n+1+(UniformConvolutionDAG.nodeFin k j).val) ≤ 2
  rw [convolution_node_uses]
  cases j with
  | normalize j =>
    have hc := outputRefs_count_of_injective (convolutionDAG k n m hm) (convolutionDAG_fresh k n m hm).1
      (n+1+(UniformConvolutionDAG.nodeFin k (.normalize j)).val)
    simp only [UniformConvolutionDAG.successors,List.length_nil]
    omega
  | forward j =>
    rw [convolutionDAG_nonterminal_output_count k n m hm (.forward j) (by intro i h; cases h),Nat.add_zero]
    exact UniformConvolutionDAG.successors_bound _
  | diagonal j =>
    rw [convolutionDAG_nonterminal_output_count k n m hm (.diagonal j) (by intro i h; cases h),Nat.add_zero]
    exact UniformConvolutionDAG.successors_bound _
  | backward j =>
    rw [convolutionDAG_nonterminal_output_count k n m hm (.backward j) (by intro i h; cases h),Nat.add_zero]
    exact UniformConvolutionDAG.successors_bound _

theorem appendWire_injective {n m t : ℕ} (f : Fin (m+1) → Fin (n+1+t))
    (hf : Function.Injective f) : Function.Injective (appendWire f) := by
  intro a b h
  by_cases ha : a < m+1 <;> by_cases hb : b < m+1
  · simp only [appendWire,dite_eq_left ha,dite_eq_left hb] at h
    exact congrArg Fin.val (hf (Fin.ext h))
  · simp only [appendWire,dite_eq_left ha,dite_eq_right hb] at h
    have := (f ⟨a,ha⟩).isLt; omega
  · simp only [appendWire,dite_eq_right ha,dite_eq_left hb] at h
    have := (f ⟨b,hb⟩).isLt; omega
  · simp only [appendWire,dite_eq_right ha,dite_eq_right hb] at h
    omega

theorem appendWire_node {n m t : ℕ} (f : Fin (m+1) → Fin (n+1+t)) (j : ℕ) :
    appendWire f (m+1+j)=n+1+t+j := by
  simp only [appendWire,dite_eq_right (show ¬m+1+j < m+1 by omega),Nat.add_sub_cancel_left]

theorem appendWire_initial {n m t : ℕ} (f : Fin (m+1) → Fin (n+1+t)) (i : Fin (m+1)) :
    appendWire f i.val=(f i).val := by simp only [appendWire,dite_eq_left i.isLt]

theorem appendWire_avoid_old {n m t : ℕ} (f : Fin (m+1) → Fin (n+1+t))
    (b : ℕ) (hb : b<n+1+t) (h : ∀ i, (f i).val≠b) : ∀ a, appendWire f a≠b := by
  intro a
  unfold appendWire
  split_ifs with ha
  · exact h ⟨a,ha⟩
  · omega

theorem allRefs_mapProgram {r s n t : ℕ} (f : Fin r → Fin s)
    (p : UniformReplayPrint.Program r n t) : allRefs (mapProgram f p)=allRefs p := by
  induction p with
  | nil => rfl
  | step p g ih =>
    simp only [mapProgram,allRefs,programRecords,List.flatMap_append,List.flatMap_singleton]
    rw [show (programRecords (mapProgram f p)).flatMap UniformConvolutionDAG.Expr.refs=allRefs p from ih]
    congr 1
    cases g <;> rfl

theorem DAG.mapCoefficients_bounds {r s n a : ℕ} (f : Fin r → Fin s) (D : DAG r n a) (I J : ℕ)
    (hi : InputBound D I) (hj : InternalBound D J) (hf : FreshOutputs D) (ht : TerminalOutputs D) :
    InputBound (D.mapCoefficients f) I ∧ InternalBound (D.mapCoefficients f) J ∧
    FreshOutputs (D.mapCoefficients f) ∧ TerminalOutputs (D.mapCoefficients f) := by
  change (∀ i : Fin n, (allRefs (mapProgram f D.program)).count i.val ≤ I) ∧
    (∀ i : Fin D.size, (allRefs (mapProgram f D.program)).count (n+1+i.val)+(outputRefs D).count (n+1+i.val) ≤ J) ∧
    FreshOutputs D ∧ (∀ i, (allRefs (mapProgram f D.program)).count (D.outputs i).val=0)
  rw [allRefs_mapProgram]
  exact ⟨hi,hj,hf,ht⟩

theorem comp_wiring_injective {r n a : ℕ} (E : DAG r n a) (hf : FreshOutputs E) :
    Function.Injective (Fin.snoc E.outputs (⟨n,by omega⟩ : Fin (n+1+E.size))) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      have hv := congrArg Fin.val h
      change n=(E.outputs j).val at hv
      have := hf.2 j
      omega
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      have hv := congrArg Fin.val h
      change (E.outputs i).val=n at hv
      have := hf.2 i
      omega
    · intro h
      simp only [Fin.snoc_castSucc] at h
      exact congrArg Fin.castSucc (hf.1 h)

theorem outputRefs_comp {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a) :
    outputRefs (D.comp E)=(outputRefs D).map
      (appendWire (Fin.snoc E.outputs (⟨n,by omega⟩ : Fin (n+1+E.size)))) := by
  simp only [outputRefs,DAG.comp,List.map_map,Function.comp_def,appendIndex_val]

theorem DAG.comp_fresh {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a)
    (hd : FreshOutputs D) (he : FreshOutputs E) : FreshOutputs (D.comp E) := by
  let f : Fin (a+1) → Fin (n+1+E.size) := Fin.snoc E.outputs ⟨n,by omega⟩
  have hinj := appendWire_injective f (comp_wiring_injective E he)
  constructor
  · intro i j hij
    apply hd.1
    apply Fin.ext
    apply hinj
    simpa only [DAG.comp,Function.comp_apply,appendIndex_val] using congrArg Fin.val hij
  · intro i
    have hi := hd.2 i
    change n<(appendIndex f (D.outputs i)).val
    rw [appendIndex_val]
    unfold appendWire
    rw [dite_eq_right (by omega)]
    omega

theorem DAG.comp_terminal {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a)
    (hd : FreshOutputs D) (he : FreshOutputs E) (ht : TerminalOutputs D) : TerminalOutputs (D.comp E) := by
  let f : Fin (a+1) → Fin (n+1+E.size) := Fin.snoc E.outputs ⟨n,by omega⟩
  have hinj := appendWire_injective f (comp_wiring_injective E he)
  intro i
  change (allRefs (appendProgram E.program f D.program)).count (appendIndex f (D.outputs i)).val=0
  rw [allRefs_append,List.count_append,appendIndex_val,List.count_map_of_injective _ _ hinj]
  rw [ht i,Nat.add_zero]
  apply List.count_eq_zero_of_not_mem
  intro hmem
  have hb := allRefs_bound E.program _ hmem
  have hi := hd.2 i
  unfold appendWire at hb
  rw [dite_eq_right (by omega)] at hb
  omega

theorem DAG.comp_inputBound {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a)
    (he : FreshOutputs E) (hE : InputBound E 2) : InputBound (D.comp E) 2 := by
  let f : Fin (a+1) → Fin (n+1+E.size) := Fin.snoc E.outputs ⟨n,by omega⟩
  intro i
  change (allRefs (appendProgram E.program f D.program)).count i.val ≤ 2
  rw [allRefs_append,List.count_append]
  have hn : ∀ j : Fin (a+1), (f j).val≠i.val := by
    intro j; refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [f,Fin.snoc_last]; have := i.isLt; omega
    · simp only [f,Fin.snoc_castSucc]; have := he.2 j; have := i.isLt; omega
  rw [count_map_zero _ _ _ (fun x _ => appendWire_avoid_old f i.val (by have := i.isLt; omega) hn x),Nat.add_zero]
  exact hE i

theorem DAG.comp_internalBound {r n a b : ℕ} (D : DAG r a b) (E : DAG r n a)
    (he : FreshOutputs E) (hd : FreshOutputs D) (ht : TerminalOutputs E)
    (hE : InternalBound E 2) (hDi : InputBound D 2) (hD : InternalBound D 2) :
    InternalBound (D.comp E) 2 := by
  let f : Fin (a+1) → Fin (n+1+E.size) := Fin.snoc E.outputs ⟨n,by omega⟩
  have hinj := appendWire_injective f (comp_wiring_injective E he)
  intro i
  change (allRefs (appendProgram E.program f D.program)).count (n+1+i.val)+
    (outputRefs (D.comp E)).count (n+1+i.val) ≤ 2
  rw [allRefs_append,List.count_append,outputRefs_comp]
  by_cases hi : i.val<E.size
  · have hout : ((outputRefs D).map (appendWire f)).count (n+1+i.val)=0 := by
      apply count_map_zero
      intro x hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      have hj := hd.2 j
      unfold appendWire
      rw [dite_eq_right (by omega)]
      omega
    rw [hout,Nat.add_zero]
    by_cases ho : ∃ j : Fin a, (E.outputs j).val=n+1+i.val
    · obtain ⟨j,hj⟩ := ho
      have hw : appendWire f j.val=n+1+i.val := by
        calc
          appendWire f j.val=(f j.castSucc).val := appendWire_initial f j.castSucc
          _=n+1+i.val := by simpa only [f,Fin.snoc_castSucc] using hj
      rw [← hj,ht j,hj,Nat.zero_add,← hw,List.count_map_of_injective _ _ hinj]
      exact hDi j
    · have hn : ∀ j : Fin (a+1), (f j).val≠n+1+i.val := by
        intro j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [f,Fin.snoc_last]; omega
        · simp only [f,Fin.snoc_castSucc]; exact fun h => ho ⟨j,h⟩
      rw [count_map_zero _ _ _ (fun x _ => appendWire_avoid_old f (n+1+i.val) (by omega) hn x),Nat.add_zero]
      exact (Nat.le_add_right _ _).trans (hE ⟨i.val,hi⟩)
  · let j : Fin D.size := ⟨i.val-E.size,by have := i.isLt; change i.val<E.size+D.size at this; omega⟩
    have hw : appendWire f (a+1+j.val)=n+1+i.val := by rw [appendWire_node]; dsimp [j]; omega
    have hp : (allRefs E.program).count (n+1+i.val)=0 := by
      apply List.count_eq_zero_of_not_mem
      intro hm
      have := allRefs_bound E.program _ hm
      omega
    rw [hp,Nat.zero_add,← hw,List.count_map_of_injective _ _ hinj,List.count_map_of_injective _ _ hinj]
    exact hD j

theorem reverse_wiring_injective (n : ℕ) : Function.Injective
    (Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j; refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h; simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      have hv := congrArg Fin.val h; have hlt := j.rev.isLt; simp only [Fin.val_last,Fin.val_castSucc] at hv; omega
  · intro j; refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      have hv := congrArg Fin.val h; have hlt := i.rev.isLt; simp only [Fin.val_last,Fin.val_castSucc] at hv; omega
    · intro h; simp only [Fin.snoc_castSucc] at h
      exact congrArg Fin.castSucc (Fin.rev_injective (Fin.castSucc_injective n h))

theorem reverse_wire_node (n p : ℕ) (hp : n < p) :
    appendWire (n := n) (m := n) (t := 0) (Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)) p=p := by
  unfold appendWire
  rw [dite_eq_right (by omega)]
  omega

theorem DAG.reverseInputs_outputVals {r n a : ℕ} (D : DAG r n a) (hf : FreshOutputs D) (i : Fin a) :
    (D.reverseInputs.outputs i).val=(D.outputs i).val := by
  change (appendIndex (n := n) (m := n) (k := 0) (l := D.size) (Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)) (D.outputs i)).val=(D.outputs i).val
  rw [appendIndex_val]
  exact reverse_wire_node n _ (hf.2 i)

theorem DAG.reverseInputs_outputRefs {r n a : ℕ} (D : DAG r n a) (hf : FreshOutputs D) :
    outputRefs D.reverseInputs=outputRefs D := by
  apply List.map_congr_left
  intro i _
  exact D.reverseInputs_outputVals hf i

theorem DAG.reverseInputs_bounds {r n a : ℕ} (D : DAG r n a)
    (hi : InputBound D 2) (hj : InternalBound D 2) (hf : FreshOutputs D) (ht : TerminalOutputs D) :
    InputBound D.reverseInputs 2 ∧ InternalBound D.reverseInputs 2 ∧
      FreshOutputs D.reverseInputs ∧ TerminalOutputs D.reverseInputs := by
  let f : Fin (n+1) → Fin (n+1) := Fin.snoc (fun i : Fin n => i.rev.castSucc) (Fin.last n)
  have hinj := appendWire_injective (n := n) (m := n) (t := 0) f (reverse_wiring_injective n)
  have hp : allRefs D.reverseInputs.program=(allRefs D.program).map (appendWire (n := n) (m := n) (t := 0) f) := by
    change allRefs (appendProgram .nil f D.program)=(allRefs D.program).map (appendWire (n := n) (m := n) (t := 0) f)
    rw [allRefs_append]
    rfl
  have ho := D.reverseInputs_outputRefs hf
  constructor
  · intro i
    rw [hp]
    have hv : appendWire (n := n) (m := n) (t := 0) f i.rev.val=i.val := by
      calc
        appendWire (n := n) (m := n) (t := 0) f i.rev.val=(f i.rev.castSucc).val := appendWire_initial (n := n) (m := n) (t := 0) f i.rev.castSucc
        _=i.val := by simp only [f,Fin.snoc_castSucc,Fin.rev_rev,Fin.val_castSucc]
    rw [← hv,List.count_map_of_injective _ _ hinj]
    exact hi i.rev
  constructor
  · intro i
    rw [hp,ho,← reverse_wire_node n (n+1+i.val) (by omega),List.count_map_of_injective _ _ hinj]
    rw [reverse_wire_node n (n+1+i.val) (by omega)]
    exact hj ⟨i.val,by simpa only [DAG.reverseInputs,Nat.zero_add] using i.isLt⟩
  constructor
  · constructor
    · intro i j h
      apply hf.1; apply Fin.ext
      have hv := congrArg Fin.val h
      rw [D.reverseInputs_outputVals hf,D.reverseInputs_outputVals hf] at hv
      exact hv
    · intro i; rw [D.reverseInputs_outputVals hf]; exact hf.2 i
  · intro i
    rw [hp,D.reverseInputs_outputVals hf,← reverse_wire_node n (D.outputs i).val (hf.2 i),
      List.count_map_of_injective _ _ hinj]
    exact ht i

theorem DAG.reverseOutputs_outputCount {r n a : ℕ} (D : DAG r n a) (hf : FreshOutputs D) (p : ℕ) :
    (outputRefs D.reverseOutputs).count p=(outputRefs D).count p := by
  have h₁ : (outputRefs D).Nodup := (List.nodup_finRange a).map (Fin.val_injective.comp hf.1)
  have h₂ : (outputRefs D.reverseOutputs).Nodup := (List.nodup_finRange a).map
    (Fin.val_injective.comp (hf.1.comp Fin.rev_injective))
  rw [h₁.count,h₂.count]
  have hm : p ∈ outputRefs D.reverseOutputs ↔ p ∈ outputRefs D := by
    simp only [outputRefs,List.mem_map,List.mem_finRange,true_and,DAG.reverseOutputs,Function.comp_apply]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨i.rev,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨i.rev,by simpa only [Fin.rev_rev] using hi⟩
  simp only [hm]

theorem DAG.reverseOutputs_bounds {r n a : ℕ} (D : DAG r n a)
    (hi : InputBound D 2) (hj : InternalBound D 2) (hf : FreshOutputs D) (ht : TerminalOutputs D) :
    InputBound D.reverseOutputs 2 ∧ InternalBound D.reverseOutputs 2 ∧
      FreshOutputs D.reverseOutputs ∧ TerminalOutputs D.reverseOutputs := by
  refine ⟨hi,?_,⟨hf.1.comp Fin.rev_injective,fun i => hf.2 i.rev⟩,fun i => ht i.rev⟩
  intro i
  rw [D.reverseOutputs_outputCount hf]
  exact hj i

theorem kernelDAG_bounds (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) (b : Fin 3) :
    InputBound (kernelDAG k a e ha he b) 2 ∧ InternalBound (kernelDAG k a e ha he b) 2 ∧
    FreshOutputs (kernelDAG k a e ha he b) ∧ TerminalOutputs (kernelDAG k a e ha he b) := by
  have hs := DAG.mapCoefficients_bounds (coefficientEmbedding k (secondSlot b))
    (convolutionDAG k e a ha) 2 2 (convolutionDAG_inputBound k e a he ha)
    (convolutionDAG_internalBound k e a ha) (convolutionDAG_fresh k e a ha) (convolutionDAG_terminal k e a ha)
  have hr := DAG.reverseInputs_bounds (convolutionDAG k e e he)
    (convolutionDAG_inputBound k e e he he) (convolutionDAG_internalBound k e e he)
    (convolutionDAG_fresh k e e he) (convolutionDAG_terminal k e e he)
  have ht := DAG.reverseOutputs_bounds _ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hf := DAG.mapCoefficients_bounds (coefficientEmbedding k (firstSlot b)) _ 2 2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
  refine ⟨DAG.comp_inputBound _ _ hf.2.2.1 hf.1,
    DAG.comp_internalBound _ _ hf.2.2.1 hs.2.2.1 hf.2.2.2 hf.2.1 hs.1 hs.2.1,
    DAG.comp_fresh _ _ hs.2.2.1 hf.2.2.1,DAG.comp_terminal _ _ hs.2.2.1 hf.2.2.1 hs.2.2.2⟩

end

/-- Parallel concatenation shares all original data ports. -/
/- Paper: Equation (3.10), p. 16: bounded fan-out is retained under explicit graph combination, including output references; no coefficient is inspected. -/
def DAG.join {r n a b : ℕ} (A : DAG r n a) (B : DAG r n b) : DAG r n (a+b) :=
  let f : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  ⟨A.size+B.size,appendProgram A.program f B.program,
    Fin.addCases (fun i => keepIndex (l := B.size) (A.outputs i))
      (fun j => appendIndex f (B.outputs j))⟩

noncomputable section

theorem join_wiring_injective (n t : ℕ) : Function.Injective
    (fun i : Fin (n+1) => (⟨i.val,by have := i.isLt; omega⟩ : Fin (n+1+t))) := by
  intro i j h; exact Fin.ext (congrArg (fun z : Fin (n+1+t) => z.val) h)

theorem outputRefs_join {r n a b : ℕ} (A : DAG r n a) (B : DAG r n b) :
    outputRefs (A.join B)=outputRefs A ++(outputRefs B).map (appendWire
      (fun i : Fin (n+1) => (⟨i.val,by have := i.isLt; omega⟩ : Fin (n+1+A.size)))) := by
  simp only [outputRefs,← List.ofFn_eq_map,DAG.join]
  rw [List.ofFn_add (n := a) (m := b),List.map_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext i
    have hc : (Fin.castLE (Nat.le_add_right a b) i)=i.castAdd b := rfl
    rw [hc,Fin.addCases_left]
    rfl
  · apply congrArg List.ofFn
    funext i
    rw [Fin.addCases_right]
    exact appendIndex_val _ _

theorem DAG.join_inputBound {r n a b : ℕ} (A : DAG r n a) (B : DAG r n b) (I J : ℕ)
    (hA : InputBound A I) (hB : InputBound B J) : InputBound (A.join B) (I+J) := by
  let f : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  have hinj := appendWire_injective f (join_wiring_injective n A.size)
  intro i
  change (allRefs (appendProgram A.program f B.program)).count i.val ≤ I+J
  rw [allRefs_append,List.count_append]
  have hw : appendWire f i.val=i.val := appendWire_initial f i.castSucc
  rw [← hw,List.count_map_of_injective _ _ hinj]
  rw [hw]
  exact Nat.add_le_add (hA i) (hB i)

theorem DAG.join_internalBound {r n a b : ℕ} (A : DAG r n a) (B : DAG r n b)
    (hA : InternalBound A 2) (hB : InternalBound B 2) (hfB : FreshOutputs B) :
    InternalBound (A.join B) 2 := by
  let f : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  have hinj := appendWire_injective f (join_wiring_injective n A.size)
  intro i
  change (allRefs (appendProgram A.program f B.program)).count (n+1+i.val)+
    (outputRefs (A.join B)).count (n+1+i.val) ≤ 2
  rw [allRefs_append,outputRefs_join,List.count_append,List.count_append]
  by_cases hi : i.val<A.size
  · have hp : ((allRefs B.program).map (appendWire f)).count (n+1+i.val)=0 := by
      apply count_map_zero
      intro x _
      apply appendWire_avoid_old f (n+1+i.val) (by omega)
      intro j; change j.val≠n+1+i.val; have := j.isLt; omega
    have ho : ((outputRefs B).map (appendWire f)).count (n+1+i.val)=0 := by
      apply count_map_zero
      intro x hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      have := hfB.2 j
      unfold appendWire
      rw [dite_eq_right (by omega)]
      omega
    rw [hp,ho,Nat.add_zero,Nat.add_zero]
    exact hA ⟨i.val,hi⟩
  · let j : Fin B.size := ⟨i.val-A.size,by have := i.isLt; change i.val<A.size+B.size at this; omega⟩
    have hw : appendWire f (n+1+j.val)=n+1+i.val := by rw [appendWire_node]; dsimp [j]; omega
    have hp : (allRefs A.program).count (n+1+i.val)=0 := by
      apply List.count_eq_zero_of_not_mem; intro h
      have := allRefs_bound A.program _ h; omega
    have ho : (outputRefs A).count (n+1+i.val)=0 := by
      apply List.count_eq_zero_of_not_mem; intro h
      obtain ⟨l,_,hl⟩ := List.mem_map.mp h
      have := (A.outputs l).isLt; omega
    rw [hp,ho,Nat.zero_add,Nat.zero_add,← hw,List.count_map_of_injective _ _ hinj,List.count_map_of_injective _ _ hinj]
    exact hB j

theorem DAG.join_outputs_lower {r n a b : ℕ} (A : DAG r n a) (B : DAG r n b)
    (hA : ∀ i, n<(A.outputs i).val) (hB : ∀ i, n<(B.outputs i).val) :
    ∀ i, n<((A.join B).outputs i).val := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [DAG.join,Fin.addCases_left,keepIndex] using hA i
  · simp only [DAG.join,Fin.addCases_right]
    rw [appendIndex_val]
    have := hB i
    unfold appendWire
    rw [dite_eq_right (by omega)]
    omega

theorem allRefs_emit {r n t a : ℕ} (p : UniformReplayPrint.Program r n t)
    (g : Fin a → UniformReplayPrint.Gate r (n+1+t)) :
    allRefs (emitProgram p g)=allRefs p ++
      ((List.finRange a).flatMap (fun i => (gateRecord (g i)).refs)) := by
  simp only [allRefs,emitProgram_records,List.flatMap_append,List.ofFn_eq_map,List.flatMap_map]

theorem count_flatMap_pairs {α : Type} (l : List α) (f g : α → ℕ) (p : ℕ) :
    (l.flatMap (fun i => [f i,g i])).count p=(l.map f).count p+(l.map g).count p := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.flatMap_cons,List.count_append,List.map_cons,List.count_cons,List.count_nil]
    rw [ih]
    omega

def nodePorts (n t a : ℕ) : List ℕ := (List.finRange a).map (fun i => n+1+t+i.val)

theorem nodePorts_count (n t a p : ℕ) : (nodePorts n t a).count p ≤ 1 := by
  have hi : Function.Injective (fun i : Fin a => n+1+t+i.val) := by
    intro i j h; apply Fin.ext; change n+1+t+i.val=n+1+t+j.val at h; omega
  unfold nodePorts
  rw [((List.nodup_finRange a).map hi).count]
  split_ifs <;> omega

theorem nodePorts_zero (n t a p : ℕ) (hp : p<n+1+t ∨ n+1+t+a ≤ p) :
    (nodePorts n t a).count p=0 := by
  apply List.count_eq_zero_of_not_mem
  intro h
  obtain ⟨i,_,hi⟩ := List.mem_map.mp h
  have := i.isLt
  omega

theorem sumThree_outputRefs {r n a : ℕ} (A B D : DAG r n a) :
    outputRefs (A.sumThree B D)=nodePorts n (((A.size+B.size)+D.size)+a) a := rfl

theorem sumThree_refCounts {r n a : ℕ} (A B D : DAG r n a) (p : ℕ) :
    (allRefs (A.sumThree B D).program).count p =
      (allRefs ((A.join B).join D).program).count p+
        (outputRefs ((A.join B).join D)).count p+
        (nodePorts n ((A.size+B.size)+D.size) a).count p := by
  let f₁ : Fin (n+1) → Fin (n+1+A.size) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let f₂ : Fin (n+1) → Fin (n+1+(A.size+B.size)) := fun i => ⟨i.val,by have := i.isLt; omega⟩
  let p₂ := appendProgram (appendProgram A.program f₁ B.program) f₂ D.program
  let ga : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size)) := fun i => .add
    (keepIndex (l := D.size) (keepIndex (l := B.size) (A.outputs i)))
    (keepIndex (l := D.size) (appendIndex f₁ (B.outputs i)))
  let p₃ := emitProgram p₂ ga
  let gb : Fin a → UniformReplayPrint.Gate r (n+1+((A.size+B.size)+D.size+a)) := fun i => .add
    (gateIndex i) (keepIndex (appendIndex f₂ (D.outputs i)))
  change (allRefs (emitProgram p₃ gb)).count p = _
  rw [allRefs_emit,List.count_append,show allRefs p₃=allRefs p₂++
    (List.finRange a).flatMap (fun i => (gateRecord (ga i)).refs) from allRefs_emit p₂ ga,List.count_append]
  simp only [ga,gb,gateRecord,UniformConvolutionDAG.Expr.refs,keepIndex,gateIndex]
  rw [count_flatMap_pairs,count_flatMap_pairs]
  rw [outputRefs_join,outputRefs_join,List.count_append,List.count_append]
  change _ = (allRefs p₂).count p+((outputRefs A).count p+
    ((outputRefs B).map (appendWire f₁)).count p+
    ((outputRefs D).map (appendWire f₂)).count p)+(nodePorts n ((A.size+B.size)+D.size) a).count p
  simp only [outputRefs,nodePorts,List.map_map,Function.comp_def,appendIndex_val]
  omega

theorem DAG.sumThree_fresh {r n a : ℕ} (A B D : DAG r n a) : FreshOutputs (A.sumThree B D) := by
  constructor
  · intro i j h; apply Fin.ext
    have hv := congrArg Fin.val h
    change n+1+((A.size+B.size)+D.size+a)+i.val=n+1+((A.size+B.size)+D.size+a)+j.val at hv
    omega
  · intro i
    change n<n+1+((A.size+B.size)+D.size+a)+i.val
    omega

theorem DAG.sumThree_bounds {r n a : ℕ} (A B D : DAG r n a)
    (hAi : InputBound A 2) (hBi : InputBound B 2) (hDi : InputBound D 2)
    (hA : InternalBound A 2) (hB : InternalBound B 2) (hD : InternalBound D 2)
    (hAf : FreshOutputs A) (hBf : FreshOutputs B) (hDf : FreshOutputs D) :
    InputBound (A.sumThree B D) 6 ∧ InternalBound (A.sumThree B D) 2 := by
  let P := (A.join B).join D
  have hPi : InputBound P 6 := DAG.join_inputBound _ _ 4 2
    (DAG.join_inputBound A B 2 2 hAi hBi) hDi
  have hP : InternalBound P 2 := DAG.join_internalBound _ _
    (DAG.join_internalBound A B hA hB hBf) hD hDf
  have hPlow : ∀ i, n<(P.outputs i).val := DAG.join_outputs_lower _ _
    (DAG.join_outputs_lower A B hAf.2 hBf.2) hDf.2
  have hpout (p : ℕ) (hp : p≤n) : (outputRefs P).count p=0 := by
    apply List.count_eq_zero_of_not_mem; intro h
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    have := hPlow i
    omega
  have hpref (p : ℕ) (hp : n+1+P.size ≤ p) : (allRefs P.program).count p=0 := by
    apply List.count_eq_zero_of_not_mem; intro h
    have := allRefs_bound P.program _ h
    omega
  have hpouts (p : ℕ) (hp : n+1+P.size ≤ p) : (outputRefs P).count p=0 := by
    apply List.count_eq_zero_of_not_mem; intro h
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    have := (P.outputs i).isLt
    omega
  constructor
  · intro i
    rw [sumThree_refCounts,hpout i.val (by have := i.isLt; omega),
      nodePorts_zero n ((A.size+B.size)+D.size) a i.val (Or.inl (by have := i.isLt; omega))]
    simp only [Nat.add_zero]
    exact hPi i
  · intro i
    rw [sumThree_refCounts,sumThree_outputRefs]
    by_cases hi : i.val<P.size
    · rw [nodePorts_zero n ((A.size+B.size)+D.size) a (n+1+i.val) (Or.inl (by change i.val<(A.size+B.size)+D.size at hi; omega)),
        nodePorts_zero n (((A.size+B.size)+D.size)+a) a (n+1+i.val) (Or.inl (by change i.val<(A.size+B.size)+D.size at hi; omega)),Nat.add_zero,Nat.add_zero]
      exact hP ⟨i.val,hi⟩
    · rw [hpref (n+1+i.val) (by omega),hpouts (n+1+i.val) (by omega)]
      simp only [Nat.zero_add]
      by_cases hia : i.val<P.size+a
      · rw [nodePorts_zero n (((A.size+B.size)+D.size)+a) a (n+1+i.val) (Or.inl (by change i.val<(A.size+B.size)+D.size+a at hia; omega)),Nat.add_zero]
        exact (nodePorts_count _ _ _ _).trans (by omega)
      · rw [nodePorts_zero n ((A.size+B.size)+D.size) a (n+1+i.val) (Or.inr (by change ¬i.val<(A.size+B.size)+D.size+a at hia; omega)),Nat.zero_add]
        exact (nodePorts_count _ _ _ _).trans (by omega)

theorem crossDAG_fanout_parts (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) :
    InputBound (crossDAG k a e ha he) 6 ∧ InternalBound (crossDAG k a e ha he) 2 := by
  have h₀ := kernelDAG_bounds k a e ha he 0
  have h₁ := kernelDAG_bounds k a e ha he 1
  have h₂ := kernelDAG_bounds k a e ha he 2
  exact DAG.sumThree_bounds _ _ _ h₀.1 h₁.1 h₂.1 h₀.2.1 h₁.2.1 h₂.2.1 h₀.2.2.1 h₁.2.2.1 h₂.2.2.1

theorem physicalUseCount_bound {r n a : ℕ} (D : DAG r n a) (I J : ℕ)
    (hI : InputBound D I) (hJ : InternalBound D J) (hf : FreshOutputs D) :
    ∀ p, physicalUseCount D p ≤ max I J := by
  intro p
  by_cases hpzero : p=n
  · simp only [physicalUseCount,hpzero,ite_true]; omega
  · rw [physicalUseCount,ite_eq_right hpzero]
    change (allRefs D.program).count p+(outputRefs D).count p ≤ max I J
    by_cases hp : p<n
    · have ho : (outputRefs D).count p=0 := by
        apply List.count_eq_zero_of_not_mem; intro h
        obtain ⟨i,_,hi⟩ := List.mem_map.mp h
        have := hf.2 i; omega
      rw [ho,Nat.add_zero]
      exact (hI ⟨p,hp⟩).trans (Nat.le_max_left _ _)
    · by_cases hb : p<n+1+D.size
      · let i : Fin D.size := ⟨p-(n+1),by omega⟩
        have he : n+1+i.val=p := by dsimp [i]; omega
        rw [← he]
        exact (hJ i).trans (Nat.le_max_right _ _)
      · have hr : (allRefs D.program).count p=0 := by
          apply List.count_eq_zero_of_not_mem; intro h
          have := allRefs_bound D.program _ h; omega
        have ho : (outputRefs D).count p=0 := by
          apply List.count_eq_zero_of_not_mem; intro h
          obtain ⟨i,_,hi⟩ := List.mem_map.mp h
          have := (D.outputs i).isLt; omega
        rw [hr,ho]; omega

/-- Literal operand counts of the same typed cross program: at most six uses
per original input, at most two per generated register including outputs.
Only the syntactic zero port is removed; prepared-bank reuse is separate. -/
theorem crossDAG_physicalFanout (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) (port : ℕ) :
    physicalUseCount (crossDAG k a e ha he) port ≤ 6 := by
  have h := crossDAG_fanout_parts k a e ha he
  exact physicalUseCount_bound _ 6 2 h.1 h.2 (DAG.sumThree_fresh _ _ _) port

/-- Semantic bank specification, not a free scalar-production operation. -/
def sharedBank (k : ℕ) (kernels : Fin 6 → Fin (width k) → ℂ) : Fin (bankSize k) → ℂ :=
  Fin.addCases (fun i => zeta (width k)^i.val)
    (fun i => (fourierMatrix (width k)).mulVec (kernels (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2)

theorem sharedBank_embedding (k : ℕ) (kernels : Fin 6 → Fin (width k) → ℂ) (b : Fin 6) :
    sharedBank k kernels ∘ coefficientEmbedding k b = UniformConvolutionDAG.coefficientBank k (kernels b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,coefficientEmbedding,Fin.addCases_left,sharedBank,
      Fin.addCases_left,UniformConvolutionDAG.coefficientBank,Fin.addCases_left]
  · simp only [Function.comp_apply,coefficientEmbedding,Fin.addCases_right,sharedBank,
      Fin.addCases_right,Equiv.symm_apply_apply,UniformConvolutionDAG.coefficientBank,Fin.addCases_right]

/-- The exact triangular convolution computed by a single printed block. -/
/- Paper: Equations (3.3) and (3.9), pp. 14, 16: no-alias padded convolution is the actual lower-Toeplitz action. -/
theorem convolutionDAG_eval (k n t m : ℕ) (hsize : n+t ≤ width k) (hm : m ≤ width k)
    (v : Fin t → ℂ) (x : Fin n → ℂ) :
    (convolutionDAG k n m hm).eval (UniformConvolutionDAG.coefficientBank k
      (UniformConvolutionDAG.inputVector k t (UniformConvolutionDAG.padInputs k t) v)) x =
    (OAI.ExactFourier.Displacement.lower (OAI.ExactFourier.Displacement.extendVector v) m n).mulVec x := by
  funext i
  rw [show (convolutionDAG k n m hm).eval _ x i = _ from
    UniformConvolutionDAG.linear_program_eval k n t m hsize hm v x i]
  simp only [Matrix.mulVec, dotProduct,OAI.ExactFourier.Displacement.lower]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hji hd
  · simp only [OAI.ExactFourier.Displacement.extendVector,dite_eq_left hd]
  · simp only [OAI.ExactFourier.Displacement.extendVector,dite_eq_right hd,zero_mul]
  · simp only [zero_mul]

theorem lower_reverse (e : ℕ) (w : Fin e → ℂ) (x : Fin e → ℂ) :
    (OAI.ExactFourier.Displacement.lower (OAI.ExactFourier.Displacement.extendVector w) e e).mulVec
      (x ∘ Fin.rev) ∘ Fin.rev =
    (OAI.ExactFourier.Displacement.lower (OAI.ExactFourier.Displacement.extendVector w) e e).transpose.mulVec x := by
  funext i
  simp only [Function.comp_apply,Matrix.mulVec,dotProduct,OAI.ExactFourier.Displacement.lower,
    Matrix.transpose_apply]
  rw [← Equiv.sum_comp (Fin.revPerm (n := e))
    (fun j : Fin e => (if j.val ≤ i.rev.val then
      OAI.ExactFourier.Displacement.extendVector w (i.rev.val-j.val) else 0)*x j.rev)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply,Fin.rev_rev]
  have hj := j.isLt
  have hi := i.isLt
  have hle : j.rev.val ≤ i.rev.val ↔ i.val ≤ j.val := by simp only [Fin.val_rev]; omega
  have hdiff : i.rev.val-j.rev.val=j.val-i.val := by simp only [Fin.val_rev]; omega
  simp only [hle,hdiff]

/-- A pair of actual printed convolutions computes one displacement kernel. -/
theorem kernelDAG_eval (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k)
    (hsize : 2*(a+e) ≤ width k) (b : Fin 3) (kernels : Fin 6 → Fin (width k) → ℂ)
    (v : Fin a → ℂ) (w : Fin e → ℂ)
    (hv : kernels (secondSlot b)=UniformConvolutionDAG.inputVector k a (UniformConvolutionDAG.padInputs k a) v)
    (hw : kernels (firstSlot b)=UniformConvolutionDAG.inputVector k e (UniformConvolutionDAG.padInputs k e) w)
    (x : Fin e → ℂ) :
    (kernelDAG k a e ha he b).eval (sharedBank k kernels) x =
      Matrix.mulVec (fun i : Fin a => fun j : Fin e => OAI.ExactFourier.Displacement.kernel
        (OAI.ExactFourier.Displacement.extendVector v) (OAI.ExactFourier.Displacement.extendVector w)
        i.val j.val) x := by
  rw [kernelDAG,DAG.eval_comp,DAG.eval_mapCoefficients,sharedBank_embedding,hv]
  rw [DAG.eval_mapCoefficients,sharedBank_embedding,hw,DAG.eval_reverseOutputs,DAG.eval_reverseInputs]
  rw [convolutionDAG_eval k e e e (by omega) he w (x ∘ Fin.rev),lower_reverse]
  rw [convolutionDAG_eval k e a a (by omega) ha v]
  rw [Matrix.mulVec_mulVec,← OAI.ExactFourier.Displacement.kernel_eq_mul]

/- Paper: Equations (3.6)–(3.8), pp. 15–16: one interior outer product plus first-row and first-column corrections. All three branches remain present if entries vanish. -/
def leftFactor (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ) (b : Fin 3) : ℕ → ℂ :=
  if b.val=0 then v else if b.val=1 then OAI.ExactFourier.Displacement.delta
    else fun i => if i=0 then 0 else M i 0-v i*w 0

def rightFactor (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ) (b : Fin 3) : ℕ → ℂ :=
  if b.val=0 then w else if b.val=1 then fun j => M 0 j-v 0*w j
    else OAI.ExactFourier.Displacement.delta

/-- Six zero-extended fixed kernels; the power bank is shared, while spectra
are explicit prepared coefficients for these particular kernels. -/
def rankKernels (k a e : ℕ) (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ)
    (slot : Fin 6) : Fin (width k) → ℂ :=
  let b : Fin 3 := ⟨slot.val/2,by have := slot.isLt; omega⟩
  if slot.val%2=0 then
    UniformConvolutionDAG.inputVector k e (UniformConvolutionDAG.padInputs k e)
      (fun j => rightFactor M v w b j.val)
  else UniformConvolutionDAG.inputVector k a (UniformConvolutionDAG.padInputs k a)
      (fun i => leftFactor M v w b i.val)

@[simp] theorem rankKernels_first (k a e : ℕ) (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ) (b : Fin 3) :
    rankKernels k a e M v w (firstSlot b) =
      UniformConvolutionDAG.inputVector k e (UniformConvolutionDAG.padInputs k e)
        (fun j => rightFactor M v w b j.val) := by
  have hb : (2*b.val)/2=b.val := by omega
  have hp : (2*b.val)%2=0 := by omega
  simp only [rankKernels,firstSlot,hb,hp,ite_true]

@[simp] theorem rankKernels_second (k a e : ℕ) (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ) (b : Fin 3) :
    rankKernels k a e M v w (secondSlot b) =
      UniformConvolutionDAG.inputVector k a (UniformConvolutionDAG.padInputs k a)
        (fun i => leftFactor M v w b i.val) := by
  have hb : (2*b.val+1)/2=b.val := by omega
  have hp : (2*b.val+1)%2≠0 := by omega
  simp only [rankKernels,secondSlot,hb,hp,ite_false]

theorem rankBranch_eval (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k)
    (hsize : 2*(a+e) ≤ width k) (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ) (b : Fin 3) (x : Fin e → ℂ) :
    (kernelDAG k a e ha he b).eval (sharedBank k (rankKernels k a e M v w)) x =
      Matrix.mulVec (fun i : Fin a => fun j : Fin e =>
        OAI.ExactFourier.Displacement.kernel (leftFactor M v w b) (rightFactor M v w b) i.val j.val) x := by
  rw [kernelDAG_eval k a e ha he hsize b (rankKernels k a e M v w)
    (fun i => leftFactor M v w b i.val) (fun j => rightFactor M v w b j.val)
    (rankKernels_second k a e M v w b) (rankKernels_first k a e M v w b) x]
  congr 1
  funext i j
  exact OAI.ExactFourier.Displacement.kernel_restrict _ _ a e i j

/-- Closed action of the literal six-convolution graph, obtained from the
actual rank-three displacement recurrence rather than an action certificate. -/
/- Paper: Equations (3.7)–(3.9), p. 16: the six literal convolutions reconstruct the rank-three displacement matrix. The recurrence assumption is specialized below. -/
theorem crossDAG_eval (k a e : ℕ) (ha : 0<a) (he : 0<e) (hsize : 2*(a+e) ≤ width k)
    (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ)
    (hrec : ∀ i j, i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1))
    (x : Fin e → ℂ) :
    (crossDAG k a e (by omega) (by omega)).eval (sharedBank k (rankKernels k a e M v w)) x =
      Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) x := by
  rw [crossDAG,DAG.eval_sumThree]
  rw [rankBranch_eval k a e (by omega) (by omega) hsize M v w 0 x,
    rankBranch_eval k a e (by omega) (by omega) hsize M v w 1 x,
    rankBranch_eval k a e (by omega) (by omega) hsize M v w 2 x]
  funext i
  simp only [Matrix.mulVec,dotProduct,leftFactor,rightFactor,Fin.val_zero,Fin.val_one,
    show (2 : Fin 3).val=2 from rfl,ite_true,show ¬(1 : ℕ)=0 by omega,
    show ¬(2 : ℕ)=0 by omega,show ¬(2 : ℕ)=1 by omega,ite_false]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [OAI.ExactFourier.Displacement.reconstruct a e ha he M v w hrec i.val j.val i.isLt j.isLt]
  ring

/-- The actual paper Toeplitz-cross recurrence supplies all matrix-action
hypotheses. Reciprocals and spectra still belong to scalar preparation. -/
/- Paper: Equations (3.5)–(3.6), p. 15: ToeplitzLayers.cross_interior supplies the displacement recurrence for every admissible source/target rectangle. -/
theorem toeplitz_cross_eval (k s a e i₀ j₀ : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e) ≤ width k) (h g : ℕ → ℂ) (hi : s ≤ i₀) (hj : j₀+e ≤ s)
    (x : Fin e → ℂ) :
    let M := fun i j => OAI.ExactFourier.ToeplitzLayers.cross s h g (i₀+i) (j₀+j)
    let v := fun i => -h (i₀+i-s)
    let w := fun j => g (s-(j₀+j))
    (crossDAG k a e (by omega) (by omega)).eval (sharedBank k (rankKernels k a e M v w)) x =
      Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) x := by
  dsimp only
  exact crossDAG_eval k a e ha he hsize _ _ _
    (OAI.ExactFourier.ToeplitzLayers.cross_interior s a e i₀ j₀ h g hi hj) x

theorem crossReplay_length (k a e : ℕ) (ha : a ≤ width k) (he : e ≤ width k) :
    (crossReplay k a e ha he).length ≤ 48*(3*k*2^k+2*2^k)+18*a := by
  have h := UniformReplayPrint.replayCode_length (crossDAG k a e ha he).program (crossDAG k a e ha he).outputs
  have hs := crossDAG_size k a e ha he
  exact h.trans (by omega)

/- Paper: Lemma 3.3, pp. 14–15, composed with Lemma 3.4’s cross DAG: dirty gate contents are arbitrary and restored after the target update. -/
theorem crossReplay_spec (k a e : ℕ) (ha : 0<a) (he : 0<e) (hsize : 2*(a+e) ≤ width k)
    (M : ℕ → ℕ → ℂ) (v w : ℕ → ℂ)
    (hrec : ∀ i j, i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1))
    (x : Fin e → ℂ) (y : Fin a → ℂ) (z : Fin (crossDAG k a e (by omega) (by omega)).size → ℂ) :
    runShears ((crossReplay k a e (by omega) (by omega)).map
      (ShearCode.eval (sharedBank k (rankKernels k a e M v w)))) (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z) (fun i => y i+Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) x i) := by
  rw [crossReplay,UniformReplayPrint.replayCode_spec]
  have h := crossDAG_eval k a e ha he hsize M v w hrec x
  exact congrArg (fun o : Fin a → ℂ => Sum.elim (Sum.elim x z) (fun i => y i+o i)) h

end
end ExactFourierCircuits.UniformToeplitzCrossDAG
