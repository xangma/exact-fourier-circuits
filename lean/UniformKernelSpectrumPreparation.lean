import UniformConvolutionDAG
import UniformToeplitzCrossDAG

/-! Shared, scalar-only production of fixed-kernel Fourier spectra.  A root is
read through an existing scalar register.  The extension introduces no root
instruction or division, and contains no array-input or complex-test opcode. -/
namespace ExactFourierCircuits.UniformKernelSpectrumPreparation
open UniformScalarPreparation
open OAI.ExactFourier (zeta fourierMatrix)
open UniformRadixTwoDAG

def powerPrefix {r l : ℕ} (p : Program r l) (omega : Fin l) :
    (t : ℕ) → Program r (l + (t + 1))
  | 0 => .step p (.rational 1)
  | t + 1 => .step (powerPrefix p omega t)
      (.mul (omega.castAdd (t+1)) (Fin.last (l+t)))

def powerRef {l t : ℕ} (j : ℕ) (hj : j ≤ t) : Fin (l+(t+1)) :=
  ⟨l+j, by omega⟩

theorem powerPrefix_old {r l : ℕ} (p : Program r l) (omega : Fin l)
    (roots : Fin r → ℂ) (t : ℕ) (j : Fin l) :
    (powerPrefix p omega t).eval roots (j.castAdd (t+1)) = p.eval roots j := by
  induction t with
  | zero =>
      change Fin.snoc (α := fun _ => ℂ) (p.eval roots) _ j.castSucc = _
      exact Fin.snoc_castSucc _ _ j
  | succ t ih =>
      have hj : j.castAdd (t+1+1) = (j.castAdd (t+1)).castSucc := rfl
      rw [hj]
      simp only [powerPrefix, Program.eval, Fin.snoc_castSucc]
      exact ih

theorem powerPrefix_power {r l : ℕ} (p : Program r l) (omega : Fin l)
    (roots : Fin r → ℂ) (t j : ℕ) (hj : j ≤ t) :
    (powerPrefix p omega t).eval roots (powerRef j hj) =
      (p.eval roots omega)^j := by
  induction t generalizing j with
  | zero =>
      have h : j=0 := by omega
      subst j
      change Fin.snoc (α := fun _ => ℂ) (p.eval roots) _ (Fin.last l) = _
      simp [Instruction.eval]
  | succ t ih =>
      by_cases h : j=t+1
      · subst j
        have hr : powerRef (t+1) (le_refl _) = Fin.last (l+(t+1)) := by
          apply Fin.ext
          simp [powerRef]
        rw [hr]
        simp only [powerPrefix, Program.eval, Fin.snoc_last, Instruction.eval]
        rw [powerPrefix_old]
        have ht : Fin.last (l+t) = powerRef t (le_refl _) := by
          apply Fin.ext; simp [powerRef]
        rw [ht, ih t (le_refl _), pow_succ]
        ring
      · have hj' : j ≤ t := by omega
        have hr : powerRef (l:=l) j hj = (powerRef (l:=l) j hj').castSucc := rfl
        rw [hr]
        simp only [powerPrefix, Program.eval, Fin.snoc_castSucc]
        exact ih j hj'

theorem powerPrefix_admissible {r l : ℕ} (p : Program r l) (omega : Fin l)
    (roots : Fin r → ℂ) (hp : p.Admissible roots) (t : ℕ) :
    (powerPrefix p omega t).Admissible roots := by
  induction t with
  | zero => exact ⟨hp, trivial⟩
  | succ t ih => exact ⟨ih, trivial⟩

/-- Logical FFT operands are either retained kernel registers or already
emitted scalar FFT gates.  Fin proves every reference is prior. -/
def operand {l n t : ℕ} (input : Fin n → Fin l) (a : ℕ) (ha : a < n+t) :
    Fin (l+t) :=
  if h : a<n then (input ⟨a,h⟩).castAdd t else ⟨l+(a-n), by omega⟩

theorem operand_succ {l n t : ℕ} (input : Fin n → Fin l)
    (a : ℕ) (ha : a<n+t) :
    operand input a (by omega : a<n+(t+1)) = (operand input a ha).castSucc := by
  unfold operand; split_ifs <;> rfl

theorem operand_new {l n t : ℕ} (input : Fin n → Fin l) :
    operand input (n+t) (by omega : n+t<n+(t+1)) = Fin.last (l+t) := by
  apply Fin.ext
  simp [operand, show ¬n+t<n by omega]

def lowerOp {r l n t : ℕ} (input : Fin n → Fin l) (powers : Fin n → Fin l)
    (op : Op ℕ) (hr : ∀ a ∈ op.refs, a<n+t)
    (hc : ∀ c ∈ op.scalars, c<n) : Instruction r (l+t) :=
  match op with
  | .add a b => .add (operand input a (hr a (by simp [Op.refs])))
      (operand input b (hr b (by simp [Op.refs])))
  | .sub a b => .sub (operand input a (hr a (by simp [Op.refs])))
      (operand input b (hr b (by simp [Op.refs])))
  | .scale c a => .mul ((powers ⟨c,hc c (by simp [Op.scalars])⟩).castAdd t)
      (operand input a (hr a (by simp [Op.refs])))

def fftInstruction {r l : ℕ} (k : ℕ) (input powers : Fin (width k) → Fin l)
    (j : Fin (count k)) : Instruction r (l+j.val) :=
  lowerOp input powers (instruction k j) (printed_refs_before k j)
    (instruction_scalar_bound k j)

def fftPrefix {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) :
    (t : ℕ) → t≤count k → Program r (l+t)
  | 0, _ => p
  | t+1, ht => .step (fftPrefix k p input powers t (by omega))
      (fftInstruction k input powers ⟨t,by omega⟩)

theorem fftPrefix_old {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) (roots : Fin r → ℂ)
    (t : ℕ) (ht : t≤count k) (j : Fin l) :
    (fftPrefix k p input powers t ht).eval roots (j.castAdd t) = p.eval roots j := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hj : j.castAdd (t+1) = (j.castAdd t).castSucc := rfl
      rw [hj]
      simp only [fftPrefix, Program.eval, Fin.snoc_castSucc]
      exact ih (by omega)

theorem lowerOp_eval {r l n t : ℕ} (input powers : Fin n → Fin l)
    (op : Op ℕ) (hr : ∀ a ∈ op.refs, a<n+t) (hc : ∀ c ∈ op.scalars, c<n)
    (roots : Fin r → ℂ) (values : Fin (l+t) → ℂ)
    (bank data : ℕ → ℂ)
    (hp : ∀ c (h:c<n), values ((powers ⟨c,h⟩).castAdd t)=bank c)
    (hv : ∀ a (h:a<n+t), values (operand input a h)=data a) :
    (lowerOp input powers op hr hc : Instruction r (l+t)).eval roots values =
      op.evalBank bank data := by
  cases op <;> simp only [lowerOp, Instruction.eval, Op.evalBank, hp, hv]

theorem lowerOp_admissible {r l n t : ℕ} (input powers : Fin n → Fin l)
    (op : Op ℕ) (hr : ∀ a ∈ op.refs, a<n+t) (hc : ∀ c ∈ op.scalars, c<n)
    (values : Fin (l+t) → ℂ) :
    (lowerOp input powers op hr hc : Instruction r (l+t)).Admissible values := by
  cases op <;> trivial

theorem fftPrefix_values {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) (roots : Fin r → ℂ) (omega : ℂ)
    (hp : ∀ i, p.eval roots (powers i)=omega^i.val)
    (t : ℕ) (ht : t≤count k) (a : ℕ) (ha : a<width k+t) :
    (fftPrefix k p input powers t ht).eval roots (operand input a ha) =
      natValues k omega (fun i => p.eval roots (input i)) a := by
  induction t generalizing a with
  | zero =>
      simp only [Nat.add_zero] at ha
      simp [operand, ha, fftPrefix, natValues]
  | succ t ih =>
      by_cases hnew : a=width k+t
      · subst a
        rw [operand_new]
        simp only [fftPrefix, Program.eval, Fin.snoc_last]
        rw [fftInstruction]
        have he := lowerOp_eval input powers (instruction k ⟨t,by omega⟩)
          (printed_refs_before k ⟨t,by omega⟩)
          (instruction_scalar_bound k ⟨t,by omega⟩) roots
          ((fftPrefix k p input powers t (by omega)).eval roots)
          (preparedBank k omega) (natValues k omega (fun i => p.eval roots (input i)))
          (by intro c hc; rw [fftPrefix_old, hp, preparedBank_eq k omega c hc])
          (by intro b hb; exact ih (by omega) b hb)
        exact he.trans (printed_gate k omega (fun i => p.eval roots (input i))
          ⟨t,by omega⟩).symm
      · have ha' : a<width k+t := by omega
        rw [operand_succ input a ha']
        simp only [fftPrefix, Program.eval, Fin.snoc_castSucc]
        exact ih (by omega) a ha'

theorem fftPrefix_admissible {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) (t : ℕ) (ht : t≤count k) :
    (fftPrefix k p input powers t ht).Admissible roots := by
  induction t with
  | zero => exact hp
  | succ t ih =>
      refine ⟨ih (by omega), ?_⟩
      exact lowerOp_admissible input powers _ _ _ _

def fftOutput {l : ℕ} (k : ℕ) (input : Fin (width k) → Fin l)
    (i : Fin (width k)) : Fin (l+count k) :=
  operand input (refNat (output k i)) (refNat_bound (output k i))

theorem fftPrefix_output {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) (roots : Fin r → ℂ) (omega : ℂ)
    (hp : ∀ i, p.eval roots (powers i)=omega^i.val) (i : Fin (width k)) :
    (fftPrefix k p input powers (count k) (le_refl _)).eval roots
        (fftOutput k input i) = run k omega (fun i => p.eval roots (input i)) i := by
  rw [fftOutput, fftPrefix_values k p input powers roots omega hp]
  exact (runPrefix_correct k omega _ (count k) (le_refl _) _
    (refNat_bound (output k i))).symm

@[reducible] def manyLength (l c : ℕ) : ℕ → ℕ
  | 0 => l
  | b+1 => manyLength l c b+c

theorem manyLength_eq (l c b : ℕ) : manyLength l c b=l+b*c := by
  induction b with
  | zero => simp [manyLength]
  | succ b ih => simp only [manyLength, ih, Nat.succ_mul]; omega

def retained {l c : ℕ} (b : ℕ) (i : Fin l) : Fin (manyLength l c b) :=
  ⟨i.val, by rw [manyLength_eq]; have := i.isLt; omega⟩

theorem retained_succ {l c b : ℕ} (i : Fin l) :
    retained (c:=c) (b+1) i=(retained (c:=c) b i).castAdd c := rfl

def manyProgram {r l : ℕ} (k : ℕ) (p : Program r l)
    (powers : Fin (width k) → Fin l) :
    (b : ℕ) → (Fin b → Fin (width k) → Fin l) →
      Program r (manyLength l (count k) b)
  | 0, _ => p
  | b+1, kernels =>
      fftPrefix k (manyProgram k p powers b (fun j => kernels j.castSucc))
        (fun i => retained b (kernels (Fin.last b) i))
        (fun i => retained b (powers i)) (count k) (le_refl _)

def manyOutput {l : ℕ} (k : ℕ) :
    (b : ℕ) → (Fin b → Fin (width k) → Fin l) →
      Fin b → Fin (width k) → Fin (manyLength l (count k) b)
  | 0, _, i, _ => Fin.elim0 i
  | b+1, kernels, i, q =>
      Fin.lastCases
        (fftOutput k (fun i => retained b (kernels (Fin.last b) i)) q)
        (fun j => (manyOutput k b (fun i => kernels i.castSucc) j q).castAdd (count k)) i

theorem manyProgram_old {r l : ℕ} (k : ℕ) (p : Program r l)
    (powers : Fin (width k) → Fin l) (roots : Fin r → ℂ)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin l) (i : Fin l) :
    (manyProgram k p powers b kernels).eval roots (retained b i)=p.eval roots i := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [retained_succ]
      simp only [manyProgram, fftPrefix_old]
      exact ih _

theorem manyProgram_admissible {r l : ℕ} (k : ℕ) (p : Program r l)
    (powers : Fin (width k) → Fin l) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) (b : ℕ)
    (kernels : Fin b → Fin (width k) → Fin l) :
    (manyProgram k p powers b kernels).Admissible roots := by
  induction b with
  | zero => exact hp
  | succ b ih => exact fftPrefix_admissible k _ _ _ roots (ih _) _ _

theorem manyProgram_output {r l : ℕ} (k : ℕ) (p : Program r l)
    (powers : Fin (width k) → Fin l) (roots : Fin r → ℂ) (omega : ℂ)
    (hp : ∀ q, p.eval roots (powers q)=omega^q.val)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin l)
    (i : Fin b) (q : Fin (width k)) :
    (manyProgram k p powers b kernels).eval roots (manyOutput k b kernels i q)=
      run k omega (fun j => p.eval roots (kernels i j)) q := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [manyProgram, manyOutput, Fin.lastCases_last]
        rw [fftPrefix_output k _ _ _ roots omega
          (by intro j; rw [manyProgram_old, hp])]
        have he : (fun j => (manyProgram k p powers b (fun i => kernels i.castSucc)).eval
            roots (retained b (kernels (Fin.last b) j))) =
            fun j => p.eval roots (kernels (Fin.last b) j) := by
          funext j; exact manyProgram_old k p powers roots b _ _
        rw [he]
      · simp only [manyProgram, manyOutput, Fin.lastCases_castSucc, fftPrefix_old]
        exact ih (fun i => kernels i.castSucc) j

def prefixPowers {l : ℕ} (k : ℕ) (j : Fin (width k)) : Fin (l+(width k+1)) :=
  powerRef j.val (Nat.le_of_lt j.isLt)

def kernelPrefix {l : ℕ} (k : ℕ) {b : ℕ}
    (kernels : Fin b → Fin (width k) → Fin l) :
    Fin b → Fin (width k) → Fin (l+(width k+1)) :=
  fun i q => (kernels i q).castAdd (width k+1)

/-- The original program and one power prefix occur literally once. -/
def bankProgram {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length) :
    Program r (manyLength (d.length+(width k+1)) (count k) b) :=
  manyProgram k (powerPrefix d.program omega (width k)) (prefixPowers k) b
    (kernelPrefix k kernels)

def bank {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length) :
    DAG r (width k+b*width k) where
  length := manyLength (d.length+(width k+1)) (count k) b
  program := bankProgram k d omega b kernels
  output := Fin.addCases
    (fun q => retained b (prefixPowers k q))
    (fun q => let ij := (finProdFinEquiv : Fin b × Fin (width k) ≃ Fin (b*width k)).symm q
      manyOutput k b (kernelPrefix k kernels) ij.1 ij.2)

theorem bank_length {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length) :
    (bank k d omega b kernels).length=d.length+(width k+1)+b*count k :=
  manyLength_eq _ _ _

theorem bank_admissible {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) :
    (bank k d omega b kernels).Admissible roots :=
  manyProgram_admissible k _ _ roots (powerPrefix_admissible d.program omega roots hd _)
    b _

theorem bank_original {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length)
    (roots : Fin r → ℂ) (j : Fin d.length) :
    (bank k d omega b kernels).program.eval roots
        (retained b (j.castAdd (width k+1)))=d.program.eval roots j := by
  change (manyProgram k (powerPrefix d.program omega (width k)) (prefixPowers k) b
    (kernelPrefix k kernels)).eval roots (retained b (j.castAdd (width k+1))) = _
  rw [manyProgram_old, powerPrefix_old]

theorem bank_power {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (q : Fin (width k)) :
    (bank k d omega b kernels).run roots (bank_admissible k d omega b kernels roots hd)
      (q.castAdd (b*width k))=(d.program.eval roots omega)^q.val := by
  simp only [DAG.run, Program.run, bank, Fin.addCases_left, bankProgram]
  rw [manyProgram_old]
  exact powerPrefix_power d.program omega roots (width k) q.val (Nat.le_of_lt q.isLt)

theorem bank_spectrum {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (homega : d.program.eval roots omega=zeta (width k))
    (i : Fin b) (q : Fin (width k)) :
    (bank k d omega b kernels).run roots (bank_admissible k d omega b kernels roots hd)
        ((finProdFinEquiv (i,q)).natAdd (width k)) =
      Matrix.mulVec (fourierMatrix (width k)) (fun j => d.program.eval roots (kernels i j)) q := by
  simp only [DAG.run, Program.run, bank, Fin.addCases_right, Equiv.symm_apply_apply,
    bankProgram]
  rw [manyProgram_output k _ _ roots (zeta (width k))
    (by intro j; rw [prefixPowers, powerPrefix_power, homega])]
  have he : (fun j => (powerPrefix d.program omega (width k)).eval roots
      (kernelPrefix k kernels i j)) = fun j => d.program.eval roots (kernels i j) := by
    funext j; exact powerPrefix_old d.program omega roots (width k) _
  rw [he, run_specified]

def convolutionBank {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernel : Fin (width k) → Fin d.length) : DAG r (width k+width k) where
  length := (bank k d omega 1 (fun _ => kernel)).length
  program := (bank k d omega 1 (fun _ => kernel)).program
  output := Fin.addCases (fun q => retained 1 (prefixPowers k q))
    (fun q => manyOutput k 1 (kernelPrefix k (fun _ => kernel)) 0 q)

theorem convolutionBank_length {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernel : Fin (width k) → Fin d.length) :
    (convolutionBank k d omega kernel).length=d.length+(width k+1)+count k := by
  exact (bank_length k d omega 1 (fun _ => kernel)).trans (by simp)

theorem convolutionBank_admissible {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernel : Fin (width k) → Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : (convolutionBank k d omega kernel).Admissible roots :=
  bank_admissible k d omega 1 (fun _ => kernel) roots hd

/-- Literal scalar preparation equals the exact bank used by convolution. -/
theorem convolutionBank_run {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernel : Fin (width k) → Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (homega : d.program.eval roots omega=zeta (width k)) :
    (convolutionBank k d omega kernel).run roots
      (convolutionBank_admissible k d omega kernel roots hd)=
      UniformConvolutionDAG.coefficientBank k (fun j => d.program.eval roots (kernel j)) := by
  funext i
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · simp only [DAG.run, Program.run, convolutionBank, Fin.addCases_left,
      bank, bankProgram, UniformConvolutionDAG.coefficientBank, Fin.addCases_left]
    rw [manyProgram_old, prefixPowers, powerPrefix_power, homega]
  · simp only [DAG.run, Program.run, convolutionBank, Fin.addCases_right,
      bank, bankProgram, UniformConvolutionDAG.coefficientBank, Fin.addCases_right]
    rw [manyProgram_output k _ _ roots (zeta (width k))
      (by intro j; rw [prefixPowers, powerPrefix_power, homega])]
    have he : (fun j => (powerPrefix d.program omega (width k)).eval roots
        (kernelPrefix k (fun _ : Fin 1 => kernel) 0 j)) =
        fun j => d.program.eval roots (kernel j) := by
      funext j; exact powerPrefix_old d.program omega roots (width k) _
    rw [he, run_specified]

def crossBank {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) :
    DAG r (UniformToeplitzCrossDAG.bankSize k) := bank k d omega 6 kernels

theorem crossBank_length {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) :
    (crossBank k d omega kernels).length=d.length+(width k+1)+6*count k :=
  bank_length k d omega 6 kernels

theorem crossBank_admissible {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : (crossBank k d omega kernels).Admissible roots :=
  bank_admissible k d omega 6 kernels roots hd

/-- Six spectra share both the original program and the single power prefix. -/
theorem crossBank_run {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (homega : d.program.eval roots omega=zeta (width k)) :
    (crossBank k d omega kernels).run roots
      (crossBank_admissible k d omega kernels roots hd)=
      UniformToeplitzCrossDAG.sharedBank k
        (fun b j => d.program.eval roots (kernels b j)) := by
  funext i
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · exact (bank_power k d omega 6 kernels roots hd q).trans (by
      simp only [homega, UniformToeplitzCrossDAG.sharedBank, Fin.addCases_left])
  · let ij := (finProdFinEquiv : Fin 6 × Fin (width k) ≃ Fin (6*width k)).symm q
    have hi : finProdFinEquiv ij=q := Equiv.apply_symm_apply _ q
    rw [← hi]
    simpa only [crossBank, UniformToeplitzCrossDAG.sharedBank, Fin.addCases_right,
      Equiv.symm_apply_apply] using
      bank_spectrum k d omega 6 kernels roots hd homega ij.1 ij.2

end ExactFourierCircuits.UniformKernelSpectrumPreparation
namespace ExactFourierCircuits.UniformScalarPreparation

def Instruction.rootReads {r t : ℕ} : Instruction r t → ℕ
  | .root _ => 1
  | _ => 0

def Instruction.divisions {r t : ℕ} : Instruction r t → ℕ
  | .divide _ _ => 1
  | _ => 0

def Program.rootReads {r : ℕ} : {t : ℕ} → Program r t → ℕ
  | _, .nil => 0
  | _, .step p i => p.rootReads+i.rootReads

def Program.divisions {r : ℕ} : {t : ℕ} → Program r t → ℕ
  | _, .nil => 0
  | _, .step p i => p.divisions+i.divisions

end ExactFourierCircuits.UniformScalarPreparation
namespace ExactFourierCircuits.UniformKernelSpectrumPreparation
open UniformScalarPreparation UniformRadixTwoDAG
open OAI.ExactFourier (zeta)

theorem powerPrefix_counts {r l : ℕ} (p : Program r l) (omega : Fin l) (t : ℕ) :
    (powerPrefix p omega t).rootReads=p.rootReads ∧
      (powerPrefix p omega t).divisions=p.divisions := by
  induction t with
  | zero => simp [powerPrefix, Program.rootReads, Program.divisions,
      Instruction.rootReads, Instruction.divisions]
  | succ t ih => simpa only [powerPrefix, Program.rootReads, Program.divisions,
      Instruction.rootReads, Instruction.divisions, Nat.add_zero] using ih

theorem lowerOp_counts {r l n t : ℕ} (input powers : Fin n → Fin l)
    (op : Op ℕ) (hr : ∀ a ∈ op.refs, a<n+t) (hc : ∀ c ∈ op.scalars, c<n) :
    (lowerOp input powers op hr hc : Instruction r (l+t)).rootReads=0 ∧
      (lowerOp input powers op hr hc : Instruction r (l+t)).divisions=0 := by
  cases op <;> exact ⟨rfl,rfl⟩

theorem fftPrefix_counts {r l : ℕ} (k : ℕ) (p : Program r l)
    (input powers : Fin (width k) → Fin l) (t : ℕ) (ht : t≤count k) :
    (fftPrefix k p input powers t ht).rootReads=p.rootReads ∧
      (fftPrefix k p input powers t ht).divisions=p.divisions := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih =>
      have hc := lowerOp_counts (r:=r) (t:=t) input powers (instruction k ⟨t,by omega⟩)
        (printed_refs_before k ⟨t,by omega⟩) (instruction_scalar_bound k ⟨t,by omega⟩)
      simpa only [fftPrefix, Program.rootReads, Program.divisions, fftInstruction,
        hc.1, hc.2, Nat.add_zero] using ih (by omega)

theorem manyProgram_counts {r l : ℕ} (k : ℕ) (p : Program r l)
    (powers : Fin (width k) → Fin l) (b : ℕ)
    (kernels : Fin b → Fin (width k) → Fin l) :
    (manyProgram k p powers b kernels).rootReads=p.rootReads ∧
      (manyProgram k p powers b kernels).divisions=p.divisions := by
  induction b with
  | zero => exact ⟨rfl,rfl⟩
  | succ b ih =>
      have hc := fftPrefix_counts k
        (manyProgram k p powers b (fun j => kernels j.castSucc))
        (fun i => retained b (kernels (Fin.last b) i))
        (fun i => retained b (powers i)) (count k) (le_refl _)
      exact ⟨hc.1.trans (ih _).1,hc.2.trans (ih _).2⟩

theorem bank_counts {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (b : ℕ) (kernels : Fin b → Fin (width k) → Fin d.length) :
    (bank k d omega b kernels).program.rootReads=d.program.rootReads ∧
      (bank k d omega b kernels).program.divisions=d.program.divisions := by
  have hc := manyProgram_counts k (powerPrefix d.program omega (width k))
    (prefixPowers k) b (kernelPrefix k kernels)
  have hp := powerPrefix_counts d.program omega (width k)
  exact ⟨hc.1.trans hp.1,hc.2.trans hp.2⟩

theorem convolutionBank_counts {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernel : Fin (width k) → Fin d.length) :
    (convolutionBank k d omega kernel).program.rootReads=d.program.rootReads ∧
      (convolutionBank k d omega kernel).program.divisions=d.program.divisions :=
  bank_counts k d omega 1 (fun _ => kernel)

theorem crossBank_counts {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) :
    (crossBank k d omega kernels).program.rootReads=d.program.rootReads ∧
      (crossBank k d omega kernels).program.divisions=d.program.divisions :=
  bank_counts k d omega 6 kernels

theorem crossBank_length_closed {r a : ℕ} (k : ℕ) (d : DAG r a) (omega : Fin d.length)
    (kernels : Fin 6 → Fin (width k) → Fin d.length) :
    (crossBank k d omega kernels).length=d.length+(2^k+1)+9*k*2^k := by
  rw [crossBank_length]
  have hc := count_exact k
  have he : 6*count k=9*k*width k := by nlinarith
  rw [he, width_eq]

/-- Each branch sees the bank expected by its actual convolution compiler. -/
theorem crossBank_kernel_restriction {r a : ℕ} (k : ℕ) (d : DAG r a)
    (omega : Fin d.length) (kernels : Fin 6 → Fin (width k) → Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (homega : d.program.eval roots omega=zeta (width k)) (b : Fin 6) :
    (crossBank k d omega kernels).run roots
        (crossBank_admissible k d omega kernels roots hd) ∘
      UniformToeplitzCrossDAG.coefficientEmbedding k b =
      UniformConvolutionDAG.coefficientBank k (fun j => d.program.eval roots (kernels b j)) := by
  rw [crossBank_run k d omega kernels roots hd homega]
  exact UniformToeplitzCrossDAG.sharedBank_embedding k _ b

/-- Existing prepared output references can supply a kernel without copying
the preparation DAG or expanding its expressions. -/
def outputKernels {r a b : ℕ} (k : ℕ) (d : DAG r a)
    (indices : Fin b → Fin (width k) → Fin a) :
    Fin b → Fin (width k) → Fin d.length := fun i q => d.output (indices i q)

theorem outputKernels_values {r a b : ℕ} (k : ℕ) (d : DAG r a)
    (indices : Fin b → Fin (width k) → Fin a) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (i : Fin b) (q : Fin (width k)) :
    d.program.eval roots (outputKernels k d indices i q)=d.run roots hd (indices i q) := rfl

end ExactFourierCircuits.UniformKernelSpectrumPreparation
