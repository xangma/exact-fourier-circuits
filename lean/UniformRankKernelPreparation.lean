import UniformKernelSpectrumPreparation
import UniformReciprocalPreparation

/-! Actual shared scalar-DAG production of the six displacement kernels.
Only the newly needed borders are expanded. Existing coefficient preparation
is retained once, and every operand is a prior register. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRankKernelPreparation
open scoped BigOperators
open UniformScalarPreparation

/-- New border expressions can only read the retained coefficient bank. -/
inductive Expr (l : ℕ) where
  | ref (i : Fin l)
  | add (x y : Expr l)
  | sub (x y : Expr l)
  | mul (x y : Expr l)

namespace Expr

def work {l : ℕ} : Expr l → ℕ
  | .ref _ => 0
  | .add x y | .sub x y | .mul x y => x.work+y.work+1

noncomputable def eval {l : ℕ} (values : Fin l → ℂ) : Expr l → ℂ
  | .ref i => values i
  | .add x y => x.eval values+y.eval values
  | .sub x y => x.eval values-y.eval values
  | .mul x y => x.eval values*y.eval values

end Expr

structure Result (r k : ℕ) where
  length : ℕ
  program : Program r length
  old : Fin k → Fin length
  output : Fin length

namespace Expr

/-- Each operation appends one instruction to the already compiled history. -/
def compile {r k l : ℕ} (p : Program r k) (input : Fin l → Fin k) : Expr l → Result r k
  | .ref i => ⟨k,p,id,input i⟩
  | .add x y =>
    let a := x.compile p input
    let b := y.compile a.program (fun i => a.old (input i))
    ⟨b.length+1,.step b.program (.add (b.old a.output) b.output),
      fun i => (b.old (a.old i)).castSucc,Fin.last b.length⟩
  | .sub x y =>
    let a := x.compile p input
    let b := y.compile a.program (fun i => a.old (input i))
    ⟨b.length+1,.step b.program (.sub (b.old a.output) b.output),
      fun i => (b.old (a.old i)).castSucc,Fin.last b.length⟩
  | .mul x y =>
    let a := x.compile p input
    let b := y.compile a.program (fun i => a.old (input i))
    ⟨b.length+1,.step b.program (.mul (b.old a.output) b.output),
      fun i => (b.old (a.old i)).castSucc,Fin.last b.length⟩

theorem compile_length {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) :
    (e.compile p input).length=k+e.work := by
  induction e generalizing k with
  | ref i => rfl
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      simp only [compile,work,hy,hx]
      omega

theorem compile_old_val {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (i : Fin k) :
    ((e.compile p input).old i).val=i.val := by
  induction e generalizing k with
  | ref j => rfl
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      simp only [compile,Fin.val_castSucc,hy,hx]

theorem compile_old {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ) (i : Fin k) :
    (e.compile p input).program.eval roots ((e.compile p input).old i)=p.eval roots i := by
  induction e generalizing k with
  | ref j => rfl
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      simp only [compile,Program.eval,Fin.snoc_castSucc,hy,hx]

theorem compile_output {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ) :
    (e.compile p input).program.eval roots (e.compile p input).output=
      e.eval (fun i => p.eval roots (input i)) := by
  induction e generalizing k with
  | ref i => rfl
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      simp only [compile,Program.eval,Fin.snoc_last,Instruction.eval,eval,
        compile_old,hx,hy]

theorem compile_admissible {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) : (e.compile p input).program.Admissible roots := by
  induction e generalizing k with
  | ref i => exact hp
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      exact ⟨hy _ _ (hx _ _ hp),trivial⟩

theorem compile_counts {l : ℕ} (e : Expr l) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) :
    (e.compile p input).program.rootReads=p.rootReads ∧
      (e.compile p input).program.divisions=p.divisions := by
  induction e generalizing k with
  | ref i => exact ⟨rfl,rfl⟩
  | add x y hx hy | sub x y hx hy | mul x y hx hy =>
      have a := hx p input
      have b := hy (x.compile p input).program (fun i => (x.compile p input).old (input i))
      simp only [compile,Program.rootReads,Program.divisions,Instruction.rootReads,
        Instruction.divisions,Nat.add_zero]
      exact ⟨b.1.trans a.1,b.2.trans a.2⟩

end Expr

structure Forest (r k : ℕ) where
  length : ℕ
  program : Program r length
  old : Fin k → Fin length
  outputs : List (Fin length)

/-- The input program is not copied between different kernel outputs. -/
def compileList {r k l : ℕ} (p : Program r k) (input : Fin l → Fin k) :
    List (Expr l) → Forest r k
  | [] => ⟨k,p,id,[]⟩
  | e::es =>
    let a := e.compile p input
    let b := compileList a.program (fun i => a.old (input i)) es
    ⟨b.length,b.program,fun i => b.old (a.old i),b.old a.output::b.outputs⟩

theorem compileList_length {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) :
    (compileList p input es).length=k+(es.map Expr.work).sum := by
  induction es generalizing k with
  | nil => simp [compileList]
  | cons e es ih => simp only [compileList,ih,Expr.compile_length,List.map_cons,List.sum_cons]; omega

@[simp] theorem compileList_outputs_length {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) :
    (compileList p input es).outputs.length=es.length := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [compileList,List.length_cons,ih]

theorem compileList_old_val {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (i : Fin k) :
    ((compileList p input es).old i).val=i.val := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [compileList,ih,Expr.compile_old_val]

theorem compileList_old {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ) (i : Fin k) :
    (compileList p input es).program.eval roots ((compileList p input es).old i)=p.eval roots i := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [compileList,ih,Expr.compile_old]

theorem compileList_outputs {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ) :
    (compileList p input es).outputs.map ((compileList p input es).program.eval roots)=
      es.map (Expr.eval (fun i => p.eval roots (input i))) := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
      simp only [compileList,List.map_cons,compileList_old,Expr.compile_output,ih,Expr.compile_old]

theorem compileList_admissible {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) : (compileList p input es).program.Admissible roots := by
  induction es generalizing k with
  | nil => exact hp
  | cons e es ih => exact ih _ _ (e.compile_admissible p input roots hp)

theorem compileList_counts {l : ℕ} (es : List (Expr l)) {r k : ℕ}
    (p : Program r k) (input : Fin l → Fin k) :
    (compileList p input es).program.rootReads=p.rootReads ∧
      (compileList p input es).program.divisions=p.divisions := by
  induction es generalizing k with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
      have a := e.compile_counts p input
      have b := ih (e.compile p input).program (fun i => (e.compile p input).old (input i))
      exact ⟨b.1.trans a.1,b.2.trans a.2⟩

def family {r k l b : ℕ} (p : Program r k) (input : Fin l → Fin k)
    (es : Fin b → Expr l) : DAG r b :=
  let f := compileList p input (List.ofFn es)
  ⟨f.length,f.program,fun i => f.outputs[i.val]'(by
    rw [compileList_outputs_length,List.length_ofFn]; exact i.isLt)⟩

theorem family_output {r k l b : ℕ} (p : Program r k) (input : Fin l → Fin k)
    (es : Fin b → Expr l) (roots : Fin r → ℂ) (i : Fin b) :
    (family p input es).program.eval roots ((family p input es).output i)=
      (es i).eval (fun j => p.eval roots (input j)) := by
  have h := congrArg (fun xs : List ℂ => xs[i.val]?)
    (compileList_outputs (List.ofFn es) p input roots)
  have hb : i.val<(compileList p input (List.ofFn es)).outputs.length := by
    rw [compileList_outputs_length,List.length_ofFn]; exact i.isLt
  simp [List.map_ofFn, i.isLt] at h
  exact h

def initialProgram {r l : ℕ} (p : Program r l) : Program r (l+2) :=
  .step (.step p (.rational 0)) (.rational 1)

def zeroRef (l : ℕ) : Fin (l+2) := (Fin.last l).castSucc
def oneRef (l : ℕ) : Fin (l+2) := Fin.last (l+1)

@[simp] theorem initial_old {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ) (j : Fin l) :
    (initialProgram p).eval roots (j.castAdd 2)=p.eval roots j := by
  change Fin.snoc (α := fun _ => ℂ) (Fin.snoc (α := fun _ => ℂ) (p.eval roots) _) _ j.castSucc.castSucc=_
  simp

@[simp] theorem initial_zero {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ) :
    (initialProgram p).eval roots (zeroRef l)=0 := by simp [initialProgram,zeroRef,Instruction.eval]

@[simp] theorem initial_one {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ) :
    (initialProgram p).eval roots (oneRef l)=1 := by simp [initialProgram,oneRef,Instruction.eval]

theorem initial_admissible {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) : (initialProgram p).Admissible roots := ⟨⟨hp,trivial⟩,trivial⟩

theorem initial_counts {r l : ℕ} (p : Program r l) :
    (initialProgram p).rootReads=p.rootReads ∧ (initialProgram p).divisions=p.divisions := by
  simp [initialProgram,Program.rootReads,Program.divisions,Instruction.rootReads,Instruction.divisions]

def sumExpr {l : ℕ} (zero : Fin l) : List (Expr l) → Expr l
  | [] => .ref zero
  | x::xs => .add x (sumExpr zero xs)

theorem sumExpr_work {l : ℕ} (zero : Fin l) (es : List (Expr l)) :
    (sumExpr zero es).work=(es.map Expr.work).sum+es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [sumExpr,Expr.work,ih,List.map_cons,List.sum_cons,List.length_cons]; omega

theorem sumExpr_eval {l : ℕ} (zero : Fin l) (es : List (Expr l)) (values : Fin l → ℂ) :
    (sumExpr zero es).eval values=(es.map (Expr.eval values)).sum+values zero := by
  induction es with
  | nil => simp [sumExpr,Expr.eval]
  | cons e es ih => simp only [sumExpr,Expr.eval,ih,List.map_cons,List.sum_cons,add_assoc]

/-- All required coefficient references are supplied by the original DAG.
The bounds are sufficient for every border term; there is no host scalar oracle. -/
structure Sources (l a e : ℕ) where
  hSize : ℕ
  gSize : ℕ
  h : Fin hSize → Fin l
  g : Fin gSize → Fin l
  s : ℕ
  i₀ : ℕ
  j₀ : ℕ
  positive : 0<a
  hBound : i₀+a≤hSize
  gBound : s<gSize

namespace Sources

def hExpr {l a e : ℕ} (c : Sources l a e) (i : ℕ) (hi : i<c.hSize) : Expr (l+2) :=
  .ref ((c.h ⟨i,hi⟩).castAdd 2)

def gExpr {l a e : ℕ} (c : Sources l a e) (i : ℕ) (hi : i<c.gSize) : Expr (l+2) :=
  .ref ((c.g ⟨i,hi⟩).castAdd 2)

/-- Literal multiplication/addition nodes for the finite Toeplitz border sum. -/
def crossExpr {l a e : ℕ} (c : Sources l a e) (i j : ℕ) (hi : i<c.hSize) : Expr (l+2) :=
  sumExpr (zeroRef l) (List.ofFn (fun u : Fin (c.s-j) =>
    Expr.mul (c.hExpr (i-j-u.val) (by omega))
      (c.gExpr u.val (by have := u.isLt; have := c.gBound; omega))))

def vExpr {l a e : ℕ} (c : Sources l a e) (i : Fin a) : Expr (l+2) :=
  .sub (.ref (zeroRef l)) (c.hExpr (c.i₀+i.val-c.s) (by
    have := i.isLt; have := c.hBound; omega))

def wExpr {l a e : ℕ} (c : Sources l a e) (j : Fin e) : Expr (l+2) :=
  c.gExpr (c.s-(c.j₀+j.val)) (by have := c.gBound; omega)

def rowExpr {l a e : ℕ} (c : Sources l a e) (j : Fin e) : Expr (l+2) :=
  .sub (c.crossExpr c.i₀ (c.j₀+j.val) (by have := c.positive; have := c.hBound; omega))
    (.mul (c.vExpr ⟨0,c.positive⟩) (c.wExpr j))

def colExpr {l a e : ℕ} (c : Sources l a e) (i : Fin a) : Expr (l+2) :=
  if i.val=0 then .ref (zeroRef l) else
  .sub (c.crossExpr (c.i₀+i.val) c.j₀ (by have := c.hBound; have := i.isLt; omega))
    (.mul (c.vExpr i) (c.gExpr (c.s-c.j₀) (by have := c.gBound; omega)))

def deltaExpr (l j : ℕ) : Expr (l+2) := if j=0 then .ref (oneRef l) else .ref (zeroRef l)

def padExpr {l n N : ℕ} (f : Fin n → Expr (l+2)) (j : Fin N) : Expr (l+2) :=
  if h : j.val<n then f ⟨j.val,h⟩ else .ref (zeroRef l)

/-- Frozen slot order: w,v,row,delta,delta,col. Padding uses the shared zero. -/
def kernelExpr {l a e : ℕ} (k : ℕ) (c : Sources l a e)
    (slot : Fin 6) (j : Fin (UniformRadixTwoDAG.width k)) : Expr (l+2) :=
  if slot.val=0 then padExpr c.wExpr j else
  if slot.val=1 then padExpr c.vExpr j else
  if slot.val=2 then padExpr c.rowExpr j else
  if slot.val=3 then padExpr (fun i : Fin a => deltaExpr l i.val) j else
  if slot.val=4 then padExpr (fun i : Fin e => deltaExpr l i.val) j else
    padExpr c.colExpr j

theorem crossExpr_work {l a e : ℕ} (c : Sources l a e) (i j : ℕ) (hi : i<c.hSize) :
    (c.crossExpr i j hi).work=2*(c.s-j) := by
  simp [crossExpr,sumExpr_work,List.map_ofFn,List.sum_ofFn,Expr.work,hExpr,gExpr]
  omega

theorem kernelExpr_work {l a e : ℕ} (k : ℕ) (c : Sources l a e)
    (slot : Fin 6) (j : Fin (UniformRadixTwoDAG.width k)) :
    (kernelExpr k c slot j).work≤2*c.s+3 := by
  have row (i : Fin e) : (c.rowExpr i).work≤2*c.s+3 := by
    simp only [rowExpr,Expr.work,crossExpr_work,vExpr,wExpr,hExpr,gExpr]
    omega
  have col (i : Fin a) : (c.colExpr i).work≤2*c.s+3 := by
    unfold colExpr; split_ifs
    · simp [Expr.work]
    · simp only [Expr.work,crossExpr_work,vExpr,hExpr,gExpr]; omega
  have v (i : Fin a) : (c.vExpr i).work≤2*c.s+3 := by simp [vExpr,hExpr,Expr.work]
  have w (i : Fin e) : (c.wExpr i).work≤2*c.s+3 := by simp [wExpr,gExpr,Expr.work]
  have delta (i : ℕ) : (deltaExpr l i).work≤2*c.s+3 := by
    unfold deltaExpr; split_ifs <;> simp [Expr.work]
  unfold kernelExpr padExpr
  split_ifs <;> first | exact row _ | exact col _ | exact v _ | exact w _ | exact delta _ | simp [Expr.work]

def matrix {l a e : ℕ} (c : Sources l a e) (h g : ℕ → ℂ) (i j : ℕ) : ℂ :=
  OAI.ExactFourier.ToeplitzLayers.cross c.s h g (c.i₀+i) (c.j₀+j)

def left {l a e : ℕ} (c : Sources l a e) (h : ℕ → ℂ) (i : ℕ) : ℂ := -h (c.i₀+i-c.s)
def right {l a e : ℕ} (c : Sources l a e) (g : ℕ → ℂ) (j : ℕ) : ℂ := g (c.s-(c.j₀+j))

theorem crossExpr_eval {r l a e : ℕ} (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hh : ∀ i, p.eval roots (c.h i)=h i.val)
    (hg : ∀ i, p.eval roots (c.g i)=g i.val)
    (i j : ℕ) (hi : i<c.hSize) :
    (c.crossExpr i j hi).eval ((initialProgram p).eval roots)=
      OAI.ExactFourier.ToeplitzLayers.cross c.s h g i j := by
  rw [crossExpr,sumExpr_eval,List.map_ofFn,List.sum_ofFn,initial_zero,add_zero]
  simp only [Function.comp_apply,Expr.eval,hExpr,gExpr,initial_old,hh,hg]
  exact Fin.sum_univ_eq_sum_range (fun u => h (i-j-u)*g u) (c.s-j)

theorem vExpr_eval {r l a e : ℕ} (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (h : ℕ → ℂ)
    (hh : ∀ i, p.eval roots (c.h i)=h i.val) (i : Fin a) :
    (c.vExpr i).eval ((initialProgram p).eval roots)=c.left h i.val := by
  simp [vExpr,Expr.eval,hExpr,hh,left]

theorem wExpr_eval {r l a e : ℕ} (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (g : ℕ → ℂ)
    (hg : ∀ i, p.eval roots (c.g i)=g i.val) (j : Fin e) :
    (c.wExpr j).eval ((initialProgram p).eval roots)=c.right g j.val := by
  simp [wExpr,gExpr,Expr.eval,hg,right]

theorem rowExpr_eval {r l a e : ℕ} (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hh : ∀ i, p.eval roots (c.h i)=h i.val)
    (hg : ∀ i, p.eval roots (c.g i)=g i.val) (j : Fin e) :
    (c.rowExpr j).eval ((initialProgram p).eval roots)=
      c.matrix h g 0 j.val-c.left h 0*c.right g j.val := by
  simp only [rowExpr,Expr.eval,crossExpr_eval c p roots h g hh hg,
    vExpr_eval c p roots h hh,wExpr_eval c p roots g hg,matrix,Nat.add_zero]

theorem colExpr_eval {r l a e : ℕ} (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hh : ∀ i, p.eval roots (c.h i)=h i.val)
    (hg : ∀ i, p.eval roots (c.g i)=g i.val) (i : Fin a) :
    (c.colExpr i).eval ((initialProgram p).eval roots)=
      if i.val=0 then 0 else c.matrix h g i.val 0-c.left h i.val*c.right g 0 := by
  unfold colExpr; split_ifs with hi
  · simp [Expr.eval]
  · simp only [Expr.eval,crossExpr_eval c p roots h g hh hg,
      vExpr_eval c p roots h hh,gExpr,initial_old,hg,matrix,right,Nat.add_zero]

theorem deltaExpr_eval {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ) (i : ℕ) :
    (deltaExpr l i).eval ((initialProgram p).eval roots)=OAI.ExactFourier.Displacement.delta i := by
  unfold deltaExpr OAI.ExactFourier.Displacement.delta
  split_ifs <;> simp [Expr.eval]

theorem padExpr_eval {r l n k : ℕ} (p : Program r l) (roots : Fin r → ℂ)
    (f : Fin n → Expr (l+2)) (j : Fin (UniformRadixTwoDAG.width k)) :
    (padExpr f j).eval ((initialProgram p).eval roots)=
      UniformConvolutionDAG.inputVector k n (UniformConvolutionDAG.padInputs k n)
        (fun i => (f i).eval ((initialProgram p).eval roots)) j := by
  unfold padExpr UniformConvolutionDAG.inputVector UniformConvolutionDAG.padInputs
  split_ifs with hj
  · simp [Fin.snoc,hj]
  · simp [Expr.eval]

/-- The concrete border arithmetic, not an assigned semantic bank, yields the
six kernels used by the frozen cross DAG. -/
theorem kernelExpr_eval {r l a e : ℕ} (k : ℕ) (c : Sources l a e) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hh : ∀ i, p.eval roots (c.h i)=h i.val)
    (hg : ∀ i, p.eval roots (c.g i)=g i.val)
    (slot : Fin 6) (j : Fin (UniformRadixTwoDAG.width k)) :
    (kernelExpr k c slot j).eval ((initialProgram p).eval roots)=
      UniformToeplitzCrossDAG.rankKernels k a e (c.matrix h g) (c.left h) (c.right g) slot j := by
  fin_cases slot <;>
    simp [kernelExpr,padExpr_eval,UniformToeplitzCrossDAG.rankKernels,
      UniformToeplitzCrossDAG.leftFactor,UniformToeplitzCrossDAG.rightFactor,
      vExpr_eval c p roots h hh,wExpr_eval c p roots g hg,
      rowExpr_eval c p roots h g hh hg,colExpr_eval c p roots h g hh hg,
      deltaExpr_eval]

end Sources

def flatExpr {l a e : ℕ} (k : ℕ) (c : Sources l a e)
    (i : Fin (6*UniformRadixTwoDAG.width k)) : Expr (l+2) :=
  let ij := (finProdFinEquiv : Fin 6 × Fin (UniformRadixTwoDAG.width k) ≃
    Fin (6*UniformRadixTwoDAG.width k)).symm i
  Sources.kernelExpr k c ij.1 ij.2

/-- One copy of `d.program`, two rational literals, then all finite borders. -/
def prepared {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e) :
    DAG r (6*UniformRadixTwoDAG.width k) :=
  family (initialProgram d.program) id (flatExpr k c)

def retained {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (i : Fin d.length) : Fin (prepared k d c).length :=
  (compileList (initialProgram d.program) id (List.ofFn (flatExpr k c))).old (i.castAdd 2)

def kernelRef {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (slot : Fin 6) (j : Fin (UniformRadixTwoDAG.width k)) : Fin (prepared k d c).length :=
  (prepared k d c).output (finProdFinEquiv (slot,j))

theorem retained_val {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (i : Fin d.length) : (retained k d c i).val=i.val := by
  exact compileList_old_val _ _ _ _

/-- Every original reference, including omega, is retained at its old address. -/
theorem prepared_old {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (roots : Fin r → ℂ) (i : Fin d.length) :
    (prepared k d c).program.eval roots (retained k d c i)=d.program.eval roots i := by
  exact (compileList_old _ _ _ roots _).trans (initial_old d.program roots i)

theorem prepared_kernel {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hh : ∀ i, d.program.eval roots (c.h i)=h i.val)
    (hg : ∀ i, d.program.eval roots (c.g i)=g i.val)
    (slot : Fin 6) (j : Fin (UniformRadixTwoDAG.width k)) :
    (prepared k d c).program.eval roots (kernelRef k d c slot j)=
      UniformToeplitzCrossDAG.rankKernels k a e (c.matrix h g) (c.left h) (c.right g) slot j := by
  rw [kernelRef,prepared,family_output]
  simpa only [flatExpr,Equiv.symm_apply_apply,id_eq] using
    Sources.kernelExpr_eval k c d.program roots h g hh hg slot j

theorem prepared_admissible {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) : (prepared k d c).Admissible roots :=
  compileList_admissible _ _ _ roots (initial_admissible d.program roots hd)

theorem prepared_counts {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e) :
    (prepared k d c).program.rootReads=d.program.rootReads ∧
      (prepared k d c).program.divisions=d.program.divisions := by
  have h := compileList_counts (List.ofFn (flatExpr k c)) (initialProgram d.program) id
  have hi := initial_counts d.program
  exact ⟨h.1.trans hi.1,h.2.trans hi.2⟩

theorem prepared_length {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e) :
    (prepared k d c).length=d.length+2+
      ∑ i : Fin (6*UniformRadixTwoDAG.width k), (flatExpr k c i).work := by
  change (compileList (initialProgram d.program) id (List.ofFn (flatExpr k c))).length=_
  rw [compileList_length,List.map_ofFn,List.sum_ofFn]
  rfl

theorem prepared_length_bound {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e) :
    (prepared k d c).length≤d.length+2+6*UniformRadixTwoDAG.width k*(2*c.s+3) := by
  rw [prepared_length]
  have h : (∑ i : Fin (6*UniformRadixTwoDAG.width k), (flatExpr k c i).work)≤
      ∑ _i : Fin (6*UniformRadixTwoDAG.width k), (2*c.s+3) := by
    apply Finset.sum_le_sum
    intro i _
    exact Sources.kernelExpr_work _ _ _ _
  exact Nat.add_le_add_left (by simpa using h) _

/-- The existing spectrum compiler now reads actual assembled kernel registers. -/
def spectrumBank {r o a e : ℕ} (k : ℕ) (d : DAG r o) (c : Sources d.length a e)
    (omega : Fin d.length) : DAG r (UniformToeplitzCrossDAG.bankSize k) :=
  UniformKernelSpectrumPreparation.crossBank k (prepared k d c) (retained k d c omega)
    (kernelRef k d c)

theorem spectrumBank_admissible {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : (spectrumBank k d c omega).Admissible roots :=
  UniformKernelSpectrumPreparation.crossBank_admissible _ _ _ _ roots
    (prepared_admissible k d c roots hd)

/-- Actual code produces the shared bank consumed by the exact cross compiler.
The only scalar facts assumed are values of existing h/g/root registers. -/
theorem spectrumBank_run {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (h g : ℕ → ℂ)
    (hh : ∀ i, d.program.eval roots (c.h i)=h i.val)
    (hg : ∀ i, d.program.eval roots (c.g i)=g i.val)
    (homega : d.program.eval roots omega=OAI.ExactFourier.zeta (UniformRadixTwoDAG.width k)) :
    (spectrumBank k d c omega).run roots (spectrumBank_admissible k d c omega roots hd)=
      UniformToeplitzCrossDAG.sharedBank k
        (UniformToeplitzCrossDAG.rankKernels k a e (c.matrix h g) (c.left h) (c.right g)) := by
  change (UniformKernelSpectrumPreparation.crossBank k (prepared k d c)
    (retained k d c omega) (kernelRef k d c)).run roots _=_
  rw [UniformKernelSpectrumPreparation.crossBank_run k (prepared k d c)
    (retained k d c omega) (kernelRef k d c) roots (prepared_admissible k d c roots hd)
    ((prepared_old k d c roots omega).trans homega)]
  congr 1
  funext b j
  exact prepared_kernel k d c roots h g hh hg b j

theorem spectrumBank_counts {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) :
    (spectrumBank k d c omega).program.rootReads=d.program.rootReads ∧
      (spectrumBank k d c omega).program.divisions=d.program.divisions := by
  have h := UniformKernelSpectrumPreparation.crossBank_counts k (prepared k d c)
    (retained k d c omega) (kernelRef k d c)
  have hp := prepared_counts k d c
  exact ⟨h.1.trans hp.1,h.2.trans hp.2⟩

theorem spectrumBank_length_bound {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) :
    (spectrumBank k d c omega).length≤d.length+2+6*2^k*(2*c.s+3)+(2^k+1)+9*k*2^k := by
  rw [spectrumBank,UniformKernelSpectrumPreparation.crossBank_length_closed]
  have h := prepared_length_bound k d c
  conv_rhs at h => rw [UniformRadixTwoDAG.width_eq]
  omega

def spectrumRetained {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (j : Fin d.length) :
    Fin (spectrumBank k d c omega).length :=
  UniformKernelSpectrumPreparation.retained (c:=UniformRadixTwoDAG.count k) 6
    ((retained k d c j).castAdd (UniformRadixTwoDAG.width k+1))

theorem spectrumRetained_val {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (j : Fin d.length) :
    (spectrumRetained k d c omega j).val=j.val := by
  exact retained_val k d c j

theorem spectrumBank_old {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (roots : Fin r → ℂ) (j : Fin d.length) :
    (spectrumBank k d c omega).program.eval roots (spectrumRetained k d c omega j)=
      d.program.eval roots j := by
  exact (UniformKernelSpectrumPreparation.bank_original k (prepared k d c)
    (retained k d c omega) 6 (kernelRef k d c) roots (retained k d c j)).trans
    (prepared_old k d c roots j)

/-- The produced spectrum bank feeds the actual cross DAG, with its concrete
Toeplitz recurrence supplying the matrix action. -/
theorem spectrumBank_cross_action {r o a e : ℕ} (k : ℕ) (d : DAG r o)
    (c : Sources d.length a e) (omega : Fin d.length) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (h g : ℕ → ℂ)
    (hh : ∀ i, d.program.eval roots (c.h i)=h i.val)
    (hg : ∀ i, d.program.eval roots (c.g i)=g i.val)
    (homega : d.program.eval roots omega=OAI.ExactFourier.zeta (UniformRadixTwoDAG.width k))
    (he : 0<e) (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (hi : c.s≤c.i₀) (hj : c.j₀+e≤c.s) (x : Fin e → ℂ) :
    (UniformToeplitzCrossDAG.crossDAG k a e (by omega) (by omega)).eval
      ((spectrumBank k d c omega).run roots (spectrumBank_admissible k d c omega roots hd)) x =
      Matrix.mulVec (fun i : Fin a => fun j : Fin e => c.matrix h g i.val j.val) x := by
  rw [spectrumBank_run k d c omega roots hd h g hh hg homega]
  exact UniformToeplitzCrossDAG.toeplitz_cross_eval k c.s a e c.i₀ c.j₀ c.positive he hsize h g hi hj x

/-- Adapter to the actual shared h/reciprocal bank, without recompiling it. -/
def reciprocalDAG {r n t : ℕ} (b : UniformReciprocalPreparation.Bank r n t) : DAG r 0 :=
  ⟨b.length,b.program,Fin.elim0⟩

def reciprocalSources {r n t : ℕ} (b : UniformReciprocalPreparation.Bank r n t)
    (a e s i₀ j₀ : ℕ) (ha : 0<a) (hh : i₀+a≤n+1) (hg : s<t+1) :
    Sources (reciprocalDAG b).length a e :=
  ⟨n+1,t+1,b.h,b.g,s,i₀,j₀,ha,hh,hg⟩

/-- Prior finite coefficient correctness comes from the reciprocal compiler;
the six new kernels and spectra are supplied by the literal extension here. -/
theorem reciprocal_spectrumBank_run {r n t : ℕ} (b : UniformReciprocalPreparation.Bank r n t)
    (k a e s i₀ j₀ : ℕ) (ha : 0<a) (hh : i₀+a≤n+1) (hg : s<t+1)
    (omega : Fin b.length) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hb : b.program.Admissible roots) (hc : b.Correct roots f)
    (homega : b.program.eval roots omega=OAI.ExactFourier.zeta (UniformRadixTwoDAG.width k)) :
    let c := reciprocalSources b a e s i₀ j₀ ha hh hg
    (spectrumBank k (reciprocalDAG b) c omega).run roots
        (spectrumBank_admissible k (reciprocalDAG b) c omega roots hb)=
      UniformToeplitzCrossDAG.sharedBank k (UniformToeplitzCrossDAG.rankKernels k a e
        (c.matrix (fun i => PowerSeries.coeff i f) (fun i => PowerSeries.coeff i f⁻¹))
        (c.left (fun i => PowerSeries.coeff i f)) (c.right (fun i => PowerSeries.coeff i f⁻¹))) := by
  dsimp only
  exact spectrumBank_run k (reciprocalDAG b) _ omega roots hb _ _ hc.1 hc.2.1 homega

end ExactFourierCircuits.UniformRankKernelPreparation
