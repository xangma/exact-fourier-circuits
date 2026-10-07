import UniformNewtonTableMachine
import UniformReciprocalPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReciprocalMachine
open UniformMachine
open scoped BigOperators

inductive Op where
  | literal (dst value : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | literalScalar (dst : ℕ) (value : ℚ)
  | getScalar (dst address : ℕ)
  | putScalar (address src : ℕ)
  | field (op : FieldOp) (dst left right : ℕ)
  deriving DecidableEq

def Op.code : Op → UniformMachine.Instruction
  | .literal d v =>  .natLiteral d v
  | .add d l r =>  .natBinary .add d l r
  | .sub d l r =>  .natBinary .sub d l r
  | .mul d l r =>  .natBinary .mul d l r
  | .literalScalar d q =>  .scalarLiteral d q
  | .getScalar d a =>  .loadScalar d a
  | .putScalar a r =>  .storeScalar a r

  | .field op d l r => .fieldBinary op d l r

noncomputable section

def Op.apply (o : Op) (s : State) : State := match o with
  | .literal d v =>  writeNat s d v
  | .add d l r =>  writeNat s d (s.natReg l+s.natReg r)
  | .sub d l r =>  writeNat s d (s.natReg l-s.natReg r)
  | .mul d l r =>  writeNat s d (s.natReg l*s.natReg r)
  | .literalScalar d q =>  writeScalar s d ⟨q,false⟩
  | .getScalar d a =>  writeScalar s d ((s.scalarHeap (s.natReg a)).getD Scalar.zero)
  | .putScalar a r =>  {next s with scalarHeap:=(Function.update s.scalarHeap
      (s.natReg a) (some (s.scalarReg r)))}

  | .field op d l r => writeScalar s d ((evalField op (s.scalarReg l) (s.scalarReg r)).getD Scalar.zero)

def Op.readable (o : Op) (s : State) : Prop := match o with
  | .getScalar _ a =>  (s.scalarHeap (s.natReg a)).isSome=true
  | .field op _ l r => (evalField op (s.scalarReg l) (s.scalarReg r)).isSome=true
  | _ =>  True

def Op.peak (o : Op) (s : State) : ℕ := match o with
  | .literal _ v =>  v
  | .add _ l r =>  s.natReg l+s.natReg r
  | .sub _ l r =>  s.natReg l-s.natReg r
  | .mul _ l r =>  s.natReg l*s.natReg r
  | .putScalar a _ =>  s.natReg a
  | _ =>  0

def applyBlock : List Op → State → State
  | [],s =>  s
  | o::b,s =>  applyBlock b (o.apply s)

def readable : List Op → State → Prop
  | [],_ =>  True
  | o::b,s =>  o.readable s ∧ readable b (o.apply s)

def peak : List Op → State → ℕ
  | [],_ =>  0
  | o::b,s =>  max (o.peak s) (peak b (o.apply s))

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by
  cases o  <;>  rfl

theorem Op.step (o : Op) (p : Program) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hcode:p[s.pc]?=some o.code) (hread:o.readable s) :
    UniformMachine.step p n x s = .running (o.apply s) := by
  cases o  <;>  simp [UniformMachine.step,hcode,Op.code,Op.apply,evalNat]
  case getScalar d a => 
    cases hh:s.scalarHeap (s.natReg a) with
    | none =>  simp [Op.readable,hh] at hread
    | some v =>  simp
  case field op d l r =>
    cases hh:evalField op (s.scalarReg l) (s.scalarReg r) with
    | none => simp [Op.readable,hh] at hread
    | some v => simp

theorem Op.apply_bound (o : Op) (B : ℕ) (s : State) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (hpeak:o.peak s ≤ B) : WordBound B (o.apply s) := by
  cases o with
  | literal d v =>  exact writeNat_bound B s d v hs hp hpeak
  | add d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | sub d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | mul d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | literalScalar d q =>  exact writeScalar_bound B s d _ hs hp
  | getScalar d a =>  exact writeScalar_bound B s d _ hs hp
  | field op d l r => exact writeScalar_bound B s d _ hs hp
  | putScalar a r => 
    refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
    intro j v hj
    by_cases he:j=s.natReg a
    · simpa [he,Op.peak] using hpeak
    · exact hs.2.2.2.1 j v (by simpa [Op.apply,next,he] using hj)

def BlockAt (b : List Op) (p : Program) (base : ℕ) : Prop :=
  ∀i,(hi:i < b.length)→p[base+i]?=some (b[i]'hi).code

/-- Every store and every operand calculation is one real charged instruction. -/
theorem block_runs (b : List Op) (p : Program) (base n B : ℕ) (x : Fin n → ℂ)
    (s : State) (hc:BlockAt b p base) (hpc:s.pc=base) (hs:WordBound B s)
    (hcode:base+b.length ≤ B) (hread:readable b s) (hpeak:peak b s ≤ B) :
    BoundedRuns p n x B s b.length (applyBlock b s) := by
  induction b generalizing base s with
  | nil =>  exact .refl hs
  | cons o b ih => 
    have hp:s.pc+1 ≤ B:=by
      simp only [List.length_cons] at hcode
      omega
    have hpk:o.peak s ≤ B:=(le_max_left _ _).trans hpeak
    have hb:=o.apply_bound B s hs hp hpk
    have htail:BlockAt b p (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change p[base+(i+1)]?=some (b[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have hr:=ih (base+1) (o.apply s) htail (by rw [Op.apply_pc,hpc]) hb
      (by simp only [List.length_cons] at hcode;omega) hread.2
      ((le_max_right _ _).trans hpeak)
    have hfirst:=hc 0 (by simp)
    change p[base]?=some o.code at hfirst
    exact .next hs (o.step p n x s (by simpa [hpc] using hfirst) hread.1) hr

theorem applyBlock_pc (b : List Op) (s : State) : (applyBlock b s).pc=s.pc+b.length := by
  induction b generalizing s with
  | nil =>  simp [applyBlock]
  | cons o b ih =>  simp [applyBlock,ih,Op.apply_pc];omega

theorem applyBlock_append (b c : List Op) (s : State) :
    applyBlock (b++c) s=applyBlock c (applyBlock b s) := by
  induction b generalizing s with
  | nil =>  rfl
  | cons o b ih =>  exact ih (o.apply s)

theorem applyBlock_outputs (b : List Op) (s : State) :
    (applyBlock b s).outputs=s.outputs ∧ (applyBlock b s).rootOrders=s.rootOrders := by
  induction b generalizing s with
  | nil =>  exact ⟨rfl,rfl⟩
  | cons o b ih => 
    have h:=ih (o.apply s)
    cases o  <;>  exact h

theorem applyBlock_natHeap (b : List Op) (s : State) :
    (applyBlock b s).natHeap=s.natHeap := by
  induction b generalizing s with
  | nil => rfl
  | cons o b ih => rw [applyBlock,ih];cases o <;> rfl


/-- No scalar-value branch or fresh root instruction occurs in this fixed code. -/
def bootBlock : List Op := [.literal 20 1,.literal 21 0,.getScalar 1 17,
  .literalScalar 4 1,.field .div 4 4 1,.literalScalar 5 0,
  .putScalar 19 4,.literal 22 1]
def resetBlock : List Op := [.literalScalar 0 0,.literal 23 0]
def termBlock : List Op := [.add 24 23 20,.mul 24 18 24,.add 24 17 24,
  .getScalar 1 24,.sub 25 22 20,.sub 25 25 23,.add 25 19 25,
  .getScalar 2 25,.field .mul 3 1 2,.field .add 0 0 3,.add 23 23 20]
def finishBlock : List Op := [.field .mul 0 4 0,.field .sub 0 5 0,
  .add 25 19 22,.putScalar 25 0,.add 22 22 20]

def program : Program := bootBlock.map Op.code ++ [.branchLT 22 16 9 30] ++
  resetBlock.map Op.code ++ [.branchLT 23 22 12 24] ++ termBlock.map Op.code ++
  [.jump 11] ++ finishBlock.map Op.code ++ [.jump 8,.halt]

theorem program_length : program.length=31 := rfl
theorem boot_at : BlockAt bootBlock program 0 := by
  intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem reset_at : BlockAt resetBlock program 9 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem term_at : BlockAt termBlock program 12 := by
  intro i hi;change i < 11 at hi;interval_cases i <;> rfl
theorem finish_at : BlockAt finishBlock program 24 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem outer_branch : program[8]?=some (.branchLT 22 16 9 30) := rfl
theorem inner_branch : program[11]?=some (.branchLT 23 22 12 24) := rfl
theorem inner_jump : program[23]?=some (.jump 11) := rfl
theorem outer_jump : program[29]?=some (.jump 8) := rfl
theorem halt_at : program[30]?=some .halt := rfl

def prepared (v : ℂ) : Scalar := ⟨v,false⟩
def HBank (r h stride : ℕ) (f : PowerSeries ℂ) (s : State) : Prop :=
  ∀j,j < r→s.scalarHeap (h+stride*j)=some (prepared (PowerSeries.coeff j f))
def GPrefix (k g : ℕ) (f : PowerSeries ℂ) (s : State) : Prop :=
  ∀j,j < k→s.scalarHeap (g+j)=some (prepared (PowerSeries.coeff j f⁻¹))
/-- The source and destination may be noncontiguous; only actual used ports
must be disjoint. No uncharged source copy is assumed. -/
def Disjoint (r h stride g : ℕ) : Prop :=
  ∀i,i < r→∀j,j < r→h+stride*i≠g+j

structure Constants (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State) : Prop where
  order : s.natReg 16=r
  source : s.natReg 17=h
  stride : s.natReg 18=stride
  target : s.natReg 19=g
  one : s.natReg 20=1
  zero : s.natReg 21=0
  inverse : s.scalarReg 4=prepared ((PowerSeries.constantCoeff f)⁻¹)
  scalarZero : s.scalarReg 5=prepared 0

structure Degree (k g : ℕ) (f : PowerSeries ℂ) (s : State) : Prop where
  index : s.natReg 22=k
  values : GPrefix k g f s

def partialSum (f : PowerSeries ℂ) (k j : ℕ) : ℂ :=
  ∑i∈Finset.range j,PowerSeries.coeff (i+1) f * PowerSeries.coeff (k-1-i) f⁻¹

structure Term (k j : ℕ) (f : PowerSeries ℂ) (s : State) : Prop where
  degree : s.natReg 22=k
  index : s.natReg 23=j
  accumulator : s.scalarReg 0=prepared (partialSum f k j)

theorem Constants.withPC {r h stride g pc : ℕ} {f : PowerSeries ℂ} {s : State}
    (hc:Constants r h stride g f s) : Constants r h stride g f {s with pc:=pc} := by
  cases hc;constructor <;> assumption
theorem Degree.withPC {k g pc : ℕ} {f : PowerSeries ℂ} {s : State}
    (hd:Degree k g f s) : Degree k g f {s with pc:=pc} := by
  cases hd;constructor <;> assumption
theorem Term.withPC {k j pc : ℕ} {f : PowerSeries ℂ} {s : State}
    (ht:Term k j f s) : Term k j f {s with pc:=pc} := by
  cases ht;constructor;assumption;assumption;assumption

theorem partialSum_zero (f : PowerSeries ℂ) (k : ℕ) : partialSum f k 0=0 := by
  simp [partialSum]
theorem partialSum_succ (f : PowerSeries ℂ) (k j : ℕ) : partialSum f k (j+1)=
    partialSum f k j+PowerSeries.coeff (j+1) f*PowerSeries.coeff (k-1-j) f⁻¹ := by
  exact Finset.sum_range_succ _ j

theorem reciprocal_step (f : PowerSeries ℂ) (k : ℕ) (hk:0 < k) :
    -(PowerSeries.constantCoeff f)⁻¹*partialSum f k k=PowerSeries.coeff k f⁻¹ := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  rw [UniformReciprocalPreparation.inverse_coeff_succ]
  unfold partialSum
  simp only [Nat.succ_sub_one]
  rw [Fin.sum_univ_eq_sum_range (fun j=>PowerSeries.coeff (j+1) f*PowerSeries.coeff (a-j) f⁻¹) (a+1)]

def Frame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.trans h.2.2⟩
theorem block_frame (b : List Op) (s : State) : Frame s (applyBlock b s) :=
  ⟨applyBlock_natHeap b s,(applyBlock_outputs b s).1,(applyBlock_outputs b s).2⟩

def HeapFree : Op→Bool | .putScalar _ _=>false | _=>true

theorem applyBlock_heap (b : List Op) (s : State) (hb:∀o∈b,HeapFree o=true) :
    (applyBlock b s).scalarHeap=s.scalarHeap := by
  induction b generalizing s with
  | nil => rfl
  | cons o b ih =>
    rw [applyBlock,ih _ (fun q hq=>hb q (by simp [hq]))]
    have ho:=hb o (by simp)
    cases o <;> first | rfl | simp [HeapFree] at ho

def Outside (g r : ℕ) (s u : State) : Prop :=
  ∀i,(i < g ∨ g+r ≤ i)→u.scalarHeap i=s.scalarHeap i

theorem Outside.trans {g r : ℕ} {s u v : State}
    (h:Outside g r s u) (h':Outside g r u v) : Outside g r s v :=
  fun i hi=>(h' i hi).trans (h i hi)

theorem boot_ready (r h stride _g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h17:s.natReg 17=h) : readable bootBlock s := by
  have hz:=hh 0 hr
  simp only [Nat.mul_zero,Nat.add_zero] at hz
  simp [readable,bootBlock,Op.readable,Op.apply,writeNat,writeScalar,next,
    h17,hz,evalField,prepared,hzero,PowerSeries.coeff_zero_eq_constantCoeff]

theorem boot_constants (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h16:s.natReg 16=r) (h17:s.natReg 17=h) (h18:s.natReg 18=stride)
    (h19:s.natReg 19=g) : Constants r h stride g f (applyBlock bootBlock s) := by
  have hz:=hh 0 hr
  simp only [Nat.mul_zero,Nat.add_zero] at hz
  constructor <;> simp [applyBlock,bootBlock,Op.apply,writeNat,writeScalar,next,
    h16,h17,h18,h19,hz,prepared,evalField,hzero,PowerSeries.coeff_zero_eq_constantCoeff]

theorem boot_heap (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h17:s.natReg 17=h) (h19:s.natReg 19=g) :
    (applyBlock bootBlock s).scalarHeap=Function.update s.scalarHeap g
      (some (prepared ((PowerSeries.constantCoeff f)⁻¹))) := by
  have hz:=hh 0 hr
  simp only [Nat.mul_zero,Nat.add_zero] at hz
  simp [applyBlock,bootBlock,Op.apply,writeNat,writeScalar,next,h17,h19,hz,
    prepared,evalField,hzero,PowerSeries.coeff_zero_eq_constantCoeff]

theorem boot_degree (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h17:s.natReg 17=h) (h19:s.natReg 19=g) :
    Degree 1 g f (applyBlock bootBlock s) := by
  refine ⟨by simp [applyBlock,bootBlock,Op.apply,writeNat,writeScalar,next],?_⟩
  intro j hj
  have hj0:j=0:=by omega
  subst j
  rw [boot_heap r h stride g f s hr hh hzero h17 h19]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

theorem boot_hbank (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h17:s.natReg 17=h) (h19:s.natReg 19=g) (hd:Disjoint r h stride g) :
    HBank r h stride f (applyBlock bootBlock s) := by
  intro j hj
  rw [boot_heap r h stride g f s hr hh hzero h17 h19]
  rw [Function.update_of_ne (by simpa using hd j hj 0 hr),hh j hj]

theorem boot_outside (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hr:0 < r) (hh:HBank r h stride f s) (hzero:PowerSeries.constantCoeff f≠0)
    (h17:s.natReg 17=h) (h19:s.natReg 19=g) :
    Outside g r s (applyBlock bootBlock s) := by
  intro i hi
  rw [boot_heap r h stride g f s hr hh hzero h17 h19]
  simp [show i≠g by omega]


theorem reset_constants (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) : Constants r h stride g f (applyBlock resetBlock s) := by
  cases hc
  constructor <;> simp_all [applyBlock,resetBlock,Op.apply,writeNat,writeScalar,next]
theorem reset_degree (k g : ℕ) (f : PowerSeries ℂ) (s : State) (hd:Degree k g f s) :
    Degree k g f (applyBlock resetBlock s) := by
  refine ⟨?_,hd.values⟩
  simpa [applyBlock,resetBlock,Op.apply,writeNat,writeScalar,next] using hd.index
theorem reset_term (k g : ℕ) (f : PowerSeries ℂ) (s : State) (hd:Degree k g f s) :
    Term k 0 f (applyBlock resetBlock s) := by
  constructor <;> simp [applyBlock,resetBlock,Op.apply,writeNat,writeScalar,next,
    hd.index,partialSum,prepared]

theorem term_heap (s : State) : (applyBlock termBlock s).scalarHeap=s.scalarHeap :=
  applyBlock_heap termBlock s (by simp [termBlock,HeapFree])

theorem term_constants (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) : Constants r h stride g f (applyBlock termBlock s) := by
  cases hc
  constructor <;> simp_all [applyBlock,termBlock,Op.apply,writeNat,writeScalar,next]

theorem term_degree (k g : ℕ) (f : PowerSeries ℂ) (s : State) (hd:Degree k g f s) :
    Degree k g f (applyBlock termBlock s) := by
  refine ⟨?_,?_⟩
  · simpa [applyBlock,termBlock,Op.apply,writeNat,writeScalar,next] using hd.index
  · intro i hi;rw [term_heap];exact hd.values i hi

theorem term_ready (r h stride g k j : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (hd:Degree k g f s) (ht:Term k j f s)
    (hh:HBank r h stride f s) (hkr:k < r) (hj:j < k) : readable termBlock s := by
  have hvh:=hh (j+1) (by omega)
  have hvg:=hd.values (k-1-j) (by omega)
  simp [readable,termBlock,Op.readable,Op.apply,writeNat,writeScalar,next,
    hc.source,hc.stride,hc.target,hc.one,ht.degree,ht.index,ht.accumulator,
    hvh,hvg,evalField,prepared]

theorem term_term (r h stride g k j : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (hd:Degree k g f s) (ht:Term k j f s)
    (hh:HBank r h stride f s) (hkr:k < r) (hj:j < k) :
    Term k (j+1) f (applyBlock termBlock s) := by
  have hvh:=hh (j+1) (by omega)
  have hvg:=hd.values (k-1-j) (by omega)
  constructor <;> simp [applyBlock,termBlock,Op.apply,writeNat,writeScalar,next,
    hc.source,hc.stride,hc.target,hc.one,ht.degree,ht.index,ht.accumulator,
    hvh,hvg,evalField,prepared,partialSum_succ]

theorem finish_ready (r h stride g k : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k k f s) : readable finishBlock s := by
  simp [readable,finishBlock,Op.readable,Op.apply,writeScalar,next,
    hc.inverse,hc.scalarZero,ht.accumulator,evalField,prepared]

theorem finish_heap (r h stride g k : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k k f s) (hk:0 < k) :
    (applyBlock finishBlock s).scalarHeap=Function.update s.scalarHeap (g+k)
      (some (prepared (PowerSeries.coeff k f⁻¹))) := by
  have he:=reciprocal_step f k hk
  simp [applyBlock,finishBlock,Op.apply,writeNat,writeScalar,next,hc.target,hc.one,
    hc.inverse,hc.scalarZero,ht.accumulator,ht.degree,evalField,prepared,←neg_mul,he]

theorem finish_constants (r h stride g : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) : Constants r h stride g f (applyBlock finishBlock s) := by
  cases hc
  constructor <;> simp_all [applyBlock,finishBlock,Op.apply,writeNat,writeScalar,next]

theorem finish_degree (r h stride g k : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (hd:Degree k g f s) (ht:Term k k f s)
    (hk:0 < k) : Degree (k+1) g f (applyBlock finishBlock s) := by
  refine ⟨?_,?_⟩
  · simp [applyBlock,finishBlock,Op.apply,writeNat,writeScalar,next,hd.index,hc.one]
  · intro j hj
    rw [finish_heap r h stride g k f s hc ht hk]
    by_cases he:j=k
    · subst j;simp
    · rw [Function.update_of_ne (by omega)]
      exact hd.values j (by omega)

theorem finish_hbank (r h stride g k : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k k f s) (hh:HBank r h stride f s)
    (hk:0 < k) (hkr:k < r) (hj:Disjoint r h stride g) :
    HBank r h stride f (applyBlock finishBlock s) := by
  intro j hji
  rw [finish_heap r h stride g k f s hc ht hk,Function.update_of_ne (hj j hji k hkr)]
  exact hh j hji

theorem finish_outside (r h stride g k : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k k f s) (hk:0 < k) (hkr:k < r) :
    Outside g r s (applyBlock finishBlock s) := by
  intro i hi
  rw [finish_heap r h stride g k f s hc ht hk,Function.update_of_ne (by omega)]

theorem boot_peak (r h stride g B : ℕ) (s : State) (h19:s.natReg 19=g)
    (hB:h+stride*r+g+r+40 ≤ B) : peak bootBlock s ≤ B := by
  simp [peak,bootBlock,Op.peak,Op.apply,writeNat,writeScalar,next,h19]
  omega

theorem term_peak (r h stride g k j B : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k j f s) (hkr:k < r) (hj:j < k)
    (hB:h+stride*r+g+r+40 ≤ B) : peak termBlock s ≤ B := by
  have hm:stride*(j+1) ≤ stride*r:=Nat.mul_le_mul_left stride (by omega)
  simp [peak,termBlock,Op.peak,Op.apply,writeNat,writeScalar,next,
    hc.source,hc.stride,hc.target,hc.one,ht.degree,ht.index]
  omega

theorem finish_peak (r h stride g k B : ℕ) (f : PowerSeries ℂ) (s : State)
    (hc:Constants r h stride g f s) (ht:Term k k f s) (hkr:k < r)
    (hB:h+stride*r+g+r+40 ≤ B) : peak finishBlock s ≤ B := by
  simp [peak,finishBlock,Op.peak,Op.apply,writeNat,writeScalar,next,
    hc.target,hc.one,ht.degree]
  omega


def termEnd (s : State) : State := {applyBlock termBlock {s with pc:=12} with pc:=11}
def finishEnd (s : State) : State := {applyBlock finishBlock {s with pc:=24} with pc:=8}

theorem term_iteration (n : ℕ) (x : Fin n→ℂ) (r h stride g k j B : ℕ)
    (f : PowerSeries ℂ) (s : State) (hc:Constants r h stride g f s)
    (hd:Degree k g f s) (ht:Term k j f s) (hh:HBank r h stride f s)
    (hp:s.pc=11) (hkr:k < r) (hj:j < k) (hB:h+stride*r+g+r+40 ≤ B)
    (hs:WordBound B s) :
    BoundedRuns program n x B s 13 (termEnd s) ∧
    Constants r h stride g f (termEnd s) ∧ Degree k g f (termEnd s) ∧
    Term k (j+1) f (termEnd s) ∧ (termEnd s).scalarHeap=s.scalarHeap ∧ Frame s (termEnd s) := by
  let e:State:={s with pc:=12}
  have he:WordBound B e:=changePC_bound B s 12 hs (by omega)
  have hr:=block_runs termBlock program 12 n B x e term_at rfl he (by change 12+11 ≤ B;omega)
    (term_ready r h stride g k j f e hc.withPC hd.withPC ht.withPC hh hkr hj)
    (term_peak r h stride g k j B f e hc.withPC ht.withPC hkr hj hB)
  have hf:WordBound B (termEnd s):=changePC_bound B _ 11 hr.final_bound (by omega)
  have hg:BoundedRuns program n x B (applyBlock termBlock e) 1 (termEnd s):=by
    refine .next hr.final_bound ?_ (.refl hf)
    have hp':(applyBlock termBlock e).pc=23:=by rw [applyBlock_pc];rfl
    rw [step,hp',inner_jump];rfl
  have hb:BoundedRuns program n x B s 1 e:=by
    refine .next hs ?_ (.refl he)
    rw [step,hp,inner_branch]
    simp [ht.index,ht.degree,hj,e]
  refine ⟨?_,(term_constants r h stride g f e hc.withPC).withPC,
    (term_degree k g f e hd.withPC).withPC,
    (term_term r h stride g k j f e hc.withPC hd.withPC ht.withPC hh hkr hj).withPC,
    term_heap e,block_frame termBlock e⟩
  convert hb.trans (hr.trans hg) using 1
  rfl

theorem inner_loop (n : ℕ) (x : Fin n→ℂ) (r h stride g k fuel j B : ℕ)
    (f : PowerSeries ℂ) (s : State) (hc:Constants r h stride g f s)
    (hd:Degree k g f s) (ht:Term k j f s) (hh:HBank r h stride f s)
    (hp:s.pc=11) (hkr:k < r) (hj:j+fuel=k) (hB:h+stride*r+g+r+40 ≤ B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (13*fuel) u ∧ Constants r h stride g f u ∧
    Degree k g f u ∧ Term k k f u ∧ u.pc=11 ∧ u.scalarHeap=s.scalarHeap ∧ Frame s u := by
  induction fuel generalizing j s with
  | zero =>
    have hjk:j=k:=by omega
    subst j
    exact ⟨s,.refl hs,hc,hd,ht,hp,rfl,rfl,rfl,rfl⟩
  | succ fuel ih =>
    obtain ⟨hr,hc',hd',ht',hw,hf⟩:=term_iteration n x r h stride g k j B f s
      hc hd ht hh hp hkr (by omega) hB hs
    have hh':HBank r h stride f (termEnd s):=by
      intro i hi;rw [hw];exact hh i hi
    obtain ⟨u,hu,hcu,hdu,htu,hpu,hwu,hfu⟩:=ih (j+1) (termEnd s) hc' hd' ht' hh'
      rfl (by omega) hr.final_bound
    refine ⟨u,?_,hcu,hdu,htu,hpu,hwu.trans hw,hf.trans hfu⟩
    convert hr.trans hu using 1;omega

theorem outer_iteration (n : ℕ) (x : Fin n→ℂ) (r h stride g k B : ℕ)
    (f : PowerSeries ℂ) (s : State) (hc:Constants r h stride g f s)
    (hd:Degree k g f s) (hh:HBank r h stride f s) (hp:s.pc=8)
    (hk:0 < k) (hkr:k < r) (hj:Disjoint r h stride g) (hB:h+stride*r+g+r+40 ≤ B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (13*k+10) u ∧ Constants r h stride g f u ∧
    Degree (k+1) g f u ∧ HBank r h stride f u ∧ u.pc=8 ∧ Frame s u ∧ Outside g r s u := by
  let e:State:={s with pc:=9}
  have he:WordBound B e:=changePC_bound B s 9 hs (by omega)
  have hb:BoundedRuns program n x B s 1 e:=by
    refine .next hs ?_ (.refl he)
    rw [step,hp,outer_branch];simp [hd.index,hc.order,hkr,e]
  have hz:=block_runs resetBlock program 9 n B x e reset_at rfl he (by change 9+2 ≤ B;omega)
    (by simp [readable,resetBlock,Op.readable])
    (by simp [peak,resetBlock,Op.peak])
  let z:=applyBlock resetBlock e
  have hcz:Constants r h stride g f z:=reset_constants r h stride g f e hc.withPC
  have hdz:Degree k g f z:=reset_degree k g f e hd.withPC
  have htz:Term k 0 f z:=reset_term k g f e hd.withPC
  have hhz:HBank r h stride f z:=hh
  have hpz:z.pc=11:=by rw [applyBlock_pc];rfl
  obtain ⟨v,hv,hcv,hdv,htv,hpv,hwv,hfv⟩:=inner_loop n x r h stride g k k 0 B f z
    hcz hdz htz hhz hpz hkr (by omega) hB hz.final_bound
  let t:State:={v with pc:=24}
  have htb:WordBound B t:=changePC_bound B v 24 hv.final_bound (by omega)
  have ht:BoundedRuns program n x B v 1 t:=by
    refine .next hv.final_bound ?_ (.refl htb)
    rw [step,hpv,inner_branch];simp [htv.index,htv.degree,t]
  have hf:=block_runs finishBlock program 24 n B x t finish_at rfl htb
    (by change 24+5 ≤ B;omega) (finish_ready r h stride g k f t hcv.withPC htv.withPC)
    (finish_peak r h stride g k B f t hcv.withPC htv.withPC hkr hB)
  have hht:HBank r h stride f t:=by intro i hi;change v.scalarHeap _=_;rw [hwv];exact hh i hi
  let u:=finishEnd v
  have hub:WordBound B u:=changePC_bound B _ 8 hf.final_bound (by omega)
  have hg:BoundedRuns program n x B (applyBlock finishBlock t) 1 u:=by
    refine .next hf.final_bound ?_ (.refl hub)
    have hpf:(applyBlock finishBlock t).pc=29:=by rw [applyBlock_pc];rfl
    rw [step,hpf,outer_jump];rfl
  refine ⟨u,?_,(finish_constants r h stride g f t hcv.withPC).withPC,
    (finish_degree r h stride g k f t hcv.withPC hdv.withPC htv.withPC hk).withPC,
    finish_hbank r h stride g k f t hcv.withPC htv.withPC hht hk hkr hj,rfl,?_,?_⟩
  · convert hb.trans (hz.trans (hv.trans (ht.trans (hf.trans hg)))) using 1
    change 13*k+10=1+(2+(13*k+(1+(5+1))))
    omega
  · exact (block_frame resetBlock e).trans (hfv.trans (block_frame finishBlock t))
  · have hwz:z.scalarHeap=s.scalarHeap:=rfl
    intro i hi
    have hfi:=finish_outside r h stride g k f t hcv.withPC htv.withPC hk hkr i hi
    exact hfi.trans ((congrFun hwv i).trans (congrFun hwz i))

def work (k : ℕ) : ℕ→ℕ
  | 0=>0
  | fuel+1=>13*k+10+work (k+1) fuel

theorem outer_loop (n : ℕ) (x : Fin n→ℂ) (r h stride g k fuel B : ℕ)
    (f : PowerSeries ℂ) (s : State) (hc:Constants r h stride g f s)
    (hd:Degree k g f s) (hh:HBank r h stride f s) (hp:s.pc=8)
    (hk:0 < k) (he:k+fuel=r) (hj:Disjoint r h stride g) (hB:h+stride*r+g+r+40 ≤ B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (work k fuel) u ∧ Constants r h stride g f u ∧
    Degree r g f u ∧ HBank r h stride f u ∧ u.pc=8 ∧ Frame s u ∧ Outside g r s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkr:k=r:=by omega
    subst k
    exact ⟨s,.refl hs,hc,hd,hh,hp,⟨rfl,rfl,rfl⟩,fun i _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨v,hv,hcv,hdv,hhv,hpv,hfv,hov⟩:=outer_iteration n x r h stride g k B f s
      hc hd hh hp hk (by omega) hj hB hs
    obtain ⟨u,hu,hcu,hdu,hhu,hpu,hfu,hou⟩:=ih (k+1) v hcv hdv hhv hpv (by omega)
      (by omega) hv.final_bound
    refine ⟨u,?_,hcu,hdu,hhu,hpu,hfv.trans hfu,hov.trans hou⟩
    simpa [work] using hv.trans hu


/-- Work is charged by the literal loops, including their branch and jump
instructions. Bootstrap and the terminating branch/halt cost ten further steps. -/
def runtime (r : ℕ) : ℕ := work 1 (r-1)+10

theorem work_bound (k fuel r : ℕ) (hr:1 ≤ r) (he:k+fuel ≤ r) :
    work k fuel ≤ 23*r*fuel := by
  induction fuel generalizing k with
  | zero => simp [work]
  | succ fuel ih =>
    have htail:=ih (k+1) (by omega)
    have hk:k ≤ r:=by omega
    have hstep:13*k+10 ≤ 23*r:=by omega
    simp only [work]
    nlinarith

theorem runtime_bound (r : ℕ) (hr:0 < r) : runtime r ≤ 23*r^2+10 := by
  have h:=work_bound 1 (r-1) r (by omega) (by omega)
  have hm:r-1 ≤ r:=by omega
  unfold runtime
  nlinarith

/-- Complete fixed-program execution from populated source coefficients.
The source predicate supplies values only; no action/row-table premise is used. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (r h stride g B : ℕ)
    (f : PowerSeries ℂ) (s : State) (hr:0 < r) (hh:HBank r h stride f s)
    (hzero:PowerSeries.constantCoeff f≠0) (hj:Disjoint r h stride g)
    (hp:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=h)
    (h18:s.natReg 18=stride) (h19:s.natReg 19=g)
    (hB:h+stride*r+g+r+40 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime r) u ∧ GPrefix r g f u ∧
    HBank r h stride f u ∧ Frame s u ∧ Outside g r s u := by
  have hb:=block_runs bootBlock program 0 n B x s boot_at hp hs (by change 0+8 ≤ B;omega)
    (boot_ready r h stride g f s hr hh hzero h17)
    (boot_peak r h stride g B s h19 hB)
  let z:=applyBlock bootBlock s
  have hcz:=boot_constants r h stride g f s hr hh hzero h16 h17 h18 h19
  have hdz:=boot_degree r h stride g f s hr hh hzero h17 h19
  have hhz:=boot_hbank r h stride g f s hr hh hzero h17 h19 hj
  have hpz:z.pc=8:=by rw [applyBlock_pc,hp];rfl
  obtain ⟨v,hv,hcv,hdv,hhv,hpv,hfv,hov⟩:=outer_loop n x r h stride g 1 (r-1) B f z
    hcz hdz hhz hpz (by omega) (by omega) hj hB hb.final_bound
  let u:State:={v with pc:=30}
  have hub:WordBound B u:=changePC_bound B v 30 hv.final_bound (by omega)
  have hhalt : BoundedExecution program n x B u 1 u:=.halt hub (by rw [step,halt_at])
  have he:BoundedExecution program n x B v 2 u:=by
    refine .next hv.final_bound ?_ hhalt
    rw [step,hpv,outer_branch]
    simp [hdv.index,hcv.order,u]
  refine ⟨u,?_,hdv.values,hhv,(block_frame bootBlock s).trans hfv,
    (boot_outside r h stride g f s hr hh hzero h17 h19).trans hov⟩
  convert hb.executes (hv.executes he) using 1
  change work 1 (r-1)+10=8+(work 1 (r-1)+2)
  omega

/-- A linear address bound gives O(log B) bits for every address in every
actual intermediate state. Strides are charged integer multiplications. -/
def wordBudget (r h stride g : ℕ) : ℕ := h+stride*r+g+r+40

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (r h stride g : ℕ)
    (f : PowerSeries ℂ) (s : State) (hr:0 < r) (hh:HBank r h stride f s)
    (hzero:PowerSeries.constantCoeff f≠0) (hj:Disjoint r h stride g)
    (hp:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=h)
    (h18:s.natReg 18=stride) (h19:s.natReg 19=g)
    (hs:WordBound (wordBudget r h stride g) s) : ∃u,
    BoundedExecution program n x (wordBudget r h stride g) s (runtime r) u ∧
    GPrefix r g f u ∧ HBank r h stride f u ∧ Frame s u ∧ Outside g r s u :=
  execution n x r h stride g _ f s hr hh hzero hj hp h16 h17 h18 h19 le_rfl hs


theorem program_keeps_nat (i : ℕ) (hi:i < 20 ∨ 26 ≤ i) :
    ∀ins∈program,UniformNewtonTableMachine.KeepsNat i ins := by
  simp [program,bootBlock,resetBlock,termBlock,finishBlock,Op.code,
    UniformNewtonTableMachine.KeepsNat]
  omega

theorem execution_keeps_nat {n r B : ℕ} {x : Fin n→ℂ}
    {s u : State} (ht:BoundedExecution program n x B s (runtime r) u)
    (i : ℕ) (hi:i < 20 ∨ 26 ≤ i) : u.natReg i=s.natReg i :=
  UniformNewtonTableMachine.Executes.keeps_nat ht.executes (program_keeps_nat i hi)

theorem wordBudget_polynomial (r h stride g : ℕ) :
    wordBudget r h stride g ≤ 40*(r+h+stride+g+1)^2 := by
  unfold wordBudget
  nlinarith [sq_nonneg (r-h : ℤ)]

theorem finalInvH_val (r : ℕ) (j : Fin r) :
    (UniformNewton.Preparation.finalInvH r j).val=5*r+3+3*j.val := by
  simp [UniformNewton.Preparation.finalInvH,UniformNewton.Preparation.inverseLift,
    UniformNewton.Preparation.inverseCount_formula]
  omega

def newtonSource (r a : ℕ) : ℕ := a+5*r+3

/-- Consumes the actual Newton machine postcondition: q=2 is coefficientwise
H_j^-1, which is the coefficient bank of invH. The generated bank is the
power-series reciprocal (invH)^-1, rather than H. -/
theorem newton_hbank (r a : ℕ) (omega : ℂ) (s : State)
    (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s) :
    HBank r (newtonSource r a) 3 (OAI.ExactFourier.NewtonFourier.invH omega) s := by
  intro j hj
  have h:=hp ⟨j,hj⟩ (2:Fin 5)
  simp only [UniformNewton.Preparation.table,Equiv.symm_apply_apply] at h
  simp only [UniformNewton.Preparation.expected] at h
  norm_num at h
  rw [finalInvH_val] at h
  simpa [newtonSource,prepared,OAI.ExactFourier.NewtonFourier.invH,PowerSeries.coeff_mk,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem newton_zero (omega : ℂ) :
    PowerSeries.constantCoeff (OAI.ExactFourier.NewtonFourier.invH omega)≠0 := by simp

/-- This is an adapter on actual prepared Newton outputs. Primitive-root and
producer hypotheses are discharged by the preceding Newton execution theorem;
they are not an arbitrary coefficient certificate. -/
theorem newton_execution (n : ℕ) (x : Fin n→ℂ) (r a g B : ℕ) (omega : ℂ) (s : State)
    (hr:0 < r) (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s)
    (hd:a+8*r+3 ≤ g) (hpc:s.pc=0) (h16:s.natReg 16=r)
    (h17:s.natReg 17=newtonSource r a) (h18:s.natReg 18=3) (h19:s.natReg 19=g)
    (hB:newtonSource r a+3*r+g+r+40 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime r) u ∧
    GPrefix r g (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    HBank r (newtonSource r a) 3 (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    Frame s u ∧ Outside g r s u := by
  apply execution n x r (newtonSource r a) 3 g B _ s hr (newton_hbank r a omega s hp)
    (newton_zero omega) _ hpc h16 h17 h18 h19 hB hs
  intro i hi j hj
  unfold newtonSource
  omega


/-- Six charged Nat operations adapt the Newton layout. Nat16=r,Nat17=a,
Nat19=g on entry. All scalar banks and all heaps are untouched here. -/
def adapterBlock : List Op := [.literal 20 5,.literal 21 3,.mul 26 16 20,
  .add 26 26 21,.add 17 17 26,.literal 18 3]
def newtonProgram : Program := adapterBlock.map Op.code ++
  program.map (UniformAssembly.relocate 6 37) ++ [.halt]

theorem newtonProgram_length : newtonProgram.length=38 := rfl
theorem adapter_at : BlockAt adapterBlock newtonProgram 0 := by
  intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem newton_code : UniformAssembly.CodeAt program newtonProgram 6 37 := by
  intro i hi;change i < 31 at hi;interval_cases i <;> rfl
theorem newton_halt : newtonProgram[37]?=some .halt := rfl

theorem adapter_peak (r a g B : ℕ) (s : State) (h16:s.natReg 16=r) (h17:s.natReg 17=a)
    (hB:a+9*r+g+80 ≤ B) : peak adapterBlock s ≤ B := by
  simp [peak,adapterBlock,Op.peak,Op.apply,writeNat,next,h16,h17]
  omega

theorem adapter_registers (r a g : ℕ) (s : State) (h16:s.natReg 16=r)
    (h17:s.natReg 17=a) (h19:s.natReg 19=g) :
    (applyBlock adapterBlock s).natReg 16=r ∧
    (applyBlock adapterBlock s).natReg 17=newtonSource r a ∧
    (applyBlock adapterBlock s).natReg 18=3 ∧
    (applyBlock adapterBlock s).natReg 19=g := by
  simp [applyBlock,adapterBlock,Op.apply,writeNat,next,h16,h17,h19,newtonSource,Nat.mul_comm,Nat.add_assoc]

theorem adapter_heap (s : State) : (applyBlock adapterBlock s).scalarHeap=s.scalarHeap := rfl

/-- Actual charged adapter followed by the actual reciprocal loop. The entry
predicate is exactly Newton's proved output contract, with no ready row table. -/
theorem newton_adapter_execution (n : ℕ) (x : Fin n→ℂ) (r a g B : ℕ)
    (omega : ℂ) (s : State) (hr:0 < r)
    (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s) (hd:a+8*r+3 ≤ g)
    (hpc:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=a) (h19:s.natReg 19=g)
    (hB:a+9*r+g+80 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution newtonProgram n x B s (runtime r+7) u ∧
    GPrefix r g (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    HBank r (newtonSource r a) 3 (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    Frame s u ∧ Outside g r s u := by
  have hz:=block_runs adapterBlock newtonProgram 0 n B x s adapter_at hpc hs
    (by change 0+6 ≤ B;omega) (by simp [readable,adapterBlock,Op.readable])
    (adapter_peak r a g B s h16 h17 hB)
  let z:=applyBlock adapterBlock s
  let t:State:={z with pc:=0}
  have htp:UniformNewtonTableMachine.PreparedOutputs r omega a t:=hp
  obtain ⟨hr',ha',hstride,hg⟩:=adapter_registers r a g s h16 h17 h19
  have htb:WordBound B t:=changePC_bound B z 0 hz.final_bound (by omega)
  obtain ⟨u,hu,hgu,hhu,hfu,hou⟩:=newton_execution n x r a g B omega t hr htp hd rfl
    hr' ha' hstride hg (by unfold newtonSource;omega) htb
  have he:=UniformBoundedAssembly.boundedExecution_placed newton_code
    (by rw [program_length];omega : 6+program.length ≤ B) (by omega : 37 ≤ B) hu
  have hpz:z.pc=6:=by rw [applyBlock_pc,hpc];rfl
  have hplaced:UniformAssembly.placed 6 t=z:=by
    change {z with pc:=6}=z
    rw [←hpz]
  rw [hplaced] at he
  have hhalt:BoundedExecution newtonProgram n x B {u with pc:=37} 1 {u with pc:=37}:=
    .halt he.final_bound (by rw [step,newton_halt])
  refine ⟨{u with pc:=37},?_,hgu,hhu,(block_frame adapterBlock s).trans hfu,?_⟩
  · convert hz.executes (he.executes hhalt) using 1
    change runtime r+7=6+(runtime r+1)
    omega
  · intro i hi
    exact hou i hi

def newtonWordBudget (r a g : ℕ) : ℕ := a+9*r+g+80

theorem newtonWordBudget_polynomial (r a g : ℕ) :
    newtonWordBudget r a g ≤ 80*(r+a+g+1) := by unfold newtonWordBudget;omega

def newtonTarget (r a : ℕ) : ℕ := a+8*r+4

theorem canonical_newton_adapter (n : ℕ) (x : Fin n→ℂ) (r a : ℕ)
    (omega : ℂ) (s : State) (hr:0 < r)
    (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s)
    (hpc:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=a)
    (h19:s.natReg 19=newtonTarget r a)
    (hs:WordBound (newtonWordBudget r a (newtonTarget r a)) s) : ∃u,
    BoundedExecution newtonProgram n x (newtonWordBudget r a (newtonTarget r a)) s
      (runtime r+7) u ∧ GPrefix r (newtonTarget r a)
      (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    HBank r (newtonSource r a) 3 (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    Frame s u ∧ Outside (newtonTarget r a) r s u :=
  newton_adapter_execution n x r a (newtonTarget r a) _ omega s hr hp
    (by unfold newtonTarget;omega) hpc h16 h17 h19 le_rfl hs


theorem relocate_keeps_nat (i base ret : ℕ) (ins : UniformMachine.Instruction) :
    UniformNewtonTableMachine.KeepsNat i (UniformAssembly.relocate base ret ins)=
      UniformNewtonTableMachine.KeepsNat i ins := by cases ins <;> rfl

theorem keeps_append (i : ℕ) {p q : Program}
    (hp:∀ins∈p,UniformNewtonTableMachine.KeepsNat i ins)
    (hq:∀ins∈q,UniformNewtonTableMachine.KeepsNat i ins) :
    ∀ins∈p++q,UniformNewtonTableMachine.KeepsNat i ins := by
  intro ins h
  rcases List.mem_append.1 h with h|h
  · exact hp ins h
  · exact hq ins h

theorem keeps_relocate (i base ret : ℕ) {p : Program}
    (hp:∀ins∈p,UniformNewtonTableMachine.KeepsNat i ins) :
    ∀ins∈p.map (UniformAssembly.relocate base ret),UniformNewtonTableMachine.KeepsNat i ins := by
  intro ins h
  rcases List.mem_map.1 h with ⟨old,hold,rfl⟩
  rw [relocate_keeps_nat]
  exact hp old hold

theorem newton_keeps_header (i : ℕ) (hi:10 ≤ i) (hj:i < 20) :
    ∀ins∈UniformNewtonTableMachine.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hs:∀ins∈UniformNewtonTableMachine.setupBlock.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.setupBlock,UniformNewtonTableMachine.saveBlock,
      UniformNewtonTableMachine.literalBlock,List.range_succ,UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat]
    omega
  have ht:=keeps_relocate i 36 169 (UniformNewtonTableMachine.table_keeps_nat i hj)
  have hc:∀ins∈UniformNewtonTableMachine.interpreterStart.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.interpreterStart,UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat]
    omega
  have hp:=keeps_relocate i 173 204 (UniformNewtonTableMachine.interpreter_keeps_nat i hi)
  have hr:∀ins∈UniformNewtonTableMachine.restoreBlock.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.restoreBlock,List.range_succ,UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat]
    omega
  have hh:∀ins∈([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformNewtonTableMachine.program,List.append_assoc] using
    keeps_append i (keeps_append i (keeps_append i (keeps_append i (keeps_append i hs ht) hc) hp) hr) hh

/-- Allocate the reciprocal after the provided root. The two address operations
are charged, then the existing six-step Newton adapter computes its strided source. -/
def afterNewtonBlock : List Op := [.literal 20 1,.add 19 18 20]++adapterBlock

def completeProgram : Program := UniformNewtonTableMachine.program.map
  (UniformAssembly.relocate 0 229) ++ afterNewtonBlock.map Op.code ++
  program.map (UniformAssembly.relocate 237 268) ++ [.halt]

theorem completeProgram_length : completeProgram.length=269 := by
  simp [completeProgram,UniformNewtonTableMachine.program_length,program_length,
    afterNewtonBlock,adapterBlock]

theorem complete_newton_code : UniformAssembly.CodeAt
    UniformNewtonTableMachine.program completeProgram 0 229 := by
  intro i hi
  simp only [Nat.zero_add,completeProgram]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega),
    List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega),
    List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem afterNewton_at : BlockAt afterNewtonBlock completeProgram 229 := by
  intro i hi
  change i < 8 at hi
  simp only [completeProgram]
  rw [List.getElem?_append_left (by simp [List.length_map,
    UniformNewtonTableMachine.program_length,afterNewtonBlock,adapterBlock];omega),
    List.getElem?_append_left (by simp [List.length_map,
    UniformNewtonTableMachine.program_length,afterNewtonBlock,adapterBlock];omega),
    List.getElem?_append_right (by rw [List.length_map,UniformNewtonTableMachine.program_length];omega)]
  simp only [List.length_map,UniformNewtonTableMachine.program_length,Nat.add_sub_cancel_left]
  interval_cases i <;> rfl

theorem complete_reciprocal_code : UniformAssembly.CodeAt program completeProgram 237 268 := by
  intro i hi
  rw [program_length] at hi
  simp only [completeProgram]
  rw [List.getElem?_append_left (by simp [List.length_map,UniformNewtonTableMachine.program_length,
    afterNewtonBlock,adapterBlock,program_length];omega),
    List.getElem?_append_right (by simp [List.length_map,UniformNewtonTableMachine.program_length,
    afterNewtonBlock,adapterBlock])]
  have he:(UniformNewtonTableMachine.program.map (UniformAssembly.relocate 0 229)++
      afterNewtonBlock.map Op.code).length=237:=by
    simp [UniformNewtonTableMachine.program_length,afterNewtonBlock,adapterBlock]
  rw [he,Nat.add_sub_cancel_left]
  simp only [List.getElem?_map]

theorem complete_halt : completeProgram[268]?=some .halt := by
  simp only [completeProgram]
  rw [List.getElem?_append_right (by simp [List.length_map,UniformNewtonTableMachine.program_length,
    afterNewtonBlock,adapterBlock,program_length])]
  simp [UniformNewtonTableMachine.program_length,afterNewtonBlock,adapterBlock,program_length]

theorem afterNewton_peak (r a source B : ℕ) (s : State) (h16:s.natReg 16=r)
    (h17:s.natReg 17=a) (h18:s.natReg 18=source) (hB:a+32*r+source+500 ≤ B) :
    peak afterNewtonBlock s ≤ B := by
  simp [peak,afterNewtonBlock,adapterBlock,Op.peak,Op.apply,writeNat,next,h16,h17,h18]
  omega

theorem afterNewton_registers (r a source : ℕ) (s : State) (h16:s.natReg 16=r)
    (h17:s.natReg 17=a) (h18:s.natReg 18=source) :
    (applyBlock afterNewtonBlock s).natReg 16=r ∧
    (applyBlock afterNewtonBlock s).natReg 17=newtonSource r a ∧
    (applyBlock afterNewtonBlock s).natReg 18=3 ∧
    (applyBlock afterNewtonBlock s).natReg 19=source+1 := by
  simp [applyBlock,afterNewtonBlock,adapterBlock,Op.apply,writeNat,next,h16,h17,h18,
    newtonSource,Nat.mul_comm,Nat.add_assoc]


def completeWordBudget (r a source : ℕ) : ℕ := a+32*r+source+500

theorem completeWordBudget_polynomial (r a source : ℕ) :
    completeWordBudget r a source ≤ 500*(r+a+source+1) := by
  unfold completeWordBudget;omega

def completeRuntime (r : ℕ) : ℕ := 252*r+runtime r+179

theorem completeRuntime_bound (r : ℕ) (hr:0 < r) :
    completeRuntime r ≤ 23*r^2+252*r+189 := by
  have h:=runtime_bound r hr
  unfold completeRuntime
  omega

/-- One literal composed program: the charged Newton row producer/interpreter,
the eight charged address-adapter steps, then the charged reciprocal recurrence.
No PreparedOutputs, NatTable, DAG-admissibility or matrix-action premise remains.
The only field provision is the previously supplied prepared primitive axis root. -/
theorem complete_execution (n : ℕ) (x : Fin n→ℂ) (r a scratch source B : ℕ)
    (omega : ℂ) (bank : Fin 6→Scalar) (s : State) (hr:0 < r)
    (hroot:IsPrimitiveRoot omega r) (hl:UniformNewtonTableMachine.Layout r a scratch source)
    (hpc:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=a)
    (h18:s.natReg 18=source) (h19:s.natReg 19=scratch)
    (hbank:UniformNewtonTableMachine.Bank bank s)
    (haxis:s.scalarHeap source=some (prepared omega))
    (hB:completeWordBudget r a source ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution completeProgram n x B s (completeRuntime r) u ∧
    GPrefix r (source+1) (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    UniformNewtonTableMachine.PreparedOutputs r omega a u ∧
    UniformNewtonTableMachine.Bank bank u ∧ u.scalarHeap source=some (prepared omega) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap ∧
    (∀i,6 ≤ i→(i < a ∨ a+8*r+3 ≤ i)→(i < scratch ∨ scratch+6 ≤ i)→
      (i < source+1 ∨ source+1+r ≤ i)→u.scalarHeap i=s.scalarHeap i) := by
  unfold completeWordBudget at hB
  obtain ⟨v,hv,hvp,hvb,hvo,hvr,hvh,hvother⟩:=UniformNewtonTableMachine.preparation_execution
    n x r a scratch source B omega bank s hr hroot hl hpc h16 h17 h18 h19 hbank haxis
    (by omega) (by have h:=hl.root;omega) hs
  have h16v:v.natReg 16=r:=(UniformNewtonTableMachine.Executes.keeps_nat hv.executes
    (newton_keeps_header 16 (by decide) (by decide))).trans h16
  have h17v:v.natReg 17=a:=(UniformNewtonTableMachine.Executes.keeps_nat hv.executes
    (newton_keeps_header 17 (by decide) (by decide))).trans h17
  have h18v:v.natReg 18=source:=(UniformNewtonTableMachine.Executes.keeps_nat hv.executes
    (newton_keeps_header 18 (by decide) (by decide))).trans h18
  have hn:=UniformBoundedAssembly.boundedExecution_placed complete_newton_code
    (by rw [UniformNewtonTableMachine.program_length];omega :
      0+UniformNewtonTableMachine.program.length ≤ B) (by omega : 229 ≤ B) hv
  have hplaced:UniformAssembly.placed 0 s=s:=by simp [UniformAssembly.placed]
  rw [hplaced] at hn
  let w:State:={v with pc:=229}
  have hz:=block_runs afterNewtonBlock completeProgram 229 n B x w afterNewton_at rfl
    hn.final_bound (by change 229+8 ≤ B;omega)
    (by simp [readable,afterNewtonBlock,adapterBlock,Op.readable])
    (afterNewton_peak r a source B w h16v h17v h18v hB)
  let z:=applyBlock afterNewtonBlock w
  let t:State:={z with pc:=0}
  have htp:UniformNewtonTableMachine.PreparedOutputs r omega a t:=hvp
  obtain ⟨hr',ha',hstride,hg⟩:=afterNewton_registers r a source w h16v h17v h18v
  have htb:WordBound B t:=changePC_bound B z 0 hz.final_bound (by omega)
  have hdis:a+8*r+3 ≤ source+1:=by have h1:=hl.afterResults;have h2:=hl.root;omega
  obtain ⟨u,hu,hgu,hhu,hfu,hou⟩:=newton_execution n x r a (source+1) B omega t hr htp
    hdis rfl hr' ha' hstride hg (by unfold newtonSource;omega) htb
  have he:=UniformBoundedAssembly.boundedExecution_placed complete_reciprocal_code
    (by rw [program_length];omega : 237+program.length ≤ B) (by omega : 268 ≤ B) hu
  have hpz:z.pc=237:=by rw [applyBlock_pc];rfl
  have hplaced':UniformAssembly.placed 237 t=z:=by
    change {z with pc:=237}=z
    rw [←hpz]
  rw [hplaced'] at he
  have hf:BoundedExecution completeProgram n x B {u with pc:=268} 1 {u with pc:=268}:=
    .halt he.final_bound (by rw [step,complete_halt])
  have hs6:6 ≤ source:=by have h1:=hl.results;have h2:=hl.afterResults;have h3:=hl.root;omega
  have hsres:a+8*r+3 ≤ source:=by have h1:=hl.afterResults;have h2:=hl.root;omega
  have hsrc:u.scalarHeap source=some (prepared omega):=by
    rw [hou source (Or.inl (by omega))]
    exact (hvother source hs6 (Or.inr hsres) (Or.inr hl.root)).trans haxis
  have hpu:UniformNewtonTableMachine.PreparedOutputs r omega a u:=by
    intro j q
    have hi:=((UniformNewton.Preparation.table r).output (finProdFinEquiv (j,q))).isLt
    change _ < UniformNewton.Preparation.inverseCount r r at hi
    rw [UniformNewton.Preparation.inverseCount_formula] at hi
    rw [hou _ (Or.inl (by omega))]
    exact hvp j q
  have hbu:UniformNewtonTableMachine.Bank bank u:=by
    intro j
    rw [hou j.val (Or.inl (by omega))]
    exact hvb j
  refine ⟨{u with pc:=268},?_,hgu,hpu,hbu,hsrc,?_,?_,?_,?_⟩
  · convert hn.executes (hz.executes (he.executes hf)) using 1
    change completeRuntime r=(252*r+170)+(8+(runtime r+1))
    unfold completeRuntime;omega
  · exact hfu.2.1.trans hvo
  · exact hfu.2.2.trans hvr
  · exact hfu.1.trans hvh
  · intro i hi hia his hig
    exact (hou i hig).trans (hvother i hi hia his)


def canonicalWordBudget (r : ℕ) : ℕ := 56*r+519

theorem canonicalWordBudget_polynomial (r : ℕ) : canonicalWordBudget r ≤ 519*(r+1) := by
  unfold canonicalWordBudget;omega

theorem canonical_execution (n : ℕ) (x : Fin n→ℂ) (r : ℕ) (omega : ℂ)
    (bank : Fin 6→Scalar) (s : State) (hr:0 < r) (hroot:IsPrimitiveRoot omega r)
    (hpc:s.pc=0) (h16:s.natReg 16=r)
    (h17:s.natReg 17=UniformNewtonTableMachine.resultBase r)
    (h18:s.natReg 18=UniformNewtonTableMachine.rootAddress r)
    (h19:s.natReg 19=UniformNewtonTableMachine.scratchBase r)
    (hbank:UniformNewtonTableMachine.Bank bank s)
    (haxis:s.scalarHeap (UniformNewtonTableMachine.rootAddress r)=some (prepared omega))
    (hs:WordBound (canonicalWordBudget r) s) : ∃u,
    BoundedExecution completeProgram n x (canonicalWordBudget r) s (completeRuntime r) u ∧
    GPrefix r (16*r+15) (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    UniformNewtonTableMachine.PreparedOutputs r omega (8*r+5) u ∧
    UniformNewtonTableMachine.Bank bank u ∧
    u.scalarHeap (16*r+14)=some (prepared omega) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r (8*r+5))) s.natHeap ∧
    (∀i,6 ≤ i→(i < 8*r+5 ∨ 16*r+8 ≤ i)→(i < 16*r+8 ∨ 16*r+14 ≤ i)→
      (i < 16*r+15 ∨ 17*r+15 ≤ i)→u.scalarHeap i=s.scalarHeap i) := by
  have h:=complete_execution n x r (UniformNewtonTableMachine.resultBase r)
    (UniformNewtonTableMachine.scratchBase r) (UniformNewtonTableMachine.rootAddress r)
    (canonicalWordBudget r) omega bank s hr hroot (UniformNewtonTableMachine.canonical_layout r)
    hpc h16 h17 h18 h19 hbank haxis
    (by unfold completeWordBudget canonicalWordBudget UniformNewtonTableMachine.resultBase UniformNewtonTableMachine.rootAddress;omega) hs
  have e1:8*r+5+8*r+3=16*r+8:=by omega
  have e2:16*r+8+6=16*r+14:=by omega
  have e3:16*r+14+1=16*r+15:=by omega
  have e4:16*r+14+1+r=17*r+15:=by omega
  simpa only [UniformNewtonTableMachine.resultBase,UniformNewtonTableMachine.scratchBase,
    UniformNewtonTableMachine.rootAddress,e1,e2,e3,e4] using h

def isRoot : UniformMachine.Instruction→Bool | .root _ _=>true | _=>false
def isInput : UniformMachine.Instruction→Bool | .input _ _=>true | _=>false
def isDivision : UniformMachine.Instruction→Bool | .fieldBinary .div _ _ _=>true | _=>false

theorem program_no_root : program.any isRoot=false := rfl
theorem program_no_input : program.any isInput=false := rfl
theorem program_one_division : program.countP isDivision=1 := rfl

end
end ExactFourierCircuits.UniformReciprocalMachine
