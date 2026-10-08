import UniformOffsetLinearMachine
import UniformDAGLowering

set_option autoImplicit false

namespace ExactFourierCircuits.UniformOffsetPreparationMachine
open UniformMachine UniformOffsetLinearMachine
open UniformPreparationMachine (Row opcode)

/-- Nat0 count, Nat9 result base, Nat137 row base. Literal32 bytecode;
Nat1..9 and Scalar0..2 are scratch. Fresh leaf banks are explicit below. -/
def program : Program := [
  .natLiteral 2 1,.natLiteral 3 3,.natLiteral 1 0,
  .branchLT 1 0 4 31,.natBinary .mul 4 1 3,.natBinary .add 4 4 137,.loadNat 5 4,
  .natBinary .add 4 4 2,.loadNat 6 4,.natBinary .add 4 4 2,.loadNat 7 4,
  .loadScalar 0 6,.loadScalar 1 7,.natLiteral 8 1,.branchLT 5 8 15 17,
  .fieldBinary .add 2 0 1,.jump 27,.natLiteral 8 2,.branchLT 5 8 19 21,
  .fieldBinary .sub 2 0 1,.jump 27,.natLiteral 8 3,.branchLT 5 8 23 25,
  .fieldBinary .mul 2 0 1,.jump 27,.fieldBinary .div 2 0 1,.jump 27,
  .storeScalar 9 2,.natBinary .add 9 9 2,.natBinary .add 1 1 2,.jump 3,.halt]

theorem program_length : program.length=32 := rfl
theorem program_eq : program=UniformOffsetLinearMachine.program := rfl

abbrev DProgram := UniformScalarPreparation.Program
abbrev DInstruction := UniformScalarPreparation.Instruction

/-- A leaf is copied by adding prepared zero at fresh address b. Binary
    operands refer directly to prior stored results, preserving DAG sharing. -/
def lowerInstruction {r j : ℕ} (b a : ℕ) : DInstruction r j → Row
  | .rational _ => ⟨.add, b + 1 + r + j, b⟩
  | .root i => ⟨.add, b + 1 + i.val, b⟩
  | .add l q => ⟨.add, a + l.val, a + q.val⟩
  | .sub l q => ⟨.sub, a + l.val, a + q.val⟩
  | .mul l q => ⟨.mul, a + l.val, a + q.val⟩
  | .divide l q => ⟨.div, a + l.val, a + q.val⟩

def compile {r : ℕ} : {k : ℕ} → DProgram r k → ℕ → ℕ → List Row
  | 0, .nil, _, _ => []
  | _ + 1, .step p i, b, a => compile p b a ++ [lowerInstruction b a i]

/-- Cons accumulation avoids repeatedly copying a growing prefix. -/
def compileReverse {r : ℕ} : {k : ℕ} → DProgram r k → ℕ → ℕ → List Row
  | 0, .nil, _, _ => []
  | _ + 1, .step p i, b, a => lowerInstruction b a i :: compileReverse p b a

def compileLinear {r k : ℕ} (p : DProgram r k) (b a : ℕ) : List Row :=
  (compileReverse p b a).reverse

theorem compileLinear_eq {r k : ℕ} (p : DProgram r k) (b a : ℕ) :
    compileLinear p b a = compile p b a := by
  induction p with
  | nil => rfl
  | step p i ih =>
    change (lowerInstruction b a i :: compileReverse p b a).reverse = compile p b a ++ [lowerInstruction b a i]
    rw [List.reverse_cons]
    exact congrArg (fun rows => rows ++ [lowerInstruction b a i]) ih

def bytecode : List Row → List ℕ
  | [] => []
  | row :: rows => opcode row.op :: row.left :: row.right :: bytecode rows

theorem bytecode_length (rows : List Row) : (bytecode rows).length = 3 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [bytecode, ih]; omega

theorem bytecode_get (rows : List Row) (j : ℕ) (row : Row) (h : rows[j]? = some row) :
    (bytecode rows)[3 * j]? = some (opcode row.op) ∧
    (bytecode rows)[3 * j + 1]? = some row.left ∧
    (bytecode rows)[3 * j + 2]? = some row.right := by
  induction rows generalizing j with
  | nil => simp at h
  | cons first rows ih =>
    cases j with
    | zero => simp at h; subst row; exact ⟨rfl, rfl, rfl⟩
    | succ j =>
      have ht : rows[j]? = some row := by simpa using h
      simpa [bytecode, Nat.mul_succ, Nat.add_assoc] using ih j ht

theorem compile_length {r k : ℕ} (p : DProgram r k) (b a : ℕ) : (compile p b a).length = k := by
  induction p with
  | nil => rfl
  | step p i ih => simp [compile, ih]

theorem compile_prefix_get {r k : ℕ} (p : DProgram r k) (i : DInstruction r k)
    (b a j : ℕ) (hj : j < k) : (compile (.step p i) b a)[j]? = (compile p b a)[j]? := by
  exact List.getElem?_append_left (by simpa [compile_length] using hj)

theorem compile_last_get {r k : ℕ} (p : DProgram r k) (i : DInstruction r k) (b a : ℕ) :
    (compile (.step p i) b a)[k]? = some (lowerInstruction b a i) := by
  calc
    (compile (.step p i) b a)[k]? = (compile (.step p i) b a)[(compile p b a).length]? :=
      congrArg (fun j => (compile (.step p i) b a)[j]?) (compile_length p b a).symm
    _ = some (lowerInstruction b a i) := List.getElem?_concat_length

noncomputable section

def NatTable (rows : List Row) (d : ℕ) (s : State) : Prop :=
  ∀ j row, rows[j]? = some row →
    s.natHeap (d + 3 * j) = some (opcode row.op) ∧
    s.natHeap (d + 3 * j + 1) = some row.left ∧ s.natHeap (d + 3 * j + 2) = some row.right

/-- Only the actual table prefix is required; metadata outside it is arbitrary. -/
theorem bytecode_natTable (rows : List Row) (d : ℕ) (s : State)
    (h:∀i,i<(bytecode rows).length→s.natHeap (d+i)=(bytecode rows)[i]?) : NatTable rows d s := by
  intro j row hj
  have hjl:j<rows.length:=(List.getElem?_eq_some_iff.mp hj).choose
  have hb:=bytecode_get rows j row hj
  rw [show d+3*j+1=d+(3*j+1) by omega,show d+3*j+2=d+(3*j+2) by omega]
  rw [h _ (by rw [bytecode_length];omega),h _ (by rw [bytecode_length];omega),h _ (by rw [bytecode_length];omega)]
  exact hb

def RootsReady {r : ℕ} (b : ℕ) (roots : Fin r → ℂ) (s : State) : Prop :=
  s.scalarHeap b = some ⟨0, false⟩ ∧
    ∀ j : Fin r, s.scalarHeap (b + 1 + j.val) = some ⟨roots j, false⟩

def LiteralReady {r j : ℕ} (b : ℕ) (i : DInstruction r j) (s : State) : Prop :=
  match i with
  | .rational q => s.scalarHeap (b + 1 + r + j) = some ⟨(q : ℂ), false⟩
  | _ => True

def LiteralsReady {r : ℕ} : {k : ℕ} → DProgram r k → ℕ → State → Prop
  | 0, .nil, _, _ => True
  | _ + 1, .step p i, b, s => LiteralsReady p b s ∧ LiteralReady b i s

def BaseHeap (a : ℕ) (s u : State) : Prop := ∀ j, j < a → u.scalarHeap j = s.scalarHeap j

def Values {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ) (a : ℕ) (s : State) : Prop :=
  ∀ j : Fin k, s.scalarHeap (a + j.val) = some ⟨p.eval roots j, false⟩

def Registers (K a d j : ℕ) (s : State) : Prop :=
  s.pc = 3 ∧ s.natReg 0 = K ∧ s.natReg 1 = j ∧ s.natReg 2 = 1 ∧
    s.natReg 3 = 3 ∧ s.natReg 9 = a + j ∧ s.natReg 137=d

theorem schedule_append {xs ys : List Row} {s u v : State}
    (hx : ValidSchedule xs s u) (hy : ValidSchedule ys u v) : ValidSchedule (xs ++ ys) s v := by
  induction hx with
  | nil _ => exact hy
  | cons hr _ ih => exact .cons hr (ih hy)

theorem instruction_operands {r k K : ℕ} (p : DProgram r k) (i : DInstruction r k)
    (roots : Fin r → ℂ) (b a : ℕ) (s u : State) (hk : k < K) (ha : b + r + K + 1 ≤ a)
    (hroots : RootsReady b roots s) (hliteral : LiteralReady b i s)
    (hbase : BaseHeap a s u) (hvalues : Values p roots a u)
    (hvalid : i.Admissible (p.eval roots)) : ∃ l q : Scalar,
    u.scalarHeap (lowerInstruction b a i).left = some l ∧
    u.scalarHeap (lowerInstruction b a i).right = some q ∧
    l.dependent = false ∧ q.dependent = false ∧
    evalField (lowerInstruction b a i).op l q = some ⟨i.eval roots (p.eval roots), false⟩ := by
  cases i with
  | rational q =>
    refine ⟨⟨(q : ℂ), false⟩, ⟨0, false⟩, ?_, ?_, rfl, rfl, ?_⟩
    · change u.scalarHeap (b + 1 + r + k) = _
      rw [hbase _ (by omega)]
      exact hliteral
    · change u.scalarHeap b = _
      rw [hbase b (by omega)]
      exact hroots.1
    · simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]
  | root j =>
    refine ⟨⟨roots j, false⟩, ⟨0, false⟩, ?_, ?_, rfl, rfl, ?_⟩
    · change u.scalarHeap (b + 1 + j.val) = _
      rw [hbase _ (by omega)]
      exact hroots.2 j
    · change u.scalarHeap b = _
      rw [hbase b (by omega)]
      exact hroots.1
    · simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]
  | add l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | sub l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | mul l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval]⟩
  | divide l q =>
    exact ⟨⟨p.eval roots l, false⟩, ⟨p.eval roots q, false⟩, hvalues l, hvalues q, rfl, rfl,
      by simp [lowerInstruction, evalField, UniformScalarPreparation.Instruction.eval,
        UniformScalarPreparation.Instruction.Admissible] at hvalid ⊢; exact hvalid⟩

theorem natTable_prefix {r k : ℕ} (p : DProgram r k) (i : DInstruction r k) (b a : ℕ)
    (d : ℕ) (s : State) (h : NatTable (compile (.step p i) b a) d s) : NatTable (compile p b a) d s := by
  intro j row hj
  have hidx : j < k := by
    simpa [compile_length] using (List.getElem?_eq_some_iff.1 hj).choose
  apply h j row
  rw [compile_prefix_get p i b a j hidx]
  exact hj

/-- The typed DAG constructs local row validity, including actual guarded
prepared division. No schedule or result-bank action is assumed. -/
theorem compile_valid {r k : ℕ} (p : DProgram r k) (roots : Fin r→ℂ)
    (K b a d : ℕ) (s : State) (hsize:k≤K) (ha:b+r+K+1≤a)
    (hregs:Registers K a d 0 s) (hroots:RootsReady b roots s)
    (hliterals:LiteralsReady p b s) (htable:NatTable (compile p b a) d s)
    (hvalid:p.Admissible roots) : ∃u:State,
    ValidSchedule (compile p b a) s u ∧ Registers K a d k u ∧
      Values p roots a u ∧ BaseHeap a s u := by
  induction p generalizing K a s with
  | nil=>
    refine ⟨s,.nil _,hregs,?_,fun _ _=>rfl⟩
    intro j;exact Fin.elim0 j
  | @step j p i ih=>
    obtain ⟨v,hv,hregv,hvalues,hbase⟩:=ih K a s (by omega) ha hregs hroots hliterals.1
      (natTable_prefix p i b a d s htable) hvalid.1
    obtain ⟨l,q,hl,hq,_hld,_hqd,heval⟩:=instruction_operands p i roots b a s v (by omega) ha
      hroots hliterals.2 hbase hvalues hvalid.2
    let row:=lowerInstruction b a i
    let value:Scalar:=⟨i.eval roots (p.eval roots),false⟩
    let u:=rowEnd row v l q value
    obtain ⟨hop,hleft,hright⟩:=htable j row (compile_last_get p i b a)
    have hnatheap:v.natHeap=s.natHeap:=hv.counters.2.2.2.1
    obtain ⟨hpv,hKv,hjv,honev,hthreev,hadrv,hdv⟩:=hregv
    have hready:Ready row v l q value:=by
      refine ⟨hpv,?_,honev,hthreev,?_,?_,?_,hl,hq,heval⟩
      · omega
      · simpa only [hjv,hdv,hnatheap] using hop
      · simpa only [hjv,hdv,hnatheap] using hleft
      · simpa only [hjv,hdv,hnatheap] using hright
    have htail:ValidSchedule [row] v u:=.cons hready (.nil u)
    have hall:ValidSchedule (compile (.step p i) b a) s u:=by
      simpa only [compile] using schedule_append hv htail
    obtain ⟨hpcu,hKu,hju,honeu,hthreeu,hadru,_,hheap,_,_⟩:=row_frame row v l q value
    have hdu:u.natReg 137=d:=((row_full_frame row v l q value).2.2.2.1 137 (by omega)).trans hdv
    refine ⟨u,hall,?_,?_,?_⟩
    · refine ⟨hpcu,hKu.trans hKv,?_,honeu.trans honev,hthreeu.trans hthreev,?_,hdu⟩
      · simpa only [hjv] using hju
      · simpa only [hadrv,Nat.add_assoc] using hadru
    · intro index
      refine Fin.lastCases ?_ (fun index=>?_) index
      · simp only [UniformScalarPreparation.Program.eval,Fin.snoc_last]
        change (rowEnd row v l q value).scalarHeap (a+j)=some value
        rw [hheap,hadrv,Function.update_self]
      · simp only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc,Fin.val_castSucc]
        rw [hheap,hadrv,Function.update_of_ne (by have hi:=index.isLt;omega)]
        exact hvalues index
    · intro addr haddr
      rw [hheap,hadrv,Function.update_of_ne (by omega)];exact hbase addr haddr

theorem literals_heap_eq {r k : ℕ} (p : DProgram r k) (b : ℕ) (s u : State)
    (h:u.scalarHeap=s.scalarHeap) : LiteralsReady p b u↔LiteralsReady p b s := by
  induction p with
  | nil=>rfl
  | step p i ih=>
    simp only [LiteralsReady]
    apply and_congr ih
    cases i <;> simp [LiteralReady,h]

theorem instruction_addresses {r j K : ℕ} (i : DInstruction r j) (b a : ℕ)
    (hj:j<K) (ha:b+r+K+1≤a) :
    (lowerInstruction b a i).left<a+j ∧ (lowerInstruction b a i).right<a+j := by
  cases i with
  | rational _=>simp only [lowerInstruction];omega
  | root root=>have hi:=root.isLt;simp only [lowerInstruction];omega
  | add l q | sub l q | mul l q | divide l q=>
    have hl:=l.isLt;have hq:=q.isLt;simp only [lowerInstruction];omega

theorem values_output {r o : ℕ} (dag : UniformScalarPreparation.DAG r o)
    (roots : Fin r→ℂ) (valid:dag.Admissible roots) (a : ℕ) (s : State)
    (h:Values dag.program roots a s) (j : Fin o) :
    s.scalarHeap (a+(dag.output j).val)=some ⟨dag.run roots valid j,false⟩ := h (dag.output j)

/-- Real fixed bytecode executes the shared DAG in linear charged time. Only
leaf and integer-table producer postconditions remain entry premises. -/
theorem interpreted_DAG {r k : ℕ} (p : DProgram r k) (roots : Fin r→ℂ)
    (valid:p.Admissible roots) (n : ℕ) (x : Fin n→ℂ) (b a d B : ℕ) (s : State)
    (hspace:b+r+k+1≤a) (hB:d+4*k+a+42≤B) (hpc:s.pc=0)
    (hk:s.natReg 0=k) (ha:s.natReg 9=a) (hd:s.natReg 137=d) (hb:WordBound B s)
    (hroots:RootsReady b roots s) (hliterals:LiteralsReady p b s)
    (htable:NatTable (compile p b a) d s) : ∃u:State,
    BoundedExecution program n x B s (totalCost (compile p b a)+5) u ∧
      totalCost (compile p b a)+5≤22*k+5 ∧ Values p roots a u ∧ BaseHeap a s u ∧
      Frame s u ∧ Outside a k s.scalarHeap u := by
  have hregs:Registers k a d 0 (initialized s):=by
    simp [Registers,initialized,writeNat,next,hpc,hk,ha,hd]
  have hlit:LiteralsReady p b (initialized s):=(literals_heap_eq p b s (initialized s) rfl).mpr hliterals
  obtain ⟨u,hschedule,_,hvalues,hbase⟩:=compile_valid p roots k b a d (initialized s) (by rfl)
    hspace hregs hroots hlit htable valid
  obtain ⟨hex,hcost,hframe,houtside⟩:=interpreted_schedule_frame n x (compile p b a) a d B s u
    (by simpa only [compile_length] using hB) hpc
    (by simpa only [compile_length] using hk) ha hd hb hschedule
  refine ⟨{u with pc:=31},?_,?_,hvalues,hbase,hframe,?_⟩
  · simpa only [program_eq] using hex
  · simpa only [compile_length] using hcost
  · change Outside a k s.scalarHeap u
    simpa only [compile_length] using houtside

/-- Everything outside the fresh result interval, including old master roots
and high retained pools, is preserved. Nat metadata and saved headers survive. -/
theorem interpreted_DAG_frames {r k : ℕ} (p : DProgram r k) (roots : Fin r→ℂ)
    (valid:p.Admissible roots) (n : ℕ) (x : Fin n→ℂ) (b a d B : ℕ) (s : State)
    (hspace:b+r+k+1≤a) (hB:d+4*k+a+42≤B) (hpc:s.pc=0)
    (hk:s.natReg 0=k) (ha:s.natReg 9=a) (hd:s.natReg 137=d) (hb:WordBound B s)
    (hroots:RootsReady b roots s) (hliterals:LiteralsReady p b s)
    (htable:NatTable (compile p b a) d s) : ∃u:State,
    BoundedExecution program n x B s (totalCost (compile p b a)+5) u ∧
    Values p roots a u ∧ (∀ i, (i < a ∨ a + k ≤ i) → u.scalarHeap i = s.scalarHeap i) ∧
    u.natHeap=s.natHeap ∧ (∀ i, 10 ≤ i → u.natReg i = s.natReg i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
  obtain ⟨u,he,_,hv,_,hf,ho⟩:=interpreted_DAG p roots valid n x b a d B s
    hspace hB hpc hk ha hd hb hroots hliterals htable
  exact ⟨u,he,hv,ho,hf.1,fun i hi=>hf.2.2.2.1 i (by omega),hf.2.1,hf.2.2.1⟩

/-- A packed fresh leaf/result bank at any caller-chosen offset b. Its tables
and prepared leaves still require real producer contracts. -/
theorem interpreted_DAG_packed {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ)
    (valid : p.Admissible roots) (n : ℕ) (x : Fin n → ℂ) (b d B : ℕ) (s : State)
    (hB : d + 5*k + b + r + 43 ≤ B) (hpc : s.pc=0) (hk : s.natReg 0=k)
    (ha : s.natReg 9=b+r+k+1) (hd : s.natReg 137=d) (hb : WordBound B s)
    (hroots : RootsReady b roots s) (hliterals : LiteralsReady p b s)
    (htable : NatTable (compile p b (b+r+k+1)) d s) : ∃u,
    BoundedExecution program n x B s (totalCost (compile p b (b+r+k+1))+5) u ∧
    totalCost (compile p b (b+r+k+1))+5 ≤ 22*k+5 ∧ Values p roots (b+r+k+1) u ∧
    BaseHeap (b+r+k+1) s u ∧ Frame s u ∧ Outside (b+r+k+1) k s.scalarHeap u :=
  interpreted_DAG p roots valid n x b (b+r+k+1) d B s (by rfl) (by omega)
    hpc hk ha hd hb hroots hliterals htable

/-- Empty rows do not load or require any prepared leaf or table bank. -/
theorem empty_execution (n : ℕ) (x : Fin n → ℂ) (a d B : ℕ) (s : State)
    (hB : d+a+42 ≤ B) (hpc : s.pc=0) (hk : s.natReg 0=0)
    (ha : s.natReg 9=a) (hd : s.natReg 137=d) (hb : WordBound B s) :
    BoundedExecution program n x B s 5 {initialized s with pc:=31} ∧
    Frame s {initialized s with pc:=31} ∧
    (∀ i, ({initialized s with pc:=31}:State).scalarHeap i=s.scalarHeap i) := by
  obtain ⟨he,_,hf,_⟩:=interpreted_schedule_frame n x [] a d B s (initialized s)
    (by simpa using hB) hpc hk ha hd hb (.nil _)
  exact ⟨by simpa only [totalCost,List.map_nil,List.sum_nil,Nat.zero_add,program_eq] using he,hf,fun _=>rfl⟩

end
end ExactFourierCircuits.UniformOffsetPreparationMachine
