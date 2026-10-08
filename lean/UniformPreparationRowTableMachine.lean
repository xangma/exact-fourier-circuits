import UniformOffsetPreparationMachine
import UniformNewtonTableMachine
import UniformNatCopyMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformPreparationRowTableMachine
open UniformMachine
open UniformOffsetPreparationMachine (DProgram DInstruction)
open UniformPreparationMachine (Row opcode)
open UniformNewtonTableMachine (putWords putWords_before putWords_after putWords_get)

/-- Actual typed-node tape fields. Tags 0/1 are rational/root leaves; 2..5
are add/sub/mul/div. The rational value has a separate prepared leaf bank. -/
structure Node where
  tag : ℕ
  left : ℕ
  right : ℕ
  deriving DecidableEq

def encodeInstruction {r j : ℕ} : DInstruction r j → Node
  | .rational _ => ⟨0,0,0⟩
  | .root i => ⟨1,i.val,0⟩
  | .add l q => ⟨2,l.val,q.val⟩
  | .sub l q => ⟨3,l.val,q.val⟩
  | .mul l q => ⟨4,l.val,q.val⟩
  | .divide l q => ⟨5,l.val,q.val⟩

def nodes {r : ℕ} : {k : ℕ} → DProgram r k → Fin k → Node
  | 0,.nil => Fin.elim0
  | _+1,.step p i => Fin.snoc (nodes p) (encodeInstruction i)

def Node.Valid (r j : ℕ) (v : Node) : Prop :=
  (v.tag=0 ∧ v.left=0 ∧ v.right=0) ∨
  (v.tag=1 ∧ v.left < r ∧ v.right=0) ∨
  (2 ≤ v.tag ∧ v.tag ≤ 5 ∧ v.left < j ∧ v.right < j)

theorem encode_valid {r j : ℕ} (i : DInstruction r j) : (encodeInstruction i).Valid r j := by
  cases i <;> simp [encodeInstruction,Node.Valid]

theorem nodes_valid {r k : ℕ} (p : DProgram r k) (j : Fin k) : (nodes p j).Valid r j.val := by
  induction p with
  | nil => exact Fin.elim0 j
  | @step k p i ih =>
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simpa [nodes] using encode_valid i
    · simpa [nodes] using ih t

/-- The concrete field relocation computed by the printer. -/
def relocated (r b a j : ℕ) (v : Node) : List ℕ :=
  if v.tag < 1 then [0,b+1+r+j,b]
  else if v.tag < 2 then [0,b+1+v.left,b]
  else [v.tag-2,a+v.left,a+v.right]

theorem relocated_encode {r j : ℕ} (i : DInstruction r j) (b a : ℕ) :
    relocated r b a j (encodeInstruction i) =
      [opcode (UniformOffsetPreparationMachine.lowerInstruction b a i).op,
       (UniformOffsetPreparationMachine.lowerInstruction b a i).left,
       (UniformOffsetPreparationMachine.lowerInstruction b a i).right] := by
  cases i <;> rfl

theorem nodes_compile_get {r k : ℕ} (p : DProgram r k) (b a : ℕ) (j : Fin k) :
    ∃row, (UniformOffsetPreparationMachine.compile p b a)[j.val]?=some row ∧
      relocated r b a j.val (nodes p j)=[opcode row.op,row.left,row.right] := by
  induction p with
  | nil => exact Fin.elim0 j
  | @step k p i ih =>
    refine Fin.lastCases ?_ (fun t => ?_) j
    · exact ⟨_,UniformOffsetPreparationMachine.compile_last_get p i b a,
        by simpa [nodes] using relocated_encode i b a⟩
    · obtain ⟨row,hrow,hr⟩:=ih t
      exact ⟨row,(UniformOffsetPreparationMachine.compile_prefix_get p i b a t.val t.isLt).trans hrow,
        by simpa [nodes] using hr⟩

/-- Nat220=count, 221=tape, 222=destination, 223=leaf base,224=result base,
225=root count. Only Nat240..252 are scratch. No scalar instruction occurs. -/
def program : Program := [
  .natLiteral 241 1,.natLiteral 242 3,.natLiteral 251 2,.natLiteral 252 0,.natLiteral 240 0,
  .branchLT 240 220 6 38,
  .natBinary .mul 243 240 242,.natBinary .add 243 243 221,.loadNat 244 243,
  .natBinary .add 243 243 241,.loadNat 245 243,.natBinary .add 243 243 241,.loadNat 246 243,
  .natBinary .mul 247 240 242,.natBinary .add 247 247 222,
  .branchLT 244 241 16 22,
  .natBinary .add 248 252 252,.natBinary .add 249 223 241,.natBinary .add 249 249 225,
  .natBinary .add 249 249 240,.natBinary .add 250 223 252,.jump 31,
  .branchLT 244 251 23 28,.natBinary .add 248 252 252,.natBinary .add 249 223 241,
  .natBinary .add 249 249 245,.natBinary .add 250 223 252,.jump 31,
  .natBinary .sub 248 244 251,.natBinary .add 249 224 245,.natBinary .add 250 224 246,
  .storeNat 247 248,.natBinary .add 247 247 241,.storeNat 247 249,
  .natBinary .add 247 247 241,.storeNat 247 250,.natBinary .add 240 240 241,.jump 5,.halt]

theorem program_length : program.length=39 := rfl

/-- A fixed-block proof notation; each constructor expands to one original RAM
instruction. Loads require actual heap presence, and stores are charged. -/
inductive Op where
  | literal (d v : ℕ)
  | add (d l r : ℕ)
  | sub (d l r : ℕ)
  | mul (d l r : ℕ)
  | get (d address : ℕ)
  | put (address src : ℕ)
  deriving DecidableEq

def Op.code : Op → Instruction
  | .literal d v => .natLiteral d v
  | .add d l r => .natBinary .add d l r
  | .sub d l r => .natBinary .sub d l r
  | .mul d l r => .natBinary .mul d l r
  | .get d a => .loadNat d a
  | .put a r => .storeNat a r

noncomputable section

def Op.apply (o : Op) (s : State) : State := match o with
  | .literal d v => writeNat s d v
  | .add d l r => writeNat s d (s.natReg l+s.natReg r)
  | .sub d l r => writeNat s d (s.natReg l-s.natReg r)
  | .mul d l r => writeNat s d (s.natReg l*s.natReg r)
  | .get d a => writeNat s d ((s.natHeap (s.natReg a)).getD 0)
  | .put a r => {next s with natHeap:=Function.update s.natHeap (s.natReg a) (some (s.natReg r))}

def Op.readable (o : Op) (s : State) : Prop := match o with
  | .get _ a => (s.natHeap (s.natReg a)).isSome=true
  | _ => True

def Op.peak (o : Op) (s : State) : ℕ := match o with
  | .literal _ v => v
  | .add _ l r => s.natReg l+s.natReg r
  | .sub _ l r => s.natReg l-s.natReg r
  | .mul _ l r => s.natReg l*s.natReg r
  | .get _ a => (s.natHeap (s.natReg a)).getD 0
  | .put a r => max (s.natReg a) (s.natReg r)

def applyBlock : List Op → State → State
  | [],s => s
  | o::os,s => applyBlock os (o.apply s)
def readable : List Op → State → Prop
  | [],_ => True
  | o::os,s => o.readable s ∧ readable os (o.apply s)
def peak : List Op → State → ℕ
  | [],_ => 0
  | o::os,s => max (o.peak s) (peak os (o.apply s))
def BlockAt (os : List Op) (p : Program) (base : ℕ) : Prop :=
  ∀i,(hi:i < os.length) → p[base+i]?=some (os[i]'hi).code

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl

theorem Op.step (o : Op) (p : Program) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hc:p[s.pc]?=some o.code) (hr:o.readable s) : step p n x s=.running (o.apply s) := by
  cases o <;> simp [UniformMachine.step,hc,Op.code,Op.apply,evalNat]
  case get d a =>
    cases hh:s.natHeap (s.natReg a) with
    | none => simp [Op.readable,hh] at hr
    | some v => simp

theorem Op.apply_bound (o : Op) (B : ℕ) (s : State) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (hk:o.peak s ≤ B) : WordBound B (o.apply s) := by
  cases o with
  | literal d v => exact writeNat_bound B s d v hs hp hk
  | add d l r => exact writeNat_bound B s d _ hs hp hk
  | sub d l r => exact writeNat_bound B s d _ hs hp hk
  | mul d l r => exact writeNat_bound B s d _ hs hp hk
  | get d a => exact writeNat_bound B s d _ hs hp hk
  | put a r =>
    exact UniformNatCopyMachine.store_bound B s _ _ hs hp
      ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk)

theorem block_runs (os : List Op) (p : Program) (base n B : ℕ) (x : Fin n → ℂ)
    (s : State) (hc:BlockAt os p base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+os.length ≤ B) (hr:readable os s) (hk:peak os s ≤ B) :
    BoundedRuns p n x B s os.length (applyBlock os s) := by
  induction os generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have h1:s.pc+1 ≤ B:=by simp only [List.length_cons] at hb;omega
    have hnext:=o.apply_bound B s hs h1 ((le_max_left _ _).trans hk)
    have ht:BlockAt os p (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change p[base+(i+1)]?=some (os[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have htail:=ih (base+1) (o.apply s) ht (by rw [Op.apply_pc,hp]) hnext
      (by simp only [List.length_cons] at hb;omega) hr.2 ((le_max_right _ _).trans hk)
    have hf:=hc 0 (by simp)
    change p[base]?=some o.code at hf
    exact .next hs (o.step p n x s (by simpa [hp] using hf) hr.1) htail

theorem applyBlock_pc (os : List Op) (s : State) : (applyBlock os s).pc=s.pc+os.length := by
  induction os generalizing s with
  | nil => simp [applyBlock]
  | cons o os ih => simp [applyBlock,ih,Op.apply_pc];omega

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀ i, (i < 240 ∨ 252 < i) → u.natReg i = s.natReg i

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,fun i hi=>(h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩

def Op.scratch : Op → ℕ
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .get d _ => d
  | .put _ _ => 240

theorem applyBlock_frame (os : List Op) (s : State)
    (h:∀o∈os,240 ≤ o.scratch ∧ o.scratch ≤ 252) : Frame s (applyBlock os s) := by
  induction os generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
  | cons o os ih =>
    have ho:=h o (by simp)
    have ht:=ih (o.apply s) (fun t ht=>h t (by simp [ht]))
    apply Frame.trans (u:=o.apply s) ?_ ht
    refine ⟨?_,?_,?_,?_,?_⟩
    · cases o <;> rfl
    · cases o <;> rfl
    · cases o <;> rfl
    · cases o <;> rfl
    · intro i hi
      have hne:i≠o.scratch:=by omega
      cases o <;> simp_all [Op.apply,Op.scratch,writeNat,next]


def Header (k c d b a r : ℕ) (s : State) : Prop :=
  s.natReg 220=k ∧ s.natReg 221=c ∧ s.natReg 222=d ∧ s.natReg 223=b ∧
  s.natReg 224=a ∧ s.natReg 225=r

structure Counters (k c d b a r j : ℕ) (s : State) : Prop where
  header : Header k c d b a r s
  index : s.natReg 240=j
  one : s.natReg 241=1
  three : s.natReg 242=3
  two : s.natReg 251=2
  zero : s.natReg 252=0

def Tape {k : ℕ} (vs : Fin k → Node) (c : ℕ) (heap : ℕ → Option ℕ) : Prop :=
  ∀j:Fin k,heap (c+3*j.val)=some (vs j).tag ∧
    heap (c+3*j.val+1)=some (vs j).left ∧ heap (c+3*j.val+2)=some (vs j).right

def Disjoint (k c d : ℕ) : Prop := c+3*k ≤ d ∨ d+3*k ≤ c

def Outside (k d : ℕ) (heap : ℕ → Option ℕ) (s : State) : Prop :=
  ∀i,(i < d ∨ d+3*k ≤ i) → s.natHeap i=heap i

structure Invariant {k : ℕ} (vs : Fin k → Node) (c d b a r j : ℕ)
    (heap : ℕ → Option ℕ) (s : State) : Prop where
  counters : Counters k c d b a r j s
  copied : ∀t:Fin k,t.val < j →
    s.natHeap (d+3*t.val)=some ((relocated r b a t.val (vs t))[0]!) ∧
    s.natHeap (d+3*t.val+1)=some ((relocated r b a t.val (vs t))[1]!) ∧
    s.natHeap (d+3*t.val+2)=some ((relocated r b a t.val (vs t))[2]!)
  outside : Outside k d heap s

theorem Counters.withPC {k c d b a r j pc : ℕ} {s : State}
    (h:Counters k c d b a r j s) : Counters k c d b a r j {s with pc:=pc} := by
  cases h;constructor <;> assumption

theorem Invariant.withPC {k c d b a r j pc : ℕ} {vs : Fin k → Node}
    {heap : ℕ → Option ℕ} {s : State} (h:Invariant vs c d b a r j heap s) :
    Invariant vs c d b a r j heap {s with pc:=pc} := by
  exact ⟨h.counters.withPC,h.copied,h.outside⟩

theorem Frame.withPC (s : State) (pc : ℕ) : Frame s {s with pc:=pc} :=
  ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

def boot : List Op := [.literal 241 1,.literal 242 3,.literal 251 2,
  .literal 252 0,.literal 240 0]
def reads : List Op := [.mul 243 240 242,.add 243 243 221,.get 244 243,
  .add 243 243 241,.get 245 243,.add 243 243 241,.get 246 243,
  .mul 247 240 242,.add 247 247 222]
def rationalFields : List Op := [.add 248 252 252,.add 249 223 241,
  .add 249 249 225,.add 249 249 240,.add 250 223 252]
def rootFields : List Op := [.add 248 252 252,.add 249 223 241,
  .add 249 249 245,.add 250 223 252]
def binaryFields : List Op := [.sub 248 244 251,.add 249 224 245,.add 250 224 246]
def stores : List Op := [.put 247 248,.add 247 247 241,.put 247 249,
  .add 247 247 241,.put 247 250,.add 240 240 241]

theorem boot_code : BlockAt boot program 0 := by
  intro i hi; change i < 5 at hi; interval_cases i <;> rfl
theorem reads_code : BlockAt reads program 6 := by
  intro i hi; change i < 9 at hi; interval_cases i <;> rfl
theorem rationalFields_code : BlockAt rationalFields program 16 := by
  intro i hi; change i < 5 at hi; interval_cases i <;> rfl
theorem rootFields_code : BlockAt rootFields program 23 := by
  intro i hi; change i < 4 at hi; interval_cases i <;> rfl
theorem binaryFields_code : BlockAt binaryFields program 28 := by
  intro i hi; change i < 3 at hi; interval_cases i <;> rfl
theorem stores_code : BlockAt stores program 31 := by
  intro i hi; change i < 6 at hi; interval_cases i <;> rfl

def nodeNat {k : ℕ} (vs : Fin k → Node) (j : ℕ) : Node :=
  if h:j < k then vs ⟨j,h⟩ else ⟨0,0,0⟩
def rowCost (v : Node) : ℕ := if v.tag < 2 then 24 else 22
def rangeCost {k : ℕ} (vs : Fin k → Node) : ℕ → ℕ → ℕ
  | _,0=>0
  | j,f+1=>rowCost (nodeNat vs j)+rangeCost vs (j+1) f

theorem rowCost_le (v : Node) : rowCost v ≤ 24 := by simp [rowCost];split_ifs <;> omega

theorem rangeCost_le {k : ℕ} (vs : Fin k → Node) (j f : ℕ) : rangeCost vs j f ≤ 24*f := by
  induction f generalizing j with
  | zero=>rfl
  | succ f ih=>
    simp only [rangeCost]
    have h:=rowCost_le (nodeNat vs j)
    have ht:=ih (j+1)
    omega

structure ReadReady (k c d b a r j : ℕ) (v : Node) (s : State) : Prop where
  counters : Counters k c d b a r j s
  tag : s.natReg 244=v.tag
  left : s.natReg 245=v.left
  right : s.natReg 246=v.right
  pointer : s.natReg 247=d+3*j

structure RowReady (k c d b a r j : ℕ) (v : Node) (s : State) : Prop where
  counters : Counters k c d b a r j s
  pointer : s.natReg 247=d+3*j
  tag : s.natReg 248=(relocated r b a j v)[0]!
  left : s.natReg 249=(relocated r b a j v)[1]!
  right : s.natReg 250=(relocated r b a j v)[2]!

/-- Every source field is still present even when the fresh destination lies
before the tape. No zero-tail premise is used. -/
theorem tape_preserved {k : ℕ} (vs : Fin k → Node) (c d b a r j : ℕ)
    (heap : ℕ → Option ℕ) (s : State) (hi:Invariant vs c d b a r j heap s)
    (ht:Tape vs c heap) (hd:Disjoint k c d) : Tape vs c s.natHeap := by
  intro t
  have h0:(c+3*t.val < d ∨ d+3*k ≤ c+3*t.val):=by
    rcases hd with hd|hd
    · left;have hh:=t.isLt;omega
    · right;omega
  have h1:(c+3*t.val+1 < d ∨ d+3*k ≤ c+3*t.val+1):=by
    rcases hd with hd|hd
    · left;have hh:=t.isLt;omega
    · right;omega
  have h2:(c+3*t.val+2 < d ∨ d+3*k ≤ c+3*t.val+2):=by
    rcases hd with hd|hd
    · left;have hh:=t.isLt;omega
    · right;omega
  rw [hi.outside _ h0,hi.outside _ h1,hi.outside _ h2]
  exact ht t

theorem reads_semantics (k c d b a r j : ℕ) (v : Node) (s : State)
    (hc:Counters k c d b a r j s)
    (h0:s.natHeap (c+3*j)=some v.tag)
    (h1:s.natHeap (c+3*j+1)=some v.left)
    (h2:s.natHeap (c+3*j+2)=some v.right) :
    ReadReady k c d b a r j v (applyBlock reads s) ∧
    (applyBlock reads s).natHeap=s.natHeap ∧ readable reads s := by
  obtain ⟨hh,hj,ho,hth,ht,hz⟩:=hc
  obtain ⟨hk,hc,hd,hb,ha,hr⟩:=hh
  have h0':s.natHeap (j*3+c)=some v.tag:=by rw [show j*3+c=c+3*j by omega];exact h0
  have h1':s.natHeap (j*3+c+1)=some v.left:=by rw [show j*3+c+1=c+3*j+1 by omega];exact h1
  have h2':s.natHeap (j*3+c+1+1)=some v.right:=by rw [show j*3+c+1+1=c+3*j+2 by omega];exact h2
  refine ⟨?_,rfl,?_⟩
  · constructor
    · constructor
      · simpa [Header,applyBlock,reads,Op.apply,writeNat,next] using ⟨hk,hc,hd,hb,ha,hr⟩
      all_goals simp [applyBlock,reads,Op.apply,writeNat,next,hj,ho,hth,ht,hz]
    all_goals simp [applyBlock,reads,Op.apply,writeNat,next,hj,ho,hth,hc,hd,h0',h1',h2']
    omega
  · simp [readable,reads,Op.readable,Op.apply,writeNat,next,hj,ho,hth,hc,h0',h1',h2']

theorem reads_peak (k c d b a r j B : ℕ) (v : Node) (s : State)
    (hc:Counters k c d b a r j s) (hv:v.Valid r j) (hj:j < k)
    (hB:c+d+b+a+r+4*k+80 ≤ B)
    (h0:s.natHeap (c+3*j)=some v.tag)
    (h1:s.natHeap (c+3*j+1)=some v.left)
    (h2:s.natHeap (c+3*j+2)=some v.right) : peak reads s ≤ B := by
  obtain ⟨hh,hi,ho,hth,ht,hz⟩:=hc
  obtain ⟨hk,hc,hd,hb,ha,hr⟩:=hh
  have h0':s.natHeap (j*3+c)=some v.tag:=by rw [show j*3+c=c+3*j by omega];exact h0
  have h1':s.natHeap (j*3+c+1)=some v.left:=by rw [show j*3+c+1=c+3*j+1 by omega];exact h1
  have h2':s.natHeap (j*3+c+1+1)=some v.right:=by rw [show j*3+c+1+1=c+3*j+2 by omega];exact h2
  simp [peak,reads,Op.peak,Op.apply,writeNat,next,
    hi,ho,hth,hc,hd,h0',h1',h2']
  rcases hv with hv|hv|hv <;> omega


theorem relocated_length (r b a j : ℕ) (v : Node) : (relocated r b a j v).length=3 := by
  unfold relocated;split_ifs <;> rfl

theorem relocated_eta (r b a j : ℕ) (v : Node) :
    relocated r b a j v=[(relocated r b a j v)[0]!,
      (relocated r b a j v)[1]!,(relocated r b a j v)[2]!] := by
  unfold relocated;split_ifs <;> rfl

def fields (v : Node) : List Op :=
  if v.tag < 1 then rationalFields else if v.tag < 2 then rootFields else binaryFields

def fieldsPC (v : Node) : ℕ := if v.tag < 1 then 16 else if v.tag < 2 then 23 else 28

theorem fields_code (v : Node) : BlockAt (fields v) program (fieldsPC v) := by
  unfold fields fieldsPC
  split_ifs
  · exact rationalFields_code
  · exact rootFields_code
  · exact binaryFields_code

theorem fields_semantics (k c d b a r j : ℕ) (v : Node) (s : State)
    (hr:ReadReady k c d b a r j v s) :
    RowReady k c d b a r j v (applyBlock (fields v) s) ∧
    (applyBlock (fields v) s).natHeap=s.natHeap ∧ readable (fields v) s := by
  obtain ⟨hc,htag,hl,hq,hp⟩:=hr
  obtain ⟨hh,hj,ho,hth,ht,hz⟩:=hc
  obtain ⟨hk,hc,hd,hb,ha,hr⟩:=hh
  unfold fields
  split_ifs with h1 h2
  all_goals refine ⟨?_,rfl,by simp [readable,rationalFields,rootFields,binaryFields,Op.readable]⟩
  all_goals constructor
  all_goals first
    | (constructor
       · simpa [Header,applyBlock,rationalFields,rootFields,binaryFields,Op.apply,writeNat,next] using
           ⟨hk,hc,hd,hb,ha,hr⟩
       all_goals simp [applyBlock,rationalFields,rootFields,binaryFields,Op.apply,writeNat,next,hj,ho,hth,ht,hz])
    | simp_all [applyBlock,rationalFields,rootFields,binaryFields,Op.apply,writeNat,next,relocated]
  all_goals split_ifs <;> simp_all
  all_goals omega

theorem fields_peak (k c d b a r j B : ℕ) (v : Node) (s : State)
    (hr:ReadReady k c d b a r j v s) (hv:v.Valid r j) (hj:j < k)
    (hB:c+d+b+a+r+4*k+80 ≤ B) : peak (fields v) s ≤ B := by
  obtain ⟨hc,htag,hl,hq,hp⟩:=hr
  obtain ⟨hh,hi,ho,hth,ht,hz⟩:=hc
  obtain ⟨hk,hc,hd,hb,ha,hr⟩:=hh
  unfold fields
  split_ifs
  all_goals simp [peak,rationalFields,rootFields,binaryFields,Op.peak,Op.apply,writeNat,next,
    htag,hl,hq,hb,ha,hr,hi,ho,ht,hz]
  all_goals rcases hv with hv|hv|hv <;> omega

theorem fields_frame (v : Node) (s : State) : Frame s (applyBlock (fields v) s) := by
  apply applyBlock_frame
  unfold fields;split_ifs
  all_goals intro o ho
  all_goals simp [rationalFields,rootFields,binaryFields] at ho
  all_goals rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp [Op.scratch]

theorem reads_frame (s : State) : Frame s (applyBlock reads s) := by
  apply applyBlock_frame
  intro o ho
  simp [reads] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Op.scratch]

theorem stores_frame (s : State) : Frame s (applyBlock stores s) := by
  apply applyBlock_frame
  intro o ho
  simp [stores] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Op.scratch]

theorem relocated_bounds (r b a j k B : ℕ) (v : Node) (hv:v.Valid r j) (hj:j < k)
    (hB:b+a+r+4*k+80 ≤ B) :
    (relocated r b a j v)[0]! ≤ B ∧ (relocated r b a j v)[1]! ≤ B ∧
    (relocated r b a j v)[2]! ≤ B := by
  unfold relocated;split_ifs
  all_goals simp
  all_goals rcases hv with hv|hv|hv <;> omega

theorem stores_peak (k c d b a r j B : ℕ) (v : Node) (s : State)
    (hr:RowReady k c d b a r j v s) (hv:v.Valid r j) (hj:j < k)
    (hB:c+d+b+a+r+4*k+80 ≤ B) : peak stores s ≤ B := by
  obtain ⟨hc,hp,h0,h1,h2⟩:=hr
  obtain ⟨hh,hi,ho,hth,ht,hz⟩:=hc
  have hb:=relocated_bounds r b a j k B v hv hj (by omega)
  simp at hb
  simp [peak,stores,Op.peak,Op.apply,writeNat,next,hi,ho,hp,h0,h1,h2]
  omega

theorem stores_semantics (k c d b a r j : ℕ) (v : Node) (s : State)
    (hr:RowReady k c d b a r j v s) :
    Counters k c d b a r (j+1) (applyBlock stores s) ∧
    (applyBlock stores s).natHeap=putWords (d+3*j) (relocated r b a j v) s.natHeap := by
  obtain ⟨hc,hp,h0,h1,h2⟩:=hr
  obtain ⟨hh,hi,ho,hth,ht,hz⟩:=hc
  refine ⟨?_,?_⟩
  · constructor
    · simpa [Header,applyBlock,stores,Op.apply,writeNat,next] using hh
    all_goals simp [applyBlock,stores,Op.apply,writeNat,next,hi,ho,hth,ht,hz]
  · rw [relocated_eta]
    simp [applyBlock,stores,Op.apply,writeNat,next,putWords,hp,ho,h0,h1,h2]

theorem stores_invariant {k : ℕ} (vs : Fin k → Node) (c d b a r j : ℕ)
    (heap : ℕ → Option ℕ) (s : State) (hi:Invariant vs c d b a r j heap s)
    (hj:j < k) (hr:RowReady k c d b a r j (vs ⟨j,hj⟩) s) :
    Invariant vs c d b a r (j+1) heap (applyBlock stores s) := by
  have hs:=stores_semantics k c d b a r j (vs ⟨j,hj⟩) s hr
  refine ⟨hs.1,?_,?_⟩
  · intro t ht
    rw [hs.2]
    by_cases he:t.val=j
    · have hte:t=⟨j,hj⟩:=Fin.ext he
      subst t
      have h0:=putWords_get (d+3*j) (relocated r b a j (vs ⟨j,hj⟩)) s.natHeap 0
        (by rw [relocated_length];omega)
      have h1:=putWords_get (d+3*j) (relocated r b a j (vs ⟨j,hj⟩)) s.natHeap 1
        (by rw [relocated_length];omega)
      have h2:=putWords_get (d+3*j) (relocated r b a j (vs ⟨j,hj⟩)) s.natHeap 2
        (by rw [relocated_length];omega)
      unfold relocated at h0 h1 h2 ⊢
      split_ifs at h0 h1 h2 ⊢ <;> simpa using ⟨h0,h1,h2⟩
    · have hlt:t.val < j:=by omega
      rw [putWords_before _ _ _ _ (by omega),putWords_before _ _ _ _ (by omega),
        putWords_before _ _ _ _ (by omega)]
      exact hi.copied t hlt
  · intro i hi'
    rw [hs.2]
    rcases hi' with hi'|hi'
    · rw [putWords_before _ _ _ i (by omega)]
      exact hi.outside i (Or.inl hi')
    · rw [putWords_after _ _ _ i (by rw [relocated_length];omega)]
      exact hi.outside i (Or.inr hi')


theorem ReadReady.withPC {k c d b a r j pc : ℕ} {v : Node} {s : State}
    (h:ReadReady k c d b a r j v s) : ReadReady k c d b a r j v {s with pc:=pc} :=
  ⟨h.counters.withPC,h.tag,h.left,h.right,h.pointer⟩

theorem RowReady.withPC {k c d b a r j pc : ℕ} {v : Node} {s : State}
    (h:RowReady k c d b a r j v s) : RowReady k c d b a r j v {s with pc:=pc} :=
  ⟨h.counters.withPC,h.pointer,h.tag,h.left,h.right⟩

theorem control_run (p : Program) (n B pc : ℕ) (x : Fin n → ℂ) (s : State)
    (hs:WordBound B s) (hp:pc ≤ B)
    (h:step p n x s=.running {s with pc:=pc}) :
    BoundedRuns p n x B s 1 {s with pc:=pc} :=
  .next hs h (.refl (changePC_bound B s pc hs hp))

def selectCost (v : Node) : ℕ := if v.tag < 1 then 1 else 2
def postCost (v : Node) : ℕ := if v.tag < 2 then 1 else 0
def fieldCost (v : Node) : ℕ := if v.tag < 2 then 7 else 5

theorem select_fields (n B k c d b a r j : ℕ) (x : Fin n → ℂ) (v : Node) (s : State)
    (hr:ReadReady k c d b a r j v s) (hp:s.pc=15) (hs:WordBound B s)
    (hB:38 ≤ B) : BoundedRuns program n x B s (selectCost v) {s with pc:=fieldsPC v} := by
  by_cases h1:v.tag < 1
  · have he:step program n x s=.running {s with pc:=16}:=by
      simp [step,program,hp,hr.tag,hr.counters.one,h1]
    simpa [selectCost,fieldsPC,h1] using control_run program n B 16 x s hs (by omega) he
  · have he:step program n x s=.running {s with pc:=22}:=by
      simp [step,program,hp,hr.tag,hr.counters.one,h1]
    have hf:=control_run program n B 22 x s hs (by omega) he
    by_cases h2:v.tag < 2
    · have ht:step program n x {s with pc:=22}=.running {s with pc:=23}:=by
        simp [step,program,hr.tag,hr.counters.two,h2]
      have hg:=control_run program n B 23 x {s with pc:=22} hf.final_bound (by omega) ht
      simpa [selectCost,fieldsPC,h1,h2] using hf.trans hg
    · have ht:step program n x {s with pc:=22}=.running {s with pc:=28}:=by
        simp [step,program,hr.tag,hr.counters.two,h2]
      have hg:=control_run program n B 28 x {s with pc:=22} hf.final_bound (by omega) ht
      simpa [selectCost,fieldsPC,h1,h2] using hf.trans hg

theorem post_fields (n B : ℕ) (x : Fin n → ℂ) (v : Node) (s : State)
    (hp:s.pc=fieldsPC v+(fields v).length) (hs:WordBound B s) (hB:38 ≤ B) :
    BoundedRuns program n x B s (postCost v) {s with pc:=31} := by
  by_cases h1:v.tag < 1
  · have hpc:s.pc=21:=by simpa [fieldsPC,fields,rationalFields,h1] using hp
    have ht:step program n x s=.running {s with pc:=31}:=by simp [step,program,hpc]
    have h2:v.tag < 2:=by omega
    simpa [postCost,h2] using control_run program n B 31 x s hs (by omega) ht
  · by_cases h2:v.tag < 2
    · have hpc:s.pc=27:=by simpa [fieldsPC,fields,rootFields,h1,h2] using hp
      have ht:step program n x s=.running {s with pc:=31}:=by simp [step,program,hpc]
      simpa [postCost,h2] using control_run program n B 31 x s hs (by omega) ht
    · have hpc:s.pc=31:=by simpa [fieldsPC,fields,binaryFields,h1,h2] using hp
      have he:{s with pc:=31}=s:=by cases s;simp_all
      simpa [postCost,h2,he] using (BoundedRuns.refl hs : BoundedRuns program n x B s 0 s)

theorem fields_cost (v : Node) : selectCost v+(fields v).length+postCost v=fieldCost v := by
  unfold selectCost fields postCost fieldCost
  split_ifs <;> simp [rationalFields,rootFields,binaryFields]
  all_goals omega

theorem fields_execution (n k c d b a r j B : ℕ) (x : Fin n → ℂ) (v : Node) (s : State)
    (hr:ReadReady k c d b a r j v s) (hv:v.Valid r j) (hj:j < k)
    (hp:s.pc=15) (hs:WordBound B s) (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u,
    BoundedRuns program n x B s (fieldCost v) u ∧ u.pc=31 ∧
    RowReady k c d b a r j v u ∧ u.natHeap=s.natHeap ∧ Frame s u := by
  let f:State:={s with pc:=fieldsPC v}
  have hselect:=select_fields n B k c d b a r j x v s hr hp hs (by omega)
  have hready:ReadReady k c d b a r j v f:=hr.withPC
  have hsem:=fields_semantics k c d b a r j v f hready
  have hpeak:=fields_peak k c d b a r j B v f hready hv hj hB
  have hrun:=block_runs (fields v) program (fieldsPC v) n B x f (fields_code v) rfl
    hselect.final_bound (by
      unfold fields fieldsPC
      split_ifs <;> simp [rationalFields,rootFields,binaryFields] <;> omega)
    hsem.2.2 hpeak
  have hpc:(applyBlock (fields v) f).pc=fieldsPC v+(fields v).length:=applyBlock_pc _ _
  have hpost:=post_fields n B x v (applyBlock (fields v) f) hpc hrun.final_bound (by omega)
  let u:State:={applyBlock (fields v) f with pc:=31}
  refine ⟨u,?_,rfl,hsem.1.withPC,hsem.2.1,?_⟩
  · rw [←fields_cost]
    exact (hselect.trans hrun).trans hpost
  · exact (Frame.withPC s (fieldsPC v)).trans
      ((fields_frame v f).trans (Frame.withPC _ 31))

/-- One literal iteration: branch, nine source/offset instructions, dispatch,
field relocation, six stores/advance instructions, and a jump. -/
theorem iteration {k : ℕ} (n c d b a r j B : ℕ) (x : Fin n → ℂ) (vs : Fin k → Node)
    (heap : ℕ → Option ℕ) (s : State) (hi:Invariant vs c d b a r j heap s)
    (ht:Tape vs c heap) (hd:Disjoint k c d) (hv:∀t,(vs t).Valid r t.val)
    (hj:j < k) (hp:s.pc=5) (hs:WordBound B s) (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u,
    BoundedRuns program n x B s (rowCost (vs ⟨j,hj⟩)) u ∧
    Invariant vs c d b a r (j+1) heap u ∧ u.pc=5 ∧ Frame s u := by
  let v:=vs ⟨j,hj⟩
  have hload:=tape_preserved vs c d b a r j heap s hi ht hd ⟨j,hj⟩
  have he:step program n x s=.running {s with pc:=6}:=by
    simp [step,program,hp,hi.counters.index,hi.counters.header.1,hj]
  have hentry:=control_run program n B 6 x s hs (by omega) he
  let e:State:={s with pc:=6}
  have hsem:=reads_semantics k c d b a r j v e hi.counters.withPC hload.1 hload.2.1 hload.2.2
  have hpeak:=reads_peak k c d b a r j B v e hi.counters.withPC (hv ⟨j,hj⟩) hj hB
    hload.1 hload.2.1 hload.2.2
  have hread:=block_runs reads program 6 n B x e reads_code rfl hentry.final_bound
    (by change 6+9 ≤ B;omega) hsem.2.2 hpeak
  have hreadpc:(applyBlock reads e).pc=15:=by rw [applyBlock_pc];rfl
  obtain ⟨f,hfields,hfpc,hfready,hfheap,hfframe⟩:=fields_execution n k c d b a r j B x v
    (applyBlock reads e) hsem.1 (hv ⟨j,hj⟩) hj hreadpc hread.final_bound hB
  have hinv:Invariant vs c d b a r j heap f:=by
    refine ⟨hfready.counters,?_,?_⟩
    · intro t ht'
      rw [hfheap,hsem.2.1]
      exact hi.copied t ht'
    · intro i hi'
      rw [hfheap,hsem.2.1]
      exact hi.outside i hi'
  have hstorepeak:=stores_peak k c d b a r j B v f hfready (hv ⟨j,hj⟩) hj hB
  have hstores:=block_runs stores program 31 n B x f stores_code hfpc hfields.final_bound
    (by change 31+6 ≤ B;omega) (by simp [stores,readable,Op.readable]) hstorepeak
  have hsPC:(applyBlock stores f).pc=37:=by rw [applyBlock_pc,hfpc];rfl
  have hexit:step program n x (applyBlock stores f)=.running {applyBlock stores f with pc:=5}:=by
    simp [step,program,hsPC]
  have hexit:=control_run program n B 5 x (applyBlock stores f) hstores.final_bound (by omega) hexit
  let u:State:={applyBlock stores f with pc:=5}
  refine ⟨u,?_,(stores_invariant vs c d b a r j heap f hinv hj hfready).withPC,rfl,?_⟩
  · have hc:1+reads.length+fieldCost v+stores.length+1=rowCost v:=by
      simp [reads,stores,fieldCost,rowCost];split_ifs <;> omega
    rw [←hc]
    exact (((hentry.trans hread).trans hfields).trans hstores).trans hexit
  · exact (Frame.withPC s 6).trans ((reads_frame e).trans
      (hfframe.trans ((stores_frame f).trans (Frame.withPC _ 5))))


/-- All node visits execute the fixed 39-instruction code, including every
literal load/store/dispatch. The list below is only the charged cost formula. -/
theorem loop {k : ℕ} (n c d b a r j fuel B : ℕ) (x : Fin n → ℂ) (vs : Fin k → Node)
    (heap : ℕ → Option ℕ) (s : State) (hi:Invariant vs c d b a r j heap s)
    (ht:Tape vs c heap) (hd:Disjoint k c d) (hv:∀t,(vs t).Valid r t.val)
    (hj:j+fuel=k) (hp:s.pc=5) (hs:WordBound B s) (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u,
    BoundedRuns program n x B s (rangeCost vs j fuel) u ∧
    Invariant vs c d b a r k heap u ∧ u.pc=5 ∧ Frame s u := by
  induction fuel generalizing j s with
  | zero=>
    have he:j=k:=by omega
    subst j
    exact ⟨s,.refl hs,hi,hp,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
  | succ fuel ih=>
    have hlt:j < k:=by omega
    obtain ⟨u,hu,hui,hup,huf⟩:=iteration n c d b a r j B x vs heap s hi ht hd hv hlt hp hs hB
    obtain ⟨v,hv',hvi,hvp,hvf⟩:=ih (j+1) u hui (by omega) hup hu.final_bound
    refine ⟨v,?_,hvi,hvp,huf.trans hvf⟩
    simpa only [rangeCost,nodeNat,dite_eq_left hlt] using hu.trans hv'

/-- Prepared tape presence/correctness is the entry contract. There is no
precompiled row premise and no host relocation step. -/
theorem execution {k : ℕ} (n c d b a r B : ℕ) (x : Fin n → ℂ) (vs : Fin k → Node)
    (s : State) (ht:Tape vs c s.natHeap) (hd:Disjoint k c d)
    (hv:∀t,(vs t).Valid r t.val) (hh:Header k c d b a r s)
    (hp:s.pc=0) (hs:WordBound B s) (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u,
    BoundedExecution program n x B s (rangeCost vs 0 k+7) u ∧
    Invariant vs c d b a r k s.natHeap u ∧ u.pc=38 ∧ Frame s u := by
  have hboot:=block_runs boot program 0 n B x s boot_code hp hs
    (by change 0+5 ≤ B;omega) (by simp [boot,readable,Op.readable])
    (by simp [boot,peak,Op.peak];omega)
  let e:=applyBlock boot s
  have hheader:Header k c d b a r e:=by
    simpa [Header,e,applyBlock,boot,Op.apply,writeNat,next] using hh
  have hi:Invariant vs c d b a r 0 s.natHeap e:=by
    refine ⟨?_,?_,?_⟩
    · refine ⟨hheader,?_,?_,?_,?_,?_⟩
      all_goals simp [e,applyBlock,boot,Op.apply,writeNat,next]
    · intro t ht';omega
    · intro i _;rfl
  have hpc:e.pc=5:=by rw [applyBlock_pc,hp];rfl
  obtain ⟨f,hf,hfi,hfp,hff⟩:=loop n c d b a r 0 k B x vs s.natHeap e hi ht hd hv (by omega) hpc
    hboot.final_bound hB
  have hstop:step program n x f=.running {f with pc:=38}:=by
    simp [step,program,hfp,hfi.counters.index,hfi.counters.header.1]
  have hlast:=control_run program n B 38 x f hf.final_bound (by omega) hstop
  have he:BoundedExecution program n x B {f with pc:=38} 1 {f with pc:=38}:=
    .halt hlast.final_bound (by simp [step,program])
  have hbootf:Frame s e:=by
    apply applyBlock_frame
    intro o ho
    simp [boot] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp [Op.scratch]
  refine ⟨{f with pc:=38},?_,hfi.withPC,rfl,hbootf.trans (hff.trans (Frame.withPC f 38))⟩
  convert (hboot.trans hf).executes (hlast.executes he) using 1
  simp [boot]
  omega

/-- Three actual loads and three actual Nat stores per node. Startup, terminal
branch and halt cost seven; rational/root dispatch costs 24, binary costs 22. -/
theorem execution_linear {k : ℕ} (n c d b a r B : ℕ) (x : Fin n → ℂ) (vs : Fin k → Node)
    (s : State) (ht:Tape vs c s.natHeap) (hd:Disjoint k c d)
    (hv:∀t,(vs t).Valid r t.val) (hh:Header k c d b a r s)
    (hp:s.pc=0) (hs:WordBound B s) (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 24*k+7 ∧
    Invariant vs c d b a r k s.natHeap u ∧ Frame s u := by
  obtain ⟨u,hu,hi,_hp,hf⟩:=execution n c d b a r B x vs s ht hd hv hh hp hs hB
  exact ⟨u,_,hu,by have h:=rangeCost_le vs 0 k;omega,hi,hf⟩

theorem printed_natTable {r k : ℕ} (p : DProgram r k) (c d b a : ℕ)
    (heap : ℕ → Option ℕ) (s : State) (hi:Invariant (nodes p) c d b a r k heap s) :
    UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d s := by
  intro j row hj
  have hlt:j < k:=by simpa [UniformOffsetPreparationMachine.compile_length] using
    (List.getElem?_eq_some_iff.mp hj).choose
  let t:Fin k:=⟨j,hlt⟩
  obtain ⟨row',hrow',hfields⟩:=nodes_compile_get p b a t
  have he:row'=row:=by rw [hj] at hrow';exact Option.some.inj hrow'.symm
  subst row'
  have hcopied:=hi.copied t hlt
  simpa [t,hfields] using hcopied

/-- The full typed-DAG NatTable obligation is discharged by actual printing.
The input node tape remains explicit until a topology producer constructs it. -/
theorem typed_execution {r k : ℕ} (p : DProgram r k) (n c d b a B : ℕ)
    (x : Fin n → ℂ) (s : State) (ht:Tape (nodes p) c s.natHeap) (hd:Disjoint k c d)
    (hh:Header k c d b a r s) (hp:s.pc=0) (hs:WordBound B s)
    (hB:c+d+b+a+r+4*k+80 ≤ B) : ∃u,
    BoundedExecution program n x B s (rangeCost (nodes p) 0 k+7) u ∧
    rangeCost (nodes p) 0 k+7 ≤ 24*k+7 ∧
    UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d u ∧
    Frame s u ∧ Outside k d s.natHeap u ∧ u.pc=38 ∧ Counters k c d b a r k u := by
  obtain ⟨u,hu,hi,hp',hf⟩:=execution n c d b a r B x (nodes p) s ht hd
    (nodes_valid p) hh hp hs hB
  exact ⟨u,hu,by have h:=rangeCost_le (nodes p) 0 k;omega,
    printed_natTable p c d b a s.natHeap u hi,hf,hi.outside,hp',hi.counters⟩

/-- The printer never changes a prepared root or rational leaf, including an
unrelated master root at heap0. No scalar retagging occurs. -/
theorem leaf_readiness_retained {r k : ℕ} (p : DProgram r k) (roots : Fin r → ℂ)
    (b : ℕ) (s u : State) (hf:Frame s u)
    (hr:UniformOffsetPreparationMachine.RootsReady b roots s)
    (hl:UniformOffsetPreparationMachine.LiteralsReady p b s) :
    UniformOffsetPreparationMachine.RootsReady b roots u ∧
    UniformOffsetPreparationMachine.LiteralsReady p b u := by
  refine ⟨?_,?_⟩
  · simpa [UniformOffsetPreparationMachine.RootsReady,hf.1] using hr
  · induction p with
    | nil=>trivial
    | step p i ih=>
      refine ⟨ih hl.1,?_⟩
      cases i <;> try trivial
      simpa [UniformOffsetPreparationMachine.LiteralReady,hf.1] using hl.2

end
end ExactFourierCircuits.UniformPreparationRowTableMachine
