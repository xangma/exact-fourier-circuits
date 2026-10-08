import UniformSelectedDFSMachine
import UniformInPlaceMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformTensorMonomialMachine
open UniformMachine
open UniformPairMachine (prepared product)

/-- Straight-line instructions have literal bytecode, present-read obligations
    and exact state semantics. There is no callback instruction. -/
inductive Op where
  | literal (dst value : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | getNat (dst address : ℕ)
  | putNat (address src : ℕ)
  | literalScalar (dst : ℕ) (value : ℚ)
  | getScalar (dst address : ℕ)
  | putScalar (address src : ℕ)
  | scalarMul (dst left right : ℕ)
  deriving DecidableEq

def Op.code : Op→Instruction
  | .literal d v => .natLiteral d v
  | .add d l r => .natBinary .add d l r
  | .sub d l r => .natBinary .sub d l r
  | .mul d l r => .natBinary .mul d l r
  | .getNat d a => .loadNat d a
  | .putNat a r => .storeNat a r
  | .literalScalar d q => .scalarLiteral d q
  | .getScalar d a => .loadScalar d a
  | .putScalar a r => .storeScalar a r
  | .scalarMul d l r => .fieldBinary .mul d l r

def boot : List Op := [.literal 9 1,.literal 10 3,.literal 13 0,.literal 0 0,
  .literal 2 0,.literal 14 0,.literalScalar 0 1,.literal 8 0]
def enterBlock : List Op := [.mul 11 0 10,.add 11 5 11,.getNat 4 11,.add 11 11 9,
  .getNat 18 11,.add 11 11 9,.getNat 17 11,.literal 3 0]
def childBlock : List Op := [.mul 11 0 10,.add 11 6 11,.putNat 11 2,
  .add 11 11 9,.putNat 11 14,.add 11 11 9,.add 12 3 9,.putNat 11 12,
  .add 11 16 0,.putScalar 11 0,.add 11 18 3,.getNat 19 11,
  .add 11 17 3,.getScalar 1 11,.scalarMul 0 0 1,
  .mul 2 2 4,.add 2 2 3,.mul 14 14 4,.add 14 14 19,.add 0 0 9]
def leafBlock : List Op := [.add 11 7 2,.getScalar 1 11,.scalarMul 1 0 1,
  .add 11 15 14,.putScalar 11 1,.add 8 8 9]
def popBlock : List Op := [.sub 0 0 9,.mul 11 0 10,.add 11 6 11,.getNat 2 11,
  .add 11 11 9,.getNat 14 11,.add 11 11 9,.getNat 3 11,
  .add 11 16 0,.getScalar 0 11,.mul 11 0 10,.add 11 5 11,.getNat 4 11,
  .add 11 11 9,.getNat 18 11,.add 11 11 9,.getNat 17 11]

/-- Nat1=axis count,5=axis-row base,6=Nat stack base,7=source,
    15=destination,16=scalar stack base. Every child updates two Horner
    ordinals and one prepared coefficient; every leaf moves one data value. -/
def program : Program := boot.map Op.code ++ [.branchLT 0 1 9 39] ++
  enterBlock.map Op.code ++ [.branchLT 3 4 18 46] ++
  childBlock.map Op.code ++ [.jump 8] ++ leafBlock.map Op.code ++ [.jump 46] ++
  [.branchLT 13 0 47 65] ++ popBlock.map Op.code ++ [.jump 17,.halt]

theorem boot_length : boot.length=8 := rfl
theorem enter_length : enterBlock.length=8 := rfl
theorem child_length : childBlock.length=20 := rfl
theorem leaf_length : leafBlock.length=6 := rfl
theorem pop_length : popBlock.length=17 := rfl
theorem program_length : program.length=66 := rfl
theorem entry_branch : program[8]?=some (.branchLT 0 1 9 39) := rfl
theorem child_branch : program[17]?=some (.branchLT 3 4 18 46) := rfl
theorem child_jump : program[38]?=some (.jump 8) := rfl
theorem leaf_jump : program[45]?=some (.jump 46) := rfl
theorem pop_branch : program[46]?=some (.branchLT 13 0 47 65) := rfl
theorem pop_jump : program[64]?=some (.jump 17) := rfl
theorem halt_at : program[65]?=some .halt := rfl

noncomputable section

def Op.apply (o : Op) (s : State) : State := match o with
  | .literal d v => writeNat s d v
  | .add d l r => writeNat s d (s.natReg l+s.natReg r)
  | .sub d l r => writeNat s d (s.natReg l-s.natReg r)
  | .mul d l r => writeNat s d (s.natReg l*s.natReg r)
  | .getNat d a => writeNat s d ((s.natHeap (s.natReg a)).getD 0)
  | .putNat a r => {next s with natHeap:=Function.update s.natHeap (s.natReg a) (some (s.natReg r))}
  | .literalScalar d q => writeScalar s d ⟨q,false⟩
  | .getScalar d a => writeScalar s d ((s.scalarHeap (s.natReg a)).getD Scalar.zero)
  | .putScalar a r => {next s with scalarHeap:=Function.update s.scalarHeap (s.natReg a) (some (s.scalarReg r))}
  | .scalarMul d l r => writeScalar s d ((evalField .mul (s.scalarReg l) (s.scalarReg r)).getD Scalar.zero)

def Op.readable (o : Op) (s : State) : Prop := match o with
  | .getNat _ a => (s.natHeap (s.natReg a)).isSome=true
  | .getScalar _ a => (s.scalarHeap (s.natReg a)).isSome=true
  | .scalarMul _ l r => (evalField .mul (s.scalarReg l) (s.scalarReg r)).isSome=true
  | _ => True

def Op.peak (o : Op) (s : State) : ℕ := match o with
  | .literal _ v => v
  | .add _ l r => s.natReg l+s.natReg r
  | .sub _ l r => s.natReg l-s.natReg r
  | .mul _ l r => s.natReg l*s.natReg r
  | .getNat _ a => (s.natHeap (s.natReg a)).getD 0
  | .putNat a r => max (s.natReg a) (s.natReg r)
  | .putScalar a _ => s.natReg a
  | _ => 0

def applyBlock : List Op→State→State
  | [],s=>s
  | o::b,s=>applyBlock b (o.apply s)
def readable : List Op→State→Prop
  | [],_=>True
  | o::b,s=>o.readable s ∧ readable b (o.apply s)
def peak : List Op→State→ℕ
  | [],_=>0
  | o::b,s=>max (o.peak s) (peak b (o.apply s))
def BlockAt (b : List Op) (p : Program) (base : ℕ) : Prop :=
  ∀i,(hi:i<b.length)→p[base+i]?=some (b[i]'hi).code

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by
  cases o <;> rfl

theorem Op.step (o : Op) (p : Program) (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:p[s.pc]?=some o.code) (hr:o.readable s) : step p n x s=.running (o.apply s) := by
  cases o <;> simp [UniformMachine.step,hc,Op.code,Op.apply,evalNat]
  case getNat d a =>
    cases hh:s.natHeap (s.natReg a) with
    | none => simp [Op.readable,hh] at hr
    | some v => simp
  case getScalar d a =>
    cases hh:s.scalarHeap (s.natReg a) with
    | none => simp [Op.readable,hh] at hr
    | some v => simp
  case scalarMul d l r =>
    cases hh:evalField .mul (s.scalarReg l) (s.scalarReg r) with
    | none => simp [Op.readable,hh] at hr
    | some v => simp

theorem Op.apply_bound (o : Op) (B : ℕ) (s : State) (hs:WordBound B s)
    (hp:s.pc+1≤B) (hv:o.peak s≤B) : WordBound B (o.apply s) := by
  cases o with
  | literal d v => exact writeNat_bound B s d v hs hp hv
  | add d l r => exact writeNat_bound B s d _ hs hp hv
  | sub d l r => exact writeNat_bound B s d _ hs hp hv
  | mul d l r => exact writeNat_bound B s d _ hs hp hv
  | getNat d a => exact writeNat_bound B s d _ hs hp hv
  | putNat a r =>
    exact UniformNatCopyMachine.store_bound B s _ _ hs hp
      ((le_max_left _ _).trans hv) ((le_max_right _ _).trans hv)
  | literalScalar d q => exact writeScalar_bound B s d _ hs hp
  | getScalar d a => exact writeScalar_bound B s d _ hs hp
  | putScalar a r => exact UniformInPlaceMachine.storeScalar_bound B s _ _ hs hp hv
  | scalarMul d l r => exact writeScalar_bound B s d _ hs hp

theorem applyBlock_pc (b : List Op) (s : State) : (applyBlock b s).pc=s.pc+b.length := by
  induction b generalizing s with
  | nil => rfl
  | cons o b ih => simp [applyBlock,ih,Op.apply_pc];omega

/-- Straight-line segments are exact charged finite-machine runs. -/
theorem block_runs (b : List Op) (p : Program) (base n B : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:BlockAt b p base) (hpc:s.pc=base) (hs:WordBound B s)
    (hb:base+b.length≤B) (hr:readable b s) (hv:peak b s≤B) :
    BoundedRuns p n x B s b.length (applyBlock b s) := by
  induction b generalizing base s with
  | nil => exact .refl hs
  | cons o b ih =>
    have hp:s.pc+1≤B:=by simp only [List.length_cons] at hb;omega
    have hbound:=o.apply_bound B s hs hp ((le_max_left _ _).trans hv)
    have ht:BlockAt b p (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change p[base+(i+1)]?=some (b[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have tail:=ih (base+1) (o.apply s) ht (by rw [Op.apply_pc,hpc]) hbound
      (by simp only [List.length_cons] at hb;omega) hr.2 ((le_max_right _ _).trans hv)
    exact .next hs (o.step p n x s (by
      have h:=hc 0 (by simp)
      change p[base+0]?=some o.code at h
      simpa only [hpc,Nat.add_zero] using h) hr.1) tail

theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i<8 at hi;interval_cases i <;> rfl
theorem enter_code : BlockAt enterBlock program 9 := by
  intro i hi;change i<8 at hi;interval_cases i <;> rfl
theorem child_code : BlockAt childBlock program 18 := by
  intro i hi;change i<20 at hi;interval_cases i <;> rfl
theorem leaf_code : BlockAt leafBlock program 39 := by
  intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem pop_code : BlockAt popBlock program 47 := by
  intro i hi;change i<17 at hi;interval_cases i <;> rfl

def setPC (s : State) (pc : ℕ) : State := {s with pc:=pc}
def initialized (s : State) : State := applyBlock boot s
def entered (s : State) : State := applyBlock enterBlock (setPC s 9)
def child (s : State) : State := setPC (applyBlock childBlock (setPC s 18)) 8
def leaf (s : State) : State := setPC (applyBlock leafBlock (setPC s 39)) 46
def popped (s : State) : State := setPC (applyBlock popBlock (setPC s 47)) 17

def treeCost : List ℕ→ℕ
  | []=>8
  | r::rs=>10+r*(treeCost rs+41)

theorem treeCost_balance (rs : List ℕ) :
    treeCost rs+41+2*rs.prod=51*UniformTraversal.nodeCount rs := by
  induction rs with
  | nil => norm_num [treeCost,UniformTraversal.nodeCount]
  | cons r rs ih =>
    simp only [treeCost,UniformTraversal.nodeCount,List.prod_cons]
    calc
      10+r*(treeCost rs+41)+41+2*(r*rs.prod)
          =51+r*(treeCost rs+41+2*rs.prod):=by ring
      _=51*(1+r*UniformTraversal.nodeCount rs):=by rw [ih];ring

/-- Exact semantic layers for the carried state, to be instantiated from
    the prepared per-axis permutation/coefficient tables. -/
structure Axis where
  radix : ℕ
  positive : 0<radix
  permutation : Fin radix≃Fin radix
  coefficient : Fin radix→ℂ
  permutationBase : ℕ
  coefficientBase : ℕ

def radices (axes : List Axis) : List ℕ := axes.map Axis.radix

def originalLayers (axes : List Axis) : List (UniformTraversal.Layer ℕ) :=
  axes.map (fun a=>⟨a.radix,fun i I=>I*a.radix+i.val⟩)
def permutedLayers (axes : List Axis) : List (UniformTraversal.Layer ℕ) :=
  axes.map (fun a=>⟨a.radix,fun i I=>I*a.radix+(a.permutation i).val⟩)

def Constants (s : State) : Prop := s.natReg 9=1 ∧ s.natReg 10=3 ∧ s.natReg 13=0

def Cursor (d I P : ℕ) (c : ℂ) (s : State) : Prop :=
  s.natReg 0=d ∧ s.natReg 2=I ∧ s.natReg 14=P ∧ s.scalarReg 0=prepared c

theorem boot_properties (s : State) : Constants (initialized s) ∧ Cursor 0 0 0 1 (initialized s) ∧
    (initialized s).natReg 8=0 ∧ (initialized s).natHeap=s.natHeap ∧
    (initialized s).scalarHeap=s.scalarHeap := by
  simp [Constants,Cursor,initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next,prepared]

theorem boot_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State) (hpc:s.pc=0)
    (hB:66≤B) (hs:WordBound B s) : BoundedRuns program n x B s 8 (initialized s) := by
  have h:=block_runs boot program 0 n B x s boot_code hpc hs
    (by rw [boot_length];omega) (by simp [readable,boot,Op.readable])
    (by simp [peak,boot,Op.peak];omega)
  simpa only [boot_length,initialized] using h

/-- The data tag passes through exactly; the first factor is prepared even
    when the input or coefficient is zero. -/
theorem leaf_effect (s : State) (c : ℂ) (v : Scalar)
    (h9:s.natReg 9=1) (hc:s.scalarReg 0=prepared c)
    (hv:s.scalarHeap (s.natReg 7+s.natReg 2)=some v) :
    (leaf s).pc=46 ∧ (leaf s).natReg 8=s.natReg 8+1 ∧
    (leaf s).scalarHeap=Function.update s.scalarHeap (s.natReg 15+s.natReg 14) (some (product c v)) ∧
    (leaf s).natHeap=s.natHeap ∧ (leaf s).scalarReg 0=prepared c ∧
    (leaf s).scalarReg 1=product c v := by
  simp [leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,writeScalar,next,h9,hc,hv,
    UniformPairMachine.prepared_mul]

/-- One branch, six literal operations, one continuation: eight charged
    instructions move exactly one arbitrary tagged data coordinate. -/
theorem leaf_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State) (c : ℂ) (v : Scalar)
    (hpc:s.pc=8) (hleaf:¬s.natReg 0<s.natReg 1) (h9:s.natReg 9=1)
    (hc:s.scalarReg 0=prepared c) (hv:s.scalarHeap (s.natReg 7+s.natReg 2)=some v)
    (hB:66≤B) (hdest:s.natReg 15+s.natReg 14≤B) (hcount:s.natReg 8+1≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 8 (leaf s) := by
  let e:=setPC s 39
  have he:WordBound B e:=changePC_bound B s 39 hs (by omega)
  have hsrc:s.natReg 7+s.natReg 2≤B:=hs.2.2.2.1 _ _ hv
  have hr:readable leafBlock e:=by
    simp [readable,leafBlock,Op.readable,Op.apply,e,setPC,writeNat,writeScalar,next,hc,hv,
      UniformPairMachine.prepared_mul]
  have hp:peak leafBlock e≤B:=by
    simp [peak,leafBlock,Op.peak,Op.apply,e,setPC,writeNat,writeScalar,next,h9]
    omega
  have body:=block_runs leafBlock program 39 n B x e leaf_code rfl he
    (by rw [leaf_length];omega) hr hp
  have hpbody:(applyBlock leafBlock e).pc=45:=by rw [applyBlock_pc,leaf_length];rfl
  have hj:BoundedRuns program n x B (applyBlock leafBlock e) 1 (leaf s):=
    .next body.final_bound (by rw [UniformMachine.step,hpbody,leaf_jump];rfl)
      (.refl (changePC_bound B _ 46 body.final_bound (by omega)))
  have enter:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [UniformMachine.step,hpc,entry_branch,hleaf,e,setPC]) (.refl he)
  simpa only [leaf_length] using enter.trans (body.trans hj)

/-- The entry loads only the three current-axis cells; no axis scan occurs. -/
theorem enter_bounded (n B d r p c : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=8) (hgo:s.natReg 0<s.natReg 1) (h0:s.natReg 0=d)
    (h9:s.natReg 9=1) (h10:s.natReg 10=3)
    (hr:s.natHeap (s.natReg 5+d*3)=some r)
    (hp:s.natHeap (s.natReg 5+d*3+1)=some p)
    (hc:s.natHeap (s.natReg 5+d*3+2)=some c)
    (hB:66≤B) (hrow:s.natReg 5+d*3+2≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 9 (entered s) := by
  simp only [Nat.add_assoc] at hr hp hc
  let e:=setPC s 9
  have he:WordBound B e:=changePC_bound B s 9 hs (by omega)
  have hrB:r≤B:=(hs.2.2.1 _ _ hr).2
  have hpB:p≤B:=(hs.2.2.1 _ _ hp).2
  have hcB:c≤B:=(hs.2.2.1 _ _ hc).2
  have hr':readable enterBlock e:=by
    simp [readable,enterBlock,Op.readable,Op.apply,e,setPC,writeNat,next,h0,h9,h10,
      hr,hp,hc,Nat.add_assoc]
  have peak':peak enterBlock e≤B:=by
    simp [peak,enterBlock,Op.peak,Op.apply,e,setPC,writeNat,next,h0,h9,h10,
      hr,hp,hc,Nat.add_assoc]
    omega
  have body:=block_runs enterBlock program 9 n B x e enter_code rfl he
    (by rw [enter_length];omega) hr' peak'
  have first:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [UniformMachine.step,hpc,entry_branch,hgo,e,setPC]) (.refl he)
  simpa only [enter_length,entered,e] using first.trans body

theorem enter_properties (s : State) (d r p c : ℕ) (h0:s.natReg 0=d)
    (h9:s.natReg 9=1) (h10:s.natReg 10=3)
    (hr:s.natHeap (s.natReg 5+d*3)=some r)
    (hp:s.natHeap (s.natReg 5+d*3+1)=some p)
    (hc:s.natHeap (s.natReg 5+d*3+2)=some c) :
    (entered s).pc=17 ∧ (entered s).natReg 4=r ∧ (entered s).natReg 18=p ∧
    (entered s).natReg 17=c ∧ (entered s).natReg 3=0 ∧
    (entered s).natHeap=s.natHeap ∧ (entered s).scalarHeap=s.scalarHeap ∧
    (entered s).scalarReg=s.scalarReg := by
  simp only [Nat.add_assoc] at hr hp hc
  simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,h0,h9,h10,
    hr,hp,hc,Nat.add_assoc]

/-- An empty tensor is a genuine charged copy, with literal prepared1 boot. -/
theorem empty_execution (n B : ℕ) (x : Fin n→ℂ) (s : State) (v : Scalar)
    (hpc:s.pc=0) (haxes:s.natReg 1=0) (hv:s.scalarHeap (s.natReg 7)=some v)
    (hB:66≤B) (hdest:s.natReg 15≤B) (hs:WordBound B s) :
    BoundedExecution program n x B s 18 (setPC (leaf (initialized s)) 65) := by
  have bootrun:=boot_bounded n B x s hpc hB hs
  have bp:=boot_properties s
  have leafrun:=leaf_bounded n B x (initialized s) 1 v (by
      simp [initialized,applyBlock_pc,boot_length,hpc])
    (by simp [initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next,haxes]) bp.1.1
    bp.2.1.2.2.2 (by
      simp [initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next,hv]) hB
    (by simpa [initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next] using hdest)
    (by rw [bp.2.2.1];omega) bootrun.final_bound
  have lp:=leaf_effect (initialized s) 1 v bp.1.1 bp.2.1.2.2.2 (by
    simp [initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next,hv])
  let u:=setPC (leaf (initialized s)) 65
  have hu:WordBound B u:=changePC_bound B _ 65 leafrun.final_bound (by omega)
  have tail:BoundedExecution program n x B (leaf (initialized s)) 2 u:=by
    refine .next leafrun.final_bound ?_ (.halt hu ?_)
    · have hd:(leaf (initialized s)).natReg 0=0:=by
        simp [leaf,initialized,setPC,applyBlock,boot,leafBlock,Op.apply,writeNat,writeScalar,next]
      have hz:(leaf (initialized s)).natReg 13=0:=by
        simp [leaf,initialized,setPC,applyBlock,boot,leafBlock,Op.apply,writeNat,writeScalar,next]
      simp [UniformMachine.step,lp.1,pop_branch,hd,hz,u,setPC]
    · simp [UniformMachine.step,u,setPC,halt_at]
  simpa using bootrun.executes (leafrun.executes tail)

structure ChildReady (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State) : Prop where
  depth : s.natReg 0=d
  original : s.natReg 2=I
  permuted : s.natReg 14=P
  radix : s.natReg 4=r
  digit : s.natReg 3=i
  permBase : s.natReg 18=p
  coefficientBase : s.natReg 17=a
  natStack : s.natReg 6=N
  scalarStack : s.natReg 16=S
  one : s.natReg 9=1
  three : s.natReg 10=3
  scalarPrefix : s.scalarReg 0=prepared c
  permutation : s.natHeap (p+i)=some pi
  coefficient : s.scalarHeap (a+i)=some (prepared k)
  permReadonly : p+i<N
  coefficientReadonly : a+i<S

def ChildBounds (B d I P r i pi p a N S : ℕ) : Prop :=
  N+d*3+2≤B ∧ S+d≤B ∧ p+i≤B ∧ a+i≤B ∧ I*r+i≤B ∧
  P*r+pi≤B ∧ d+1≤B ∧ i+1≤B

/-- Both ordinals and the prepared scalar prefix are carried by literal
    operations. Stack slots preserve the parent's complete cursor. -/
theorem child_properties (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) :
    (child s).pc=8 ∧ Cursor (d+1) (I*r+i) (P*r+pi) (c*k) (child s) ∧
    (child s).natReg 8=s.natReg 8 ∧
    (child s).natHeap=Function.update
      (Function.update (Function.update s.natHeap (N+d*3) (some I)) (N+d*3+1) (some P))
      (N+d*3+2) (some (i+1)) ∧
    (child s).scalarHeap=Function.update s.scalarHeap (S+d) (some (prepared c)) := by
  rcases h with ⟨hd,hI,hP,hr,hi,hp,ha,hN,hS,h1,h3,hc,hpi,hk,hpn,hks⟩
  simp (disch:=omega) [child,setPC,Cursor,applyBlock,childBlock,Op.apply,writeNat,writeScalar,next,
    hd,hI,hP,hr,hi,hp,ha,hN,hS,h1,h3,hc,hpi,hk,evalField,prepared,Nat.add_assoc]

theorem child_readable (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) : readable childBlock (setPC s 18) := by
  rcases h with ⟨hd,hI,hP,hr,hi,hp,ha,hN,hS,h1,h3,hc,hpi,hk,hpn,hks⟩
  simp (disch:=omega) [readable,childBlock,Op.readable,Op.apply,setPC,writeNat,writeScalar,next,
    hd,hI,hP,hi,hp,ha,hN,hS,h1,h3,hc,hpi,hk,evalField,prepared,Nat.add_assoc]

theorem child_peak (d I P r i pi p a N S B : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) (hb:ChildBounds B d I P r i pi p a N S)
    (hs:WordBound B s) : peak childBlock (setPC s 18)≤B := by
  rcases h with ⟨hd,hI,hP,hr,hi,hp,ha,hN,hS,h1,h3,hc,hpi,hk,hpn,hks⟩
  have hIB:I≤B:=by simpa only [hI] using hs.2.1 2
  have hPB:P≤B:=by simpa only [hP] using hs.2.1 14
  have hpiB:pi≤B:=(hs.2.2.1 _ _ hpi).2
  rcases hb with ⟨hstack,hscalar,hperm,hcoef,hnewI,hnewP,hdepth,hdigit⟩
  simp (disch:=omega) [peak,childBlock,Op.peak,Op.apply,setPC,writeNat,writeScalar,next,
    hd,hI,hP,hr,hi,hp,ha,hN,hS,h1,h3,hpi,Nat.add_assoc]
  omega

/-- Conditional descent: one branch, twenty operations and one jump. -/
theorem child_bounded (n B d I P r i pi p a N S : ℕ) (x : Fin n→ℂ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) (hpc:s.pc=17) (hi:i<r)
    (hB:66≤B) (hb:ChildBounds B d I P r i pi p a N S) (hs:WordBound B s) :
    BoundedRuns program n x B s 22 (child s) := by
  let e:=setPC s 18
  have he:WordBound B e:=changePC_bound B s 18 hs (by omega)
  have body:=block_runs childBlock program 18 n B x e child_code rfl he
    (by rw [child_length];omega) (child_readable d I P r i pi p a N S c k s h)
    (child_peak d I P r i pi p a N S B c k s h hb hs)
  have bp:(applyBlock childBlock e).pc=38:=by rw [applyBlock_pc,child_length];rfl
  have jump:BoundedRuns program n x B (applyBlock childBlock e) 1 (child s):=
    .next body.final_bound (by rw [UniformMachine.step,bp,child_jump];rfl)
      (.refl (changePC_bound B _ 8 body.final_bound (by omega)))
  have first:BoundedRuns program n x B s 1 e:=.next hs (by
    simp [UniformMachine.step,hpc,child_branch,h.digit,h.radix,hi,e,setPC]) (.refl he)
  simpa only [child_length] using first.trans (body.trans jump)


structure PopReady (d I P i r p a b N S : ℕ) (c : ℂ) (s : State) : Prop where
  depth : s.natReg 0=d+1
  one : s.natReg 9=1
  three : s.natReg 10=3
  zero : s.natReg 13=0
  rowBase : s.natReg 5=b
  natStack : s.natReg 6=N
  scalarStack : s.natReg 16=S
  original : s.natHeap (N+d*3)=some I
  permuted : s.natHeap (N+d*3+1)=some P
  digit : s.natHeap (N+d*3+2)=some i
  scalarPrefix : s.scalarHeap (S+d)=some (prepared c)
  radix : s.natHeap (b+d*3)=some r
  permBase : s.natHeap (b+d*3+1)=some p
  coefficientBase : s.natHeap (b+d*3+2)=some a

/-- Pop reads the saved complete cursor and the current row, restoring all
    three carried values. It does not reconstruct a prefix by scanning axes. -/
theorem pop_properties (d I P i r p a b N S : ℕ) (c : ℂ) (s : State)
    (h:PopReady d I P i r p a b N S c s) :
    (popped s).pc=17 ∧ Cursor d I P c (popped s) ∧
    (popped s).natReg 3=i ∧ (popped s).natReg 4=r ∧
    (popped s).natReg 18=p ∧ (popped s).natReg 17=a ∧
    (popped s).natReg 8=s.natReg 8 ∧
    (popped s).natHeap=s.natHeap ∧ (popped s).scalarHeap=s.scalarHeap := by
  rcases h with ⟨hd,h1,h3,h0,ha,hN,hS,hI,hP,hi,hc,hr,hp,hcoef⟩
  simp only [Nat.add_assoc] at hI hP hi hr hp hcoef
  simp [popped,setPC,Cursor,applyBlock,popBlock,Op.apply,writeNat,writeScalar,next,
    hd,h1,h3,ha,hN,hS,hI,hP,hi,hc,hr,hp,hcoef,Nat.add_assoc]

theorem pop_bounded (n B d I P i r p a b N S : ℕ) (x : Fin n→ℂ) (c : ℂ) (s : State)
    (h:PopReady d I P i r p a b N S c s) (hpc:s.pc=46) (hB:66≤B)
    (hstack:N+d*3+2≤B) (hrow:b+d*3+2≤B) (hscalar:S+d≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 19 (popped s) := by
  have hIB: I≤B:=(hs.2.2.1 _ _ h.original).2
  have hPB: P≤B:=(hs.2.2.1 _ _ h.permuted).2
  have hiB: i≤B:=(hs.2.2.1 _ _ h.digit).2
  have hrB: r≤B:=(hs.2.2.1 _ _ h.radix).2
  have hpB: p≤B:=(hs.2.2.1 _ _ h.permBase).2
  have haB: a≤B:=(hs.2.2.1 _ _ h.coefficientBase).2
  rcases h with ⟨hd,h1,h3,h0,ha,hN,hS,hI,hP,hi,hc,hr,hp,hcoef⟩
  simp only [Nat.add_assoc] at hI hP hi hr hp hcoef
  let e:=setPC s 47
  have he:WordBound B e:=changePC_bound B s 47 hs (by omega)
  have readable':readable popBlock e:=by
    simp [readable,popBlock,Op.readable,Op.apply,e,setPC,writeNat,writeScalar,next,
      hd,h1,h3,ha,hN,hS,hI,hP,hi,hc,hr,hp,hcoef,Nat.add_assoc]
  have peak':peak popBlock e≤B:=by
    simp [peak,popBlock,Op.peak,Op.apply,e,setPC,writeNat,writeScalar,next,
      hd,h1,h3,ha,hN,hS,hI,hP,hi,hr,hp,hcoef,Nat.add_assoc]
    omega
  have body:=block_runs popBlock program 47 n B x e pop_code rfl he
    (by rw [pop_length];omega) readable' peak'
  have bp:(applyBlock popBlock e).pc=64:=by rw [applyBlock_pc,pop_length];rfl
  have jump:BoundedRuns program n x B (applyBlock popBlock e) 1 (popped s):=
    .next body.final_bound (by rw [UniformMachine.step,bp,pop_jump];rfl)
      (.refl (changePC_bound B _ 17 body.final_bound (by omega)))
  have first:BoundedRuns program n x B s 1 e:=.next hs (by
    simp [UniformMachine.step,hpc,pop_branch,h0,hd,e,setPC]) (.refl he)
  simpa only [pop_length] using first.trans (body.trans jump)

/-- Every literal operation retains roots, output and all high registers.
    The monomial program changes only the explicitly designated low registers. -/
def Frame (s t : State) : Prop :=
  t.rootOrders=s.rootOrders ∧ t.outputs=s.outputs ∧
  (∀j,20≤j→t.natReg j=s.natReg j) ∧
  (∀j,2≤j→t.scalarReg j=s.scalarReg j)

theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem frame_trans {s t u : State} (h:Frame s t) (h':Frame t u) : Frame s u := by
  refine ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,?_,?_⟩
  · intro j hj; exact (h'.2.2.1 j hj).trans (h.2.2.1 j hj)
  · intro j hj; exact (h'.2.2.2 j hj).trans (h.2.2.2 j hj)

theorem block_frame (b : List Op) (s : State)
    (hNat:∀o∈b,match o with
      | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _ => d<20
      | _=>True)
    (hScalar:∀o∈b,match o with
      | .literalScalar d _ | .getScalar d _ | .scalarMul d _ _ => d<2
      | _=>True) : Frame s (applyBlock b s) := by
  induction b generalizing s with
  | nil => exact frame_refl s
  | cons o b ih =>
    have hN:=hNat o (by simp)
    have hS:=hScalar o (by simp)
    have hstep:Frame s (o.apply s):=by
      cases o <;> simp only at hN hS <;>
        simp [Frame,Op.apply,writeNat,writeScalar,next]
      all_goals intro j hj; simp (disch:=omega)
    exact frame_trans hstep (ih _ (fun q hq=>hNat q (by simp [hq]))
      (fun q hq=>hScalar q (by simp [hq])))

theorem all_blocks_frame (s : State) : Frame s (initialized s) ∧ Frame s (entered s) ∧
    Frame s (child s) ∧ Frame s (leaf s) ∧ Frame s (popped s) := by
  have f (b : List Op) (hb: b=boot ∨ b=enterBlock ∨ b=childBlock ∨ b=leafBlock ∨ b=popBlock) :
      Frame s (applyBlock b s):=by
    apply block_frame
    · rcases hb with h|h|h|h|h <;> subst b <;>
        simp [boot,enterBlock,childBlock,leafBlock,popBlock]
    · rcases hb with h|h|h|h|h <;> subst b <;>
        simp [boot,enterBlock,childBlock,leafBlock,popBlock]
  refine ⟨f boot (by simp),?_,?_,?_,?_⟩
  · simpa [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,Frame] using
      f enterBlock (by simp)
  · simpa [child,setPC,applyBlock,childBlock,Op.apply,writeNat,writeScalar,next,Frame] using
      f childBlock (by simp)
  · simpa [leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,writeScalar,next,Frame] using
      f leafBlock (by simp)
  · simpa [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,writeScalar,next,Frame] using
      f popBlock (by simp)


/-- The recursive evaluator below is only a logical reference for the fixed
    bytecode. In particular `visit` never occurs in an Instruction. -/
def children (visit : State→State) : ℕ→State→State
  | 0,s=>setPC s 46
  | k+1,s=>children visit k (popped (visit (child s)))
def tree : List ℕ→State→State
  | [],s=>leaf s
  | r::rs,s=>children (tree rs) r (entered s)

structure EntrySafe (B : ℕ) (s : State) : Prop where
  pc : s.pc=8
  go : s.natReg 0<s.natReg 1
  readable : readable enterBlock (setPC s 9)
  peak : peak enterBlock (setPC s 9)≤B
structure DescentSafe (B : ℕ) (s : State) : Prop where
  pc : s.pc=17
  go : s.natReg 3<s.natReg 4
  readable : readable childBlock (setPC s 18)
  peak : peak childBlock (setPC s 18)≤B
structure ReturnSafe (B : ℕ) (s : State) : Prop where
  pc : s.pc=46
  go : s.natReg 13<s.natReg 0
  readable : readable popBlock (setPC s 47)
  peak : peak popBlock (setPC s 47)≤B
structure LeafSafe (B : ℕ) (s : State) : Prop where
  pc : s.pc=8
  go : ¬s.natReg 0<s.natReg 1
  readable : readable leafBlock (setPC s 39)
  peak : peak leafBlock (setPC s 39)≤B
structure Exhausted (s : State) : Prop where
  pc : s.pc=17
  stop : ¬s.natReg 3<s.natReg 4

/-- A segment lemma for the literal branch, literal block and literal jump.
    Readability and integer peaks are safety predicates, never action premises. -/
theorem branched_block (b : List Op) (base branchPC jumpPC target yes no l r n B : ℕ)
    (x : Fin n→ℂ) (s : State) (hc:BlockAt b program base)
    (hbranch:program[branchPC]?=some (.branchLT l r yes no))
    (hjump:program[jumpPC]?=some (.jump target)) (htarget:target≤B)
    (hbase:base+b.length=jumpPC) (hcode:base+b.length≤B)
    (hpc:s.pc=branchPC) (hgo:(if s.natReg l<s.natReg r then yes else no)=base)
    (hr:readable b (setPC s base)) (hv:peak b (setPC s base)≤B)
    (hs:WordBound B s) :
    BoundedRuns program n x B s (b.length+2)
      (setPC (applyBlock b (setPC s base)) target) := by
  let e:=setPC s base
  have he:WordBound B e:=changePC_bound B s base hs (by omega)
  have body:=block_runs b program base n B x e hc rfl he hcode hr hv
  have bp:(applyBlock b e).pc=jumpPC:=by rw [applyBlock_pc];exact hbase
  have jump:BoundedRuns program n x B (applyBlock b e) 1
      (setPC (applyBlock b e) target):=.next body.final_bound
    (by rw [UniformMachine.step,bp,hjump];rfl)
    (.refl (changePC_bound B _ target body.final_bound htarget))
  have first:BoundedRuns program n x B s 1 e:=.next hs (by
    simp [UniformMachine.step,hpc,hbranch,hgo,e,setPC]) (.refl he)
  simpa only [e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    first.trans (body.trans jump)

theorem safe_enter (n B : ℕ) (x : Fin n→ℂ) (s : State) (hB:66≤B)
    (h:EntrySafe B s) (hs:WordBound B s) :
    BoundedRuns program n x B s 9 (entered s) := by
  let e:=setPC s 9
  have he:WordBound B e:=changePC_bound B s 9 hs (by omega)
  have body:=block_runs enterBlock program 9 n B x e enter_code rfl he
    (by rw [enter_length];omega) h.readable h.peak
  have first:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [UniformMachine.step,h.pc,entry_branch,h.go,e,setPC]) (.refl he)
  simpa only [enter_length,entered,e] using first.trans body

theorem safe_child (n B : ℕ) (x : Fin n→ℂ) (s : State) (hB:66≤B)
    (h:DescentSafe B s) (hs:WordBound B s) :
    BoundedRuns program n x B s 22 (child s) := by
  simpa only [child_length,child] using branched_block childBlock 18 17 38 8 18 46 3 4
    n B x s child_code child_branch child_jump (by omega) rfl (by rw [child_length];omega)
    h.pc (by simp [h.go]) h.readable h.peak hs

theorem safe_leaf (n B : ℕ) (x : Fin n→ℂ) (s : State) (hB:66≤B)
    (h:LeafSafe B s) (hs:WordBound B s) :
    BoundedRuns program n x B s 8 (leaf s) := by
  simpa only [leaf_length,leaf] using branched_block leafBlock 39 8 45 46 9 39 0 1
    n B x s leaf_code entry_branch leaf_jump (by omega) rfl (by rw [leaf_length];omega)
    h.pc (by simp [h.go]) h.readable h.peak hs

theorem safe_pop (n B : ℕ) (x : Fin n→ℂ) (s : State) (hB:66≤B)
    (h:ReturnSafe B s) (hs:WordBound B s) :
    BoundedRuns program n x B s 19 (popped s) := by
  simpa only [pop_length,popped] using branched_block popBlock 47 46 64 17 47 65 13 0
    n B x s pop_code pop_branch pop_jump (by omega) rfl (by rw [pop_length];omega)
    h.pc (by simp [h.go]) h.readable h.peak hs

theorem safe_exhausted (n B : ℕ) (x : Fin n→ℂ) (s : State) (hB:66≤B)
    (h:Exhausted s) (hs:WordBound B s) :
    BoundedRuns program n x B s 1 (setPC s 46) :=
  .next hs (by simp [UniformMachine.step,h.pc,child_branch,h.stop,setPC])
    (.refl (changePC_bound B s 46 hs (by omega)))

/-- This is an explicit recursive *safety* certificate, not a table/action
    oracle. It spells out present reads and integer bounds at every actual
    state reached by the literal reference evaluation. Deriving it uniformly
    from one incoming physical bank layout is discharged directly by
    `physical_tree` below. -/
def ChildrenSafe (B : ℕ) (visit : State→State) (valid : State→Prop) : ℕ→State→Prop
  | 0,s=>Exhausted s
  | k+1,s=>DescentSafe B s ∧ valid (child s) ∧ ReturnSafe B (visit (child s)) ∧
      ChildrenSafe B visit valid k (popped (visit (child s)))
def TreeSafe (B : ℕ) : List ℕ→State→Prop
  | [],s=>LeafSafe B s
  | r::rs,s=>EntrySafe B s ∧ ChildrenSafe B (tree rs) (TreeSafe B rs) r (entered s)

theorem children_bounded (B n : ℕ) (x : Fin n→ℂ) (visit : State→State)
    (valid : State→Prop) (cost : ℕ) (hB:66≤B)
    (hv:∀s,valid s→WordBound B s→BoundedRuns program n x B s cost (visit s))
    (k : ℕ) (s : State) (h:ChildrenSafe B visit valid k s) (hs:WordBound B s) :
    BoundedRuns program n x B s (1+k*(cost+41)) (children visit k s) := by
  induction k generalizing s with
  | zero => simpa [children] using safe_exhausted n B x s hB h hs
  | succ k ih =>
    have descend:=safe_child n B x s hB h.1 hs
    have sub:=hv (child s) h.2.1 descend.final_bound
    have ret:=safe_pop n B x (visit (child s)) hB h.2.2.1 sub.final_bound
    have rest:=ih (popped (visit (child s))) h.2.2.2 ret.final_bound
    have eq:22+(cost+(19+(1+k*(cost+41))))=1+(k+1)*(cost+41):=by ring
    simpa only [children,eq] using descend.trans (sub.trans (ret.trans rest))

/-- The entire recursive reference computation is executed by the same
    fixed66 instructions, with exact charged count and every word bounded. -/
theorem tree_bounded (rs : List ℕ) (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (hB:66≤B) (h:TreeSafe B rs s) (hs:WordBound B s) :
    BoundedRuns program n x B s (treeCost rs) (tree rs s) := by
  induction rs generalizing s with
  | nil => exact safe_leaf n B x s hB h hs
  | cons r rs ih =>
    have entry:=safe_enter n B x s hB h.1 hs
    have rest:=children_bounded B n x (tree rs) (TreeSafe B rs) (treeCost rs) hB
      (fun t ht hb=>ih t ht hb) r (entered s) h.2 entry.final_bound
    simpa only [tree,treeCost,show 9+(1+r*(treeCost rs+41))=10+r*(treeCost rs+41) by omega]
      using entry.trans rest

theorem treeCost_bound (rs : List ℕ) : treeCost rs+10≤51*UniformTraversal.nodeCount rs+10 := by
  have h:=treeCost_balance rs;omega

theorem treeCost_linear (rs : List ℕ) (C : ℕ)
    (h:UniformTraversal.nodeCount rs≤C*rs.prod) : treeCost rs+10≤51*C*rs.prod+10 := by
  have b:=treeCost_bound rs
  have e:51*UniformTraversal.nodeCount rs≤51*(C*rs.prod):=Nat.mul_le_mul_left 51 h
  simpa only [Nat.mul_assoc] using b.trans (Nat.add_le_add_right e 10)

/-- Roots/output/high-register frames hold for the literal traversal even
    independently of its safety proof. -/
theorem children_frame (visit : State→State) (h:∀s,Frame s (visit s)) (k : ℕ) (s : State) :
    Frame s (children visit k s) := by
  induction k generalizing s with
  | zero => exact frame_refl s
  | succ k ih =>
    have a:Frame s (child s):=(all_blocks_frame s).2.2.1
    have b:=h (child s)
    have c:Frame (visit (child s)) (popped (visit (child s))):=
      (all_blocks_frame (visit (child s))).2.2.2.2
    exact frame_trans (frame_trans (frame_trans a b) c) (ih _)
theorem tree_frame (rs : List ℕ) (s : State) : Frame s (tree rs s) := by
  induction rs generalizing s with
  | nil => exact (all_blocks_frame s).2.2.2.1
  | cons r rs ih =>
    exact frame_trans (all_blocks_frame s).2.1 (children_frame (tree rs) ih r (entered s))


/-- A concrete disjoint physical layout. Read-only tables and input lie below
    their stacks; the destination lies above the complete scalar stack. -/
structure Layout where
  B : ℕ
  ell : ℕ
  row : ℕ
  natStack : ℕ
  scalarStack : ℕ
  source : ℕ
  destination : ℕ
  volume : ℕ
  codeBound : 66≤B
  rowsBelow : row+ell*3≤natStack
  natStackBound : natStack+ell*3≤B
  scalarStackBound : scalarStack+ell≤B
  sourceBelow : source+volume≤ scalarStack
  destinationAbove : scalarStack+ell≤destination
  destinationBound : destination+volume≤B

structure Headers (L : Layout) (s : State) : Prop where
  axes : s.natReg 1=L.ell
  row : s.natReg 5=L.row
  natStack : s.natReg 6=L.natStack
  source : s.natReg 7=L.source
  destination : s.natReg 15=L.destination
  scalarStack : s.natReg 16=L.scalarStack
  one : s.natReg 9=1
  three : s.natReg 10=3
  zero : s.natReg 13=0

theorem headers_setPC (L : Layout) (s : State) (h:Headers L s) (pc : ℕ) :
    Headers L (setPC s pc) :=
  ⟨h.axes,h.row,h.natStack,h.source,h.destination,h.scalarStack,h.one,h.three,h.zero⟩

def Rows (axes : List Axis) (d b : ℕ) (s : State) : Prop := match axes with
  | []=>True
  | a::tail=>s.natHeap (b+d*3)=some a.radix ∧
      s.natHeap (b+d*3+1)=some a.permutationBase ∧
      s.natHeap (b+d*3+2)=some a.coefficientBase ∧ Rows tail (d+1) b s
structure Banks (axes : List Axis) (d : ℕ) (L : Layout) (s : State) : Prop where
  rows : Rows axes d L.row s
  permutation : ∀a∈axes,∀i:Fin a.radix,
    s.natHeap (a.permutationBase+i.val)=some (a.permutation i).val
  coefficient : ∀a∈axes,∀i:Fin a.radix,
    s.scalarHeap (a.coefficientBase+i.val)=some (prepared (a.coefficient i))
  permutationBelow : ∀a∈axes,a.permutationBase+a.radix≤L.natStack
  coefficientBelow : ∀a∈axes,a.coefficientBase+a.radix≤L.scalarStack

theorem rows_transfer (axes : List Axis) (d : ℕ) (L : Layout) (s t : State)
    (hlen:d+axes.length≤L.ell) (h:Rows axes d L.row s)
    (hf:∀a,a<L.natStack→t.natHeap a=s.natHeap a) : Rows axes d L.row t := by
  induction axes generalizing d with
  | nil => trivial
  | cons a tail ih =>
    have hd:d<L.ell:=by simp only [List.length_cons] at hlen;omega
    have hrow:L.row+d*3+2<L.natStack:=by have b:=L.rowsBelow;omega
    refine ⟨?_,?_,?_,ih (d+1) (by simp only [List.length_cons] at hlen;omega) h.2.2.2⟩
    · rw [hf _ (by omega)];exact h.1
    · rw [hf _ (by omega)];exact h.2.1
    · rw [hf _ hrow];exact h.2.2.1

theorem banks_transfer (axes : List Axis) (d : ℕ) (L : Layout) (s t : State)
    (hlen:d+axes.length≤L.ell) (h:Banks axes d L s)
    (hn:∀a,a<L.natStack→t.natHeap a=s.natHeap a)
    (hc:∀a,a<L.scalarStack→t.scalarHeap a=s.scalarHeap a) : Banks axes d L t := by
  refine ⟨rows_transfer axes d L s t hlen h.rows hn,?_,?_,h.permutationBelow,h.coefficientBelow⟩
  · intro a ha i
    rw [hn _ (by have b:=h.permutationBelow a ha;have bi:=i.isLt;omega)]
    exact h.permutation a ha i
  · intro a ha i
    rw [hc _ (by have b:=h.coefficientBelow a ha;have bi:=i.isLt;omega)]
    exact h.coefficient a ha i

theorem banks_tail (a : Axis) (axes : List Axis) (d : ℕ) (L : Layout) (s : State)
    (h:Banks (a::axes) d L s) : Banks axes (d+1) L s := by
  refine ⟨h.rows.2.2.2,?_,?_,?_,?_⟩
  · intro b hb i;exact h.permutation b (by simp [hb]) i
  · intro b hb i;exact h.coefficient b (by simp [hb]) i
  · intro b hb;exact h.permutationBelow b (by simp [hb])
  · intro b hb;exact h.coefficientBelow b (by simp [hb])

/-- Exact tensor paths: each edge performs the two Horner updates and one
    prepared scalar multiplication. This relation contains no RAM callback. -/
inductive Path : List Axis→ℕ→ℕ→ℂ→ℕ→ℕ→ℂ→Prop where
  | nil (I P : ℕ) (c : ℂ) : Path [] I P c I P c
  | cons {axes : List Axis} (a : Axis) (i : Fin a.radix) {I P J Q : ℕ} {c z : ℂ}
      (tail:Path axes (I*a.radix+i.val) (P*a.radix+(a.permutation i).val)
        (c*a.coefficient i) J Q z) : Path (a::axes) I P c J Q z

theorem volume_positive (axes : List Axis) : 0<(radices axes).prod := by
  induction axes with
  | nil => simp [radices]
  | cons a axes ih => simpa only [radices,List.map_cons,List.prod_cons] using
      (Nat.mul_pos a.positive ih)

theorem path_bounds {axes : List Axis} {I P J Q : ℕ} {c z : ℂ}
    (h:Path axes I P c J Q z) :
    I*(radices axes).prod≤J ∧ J<(I+1)*(radices axes).prod ∧
    P*(radices axes).prod≤Q ∧ Q<(P+1)*(radices axes).prod := by
  induction h with
  | nil I P c => simp [radices]
  | @cons axes a i I P J Q c z h ih =>
    have hi:=i.isLt
    have hp:=(a.permutation i).isLt
    have hv:=volume_positive axes
    change I*(a.radix*(radices axes).prod)≤J ∧ J<(I+1)*(a.radix*(radices axes).prod) ∧
      P*(a.radix*(radices axes).prod)≤Q ∧ Q<(P+1)*(a.radix*(radices axes).prod)
    rcases ih with ⟨hJ,hJ',hQ,hQ'⟩
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- Distinct digit blocks have disjoint destination intervals, including
    nonidentity permutations and unit radices. -/
theorem block_disjoint (p A B q : ℕ) (hne:A≠B)
    (hq:A*p≤q) (hq':q<(A+1)*p) : q<B*p ∨ (B+1)*p≤q := by
  rcases lt_or_gt_of_ne hne with h|h
  · left
    have h':A+1≤B:=by omega
    exact hq'.trans_le (Nat.mul_le_mul_right p h')
  · right
    exact (Nat.mul_le_mul_right p (show B+1≤A by omega)).trans hq

theorem headers_blocks (L : Layout) (s : State) (h:Headers L s) :
    Headers L (entered s) ∧ Headers L (child s) ∧ Headers L (leaf s) ∧ Headers L (popped s) := by
  rcases h with ⟨hA,hR,hN,hS,hD,hT,h1,h3,h0⟩
  constructor
  · constructor <;> simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
      hA,hR,hN,hS,hD,hT,h1,h3,h0]
  constructor
  · constructor <;> simp [child,setPC,applyBlock,childBlock,Op.apply,writeNat,writeScalar,next,
      hA,hR,hN,hS,hD,hT,h1,h3,h0]
  constructor
  · constructor <;> simp [leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,writeScalar,next,
      hA,hR,hN,hS,hD,hT,h1,h3,h0]
  · constructor <;> simp [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,writeScalar,next,
      hA,hR,hN,hS,hD,hT,h1,h3,h0]

/-- Footprints include only stack cells and the current tensor destination
    block. They make the preservation of earlier sibling writes explicit. -/
structure Effect (axes : List Axis) (d I P count : ℕ) (c : ℂ) (L : Layout)
    (s t : State) : Prop where
  pc : t.pc=46
  headers : Headers L t
  cursor : Cursor d I P c t
  count : t.natReg 8=count+(radices axes).prod
  natFrame : ∀a,a<L.natStack+d*3 ∨ L.natStack+L.ell*3≤a→t.natHeap a=s.natHeap a
  scalarLow : ∀a,a<L.scalarStack+d→t.scalarHeap a=s.scalarHeap a
  scalarFrame : ∀a,(a<L.scalarStack+d ∨ L.scalarStack+L.ell≤a)→
    (a<L.destination+P*(radices axes).prod ∨ L.destination+(P+1)*(radices axes).prod≤a)→
    t.scalarHeap a=s.scalarHeap a
  output : ∀J Q z,Path axes I P c J Q z→∀v,
    s.scalarHeap (L.source+J)=some v→t.scalarHeap (L.destination+Q)=some (product z v)


def SourceAt (L : Layout) (s : State) : Prop :=
  ∀J,J<L.volume→∃v,s.scalarHeap (L.source+J)=some v
def Fits (axes : List Axis) (I P count : ℕ) (L : Layout) : Prop :=
  (I+1)*(radices axes).prod≤L.volume ∧
  (P+1)*(radices axes).prod≤L.volume ∧ count+(radices axes).prod≤L.volume

theorem source_transfer (L : Layout) (s t : State) (h:SourceAt L s)
    (hf:∀a,a<L.scalarStack→t.scalarHeap a=s.scalarHeap a) : SourceAt L t := by
  intro J hJ
  rw [hf _ (by have b:=L.sourceBelow;omega)]
  exact h J hJ

theorem entered_cursor (_L : Layout) (d I P count : ℕ) (c : ℂ) (s : State)
    (hc:Cursor d I P c s) (hcount:s.natReg 8=count) :
    Cursor d I P c (entered s) ∧ (entered s).natReg 8=count := by
  simpa [Cursor,entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next] using
    And.intro hc hcount

theorem child_nat_frame (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) (ell j : ℕ) (hd:d<ell)
    (hj:j<N+d*3 ∨ N+ell*3≤j) : (child s).natHeap j=s.natHeap j := by
  rw [(child_properties d I P r i pi p a N S c k s h).2.2.2.1]
  simp (disch:=omega) [Function.update_of_ne]

theorem child_scalar_frame (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) (ell j : ℕ) (hd:d<ell)
    (hj:j<S+d ∨ S+ell≤j) : (child s).scalarHeap j=s.scalarHeap j := by
  rw [(child_properties d I P r i pi p a N S c k s h).2.2.2.2]
  simp (disch:=omega) [Function.update_of_ne]

theorem child_saved (d I P r i pi p a N S : ℕ) (c k : ℂ) (s : State)
    (h:ChildReady d I P r i pi p a N S c k s) :
    (child s).natHeap (N+d*3)=some I ∧
    (child s).natHeap (N+d*3+1)=some P ∧
    (child s).natHeap (N+d*3+2)=some (i+1) ∧
    (child s).scalarHeap (S+d)=some (prepared c) := by
  have e:=child_properties d I P r i pi p a N S c k s h
  rw [e.2.2.2.1,e.2.2.2.2]
  simp (disch:=omega) [Function.update_of_ne]

theorem child_fits (a : Axis) (axes : List Axis) (I P count : ℕ) (i : Fin a.radix)
    (L : Layout) (hI:(I+1)*(radices (a::axes)).prod≤L.volume)
    (hP:(P+1)*(radices (a::axes)).prod≤L.volume)
    (hcount:count+(radices axes).prod≤L.volume) :
    Fits axes (I*a.radix+i.val) (P*a.radix+(a.permutation i).val) count L := by
  change (I+1)*(a.radix*(radices axes).prod)≤L.volume at hI
  change (P+1)*(a.radix*(radices axes).prod)≤L.volume at hP
  have hi:=i.isLt
  have hp:=(a.permutation i).isLt
  refine ⟨?_,?_,hcount⟩
  · calc
      (I*a.radix+i.val+1)*(radices axes).prod
        ≤ ((I+1)*a.radix)*(radices axes).prod:=
          Nat.mul_le_mul_right _ (by nlinarith)
      _=(I+1)*(a.radix*(radices axes).prod):=by ring
      _≤L.volume:=hI
  · calc
      (P*a.radix+(a.permutation i).val+1)*(radices axes).prod
        ≤ ((P+1)*a.radix)*(radices axes).prod:=
          Nat.mul_le_mul_right _ (by nlinarith)
      _=(P+1)*(a.radix*(radices axes).prod):=by ring
      _≤L.volume:=hP

theorem child_ready_of_banks (a : Axis) (axes : List Axis) (d I P : ℕ) (c : ℂ)
    (i : Fin a.radix) (L : Layout) (s : State) (hh:Headers L s) (hc:Cursor d I P c s)
    (hr:s.natReg 4=a.radix) (hi:s.natReg 3=i.val)
    (hp:s.natReg 18=a.permutationBase) (ha:s.natReg 17=a.coefficientBase)
    (hb:Banks (a::axes) d L s) :
    ChildReady d I P a.radix i.val (a.permutation i).val a.permutationBase a.coefficientBase
      L.natStack L.scalarStack c (a.coefficient i) s := by
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hr,hi,hp,ha,hh.natStack,hh.scalarStack,hh.one,hh.three,
    hc.2.2.2,hb.permutation a (by simp) i,hb.coefficient a (by simp) i,?_,?_⟩
  · have h:=hb.permutationBelow a (by simp);have h':=i.isLt;omega
  · have h:=hb.coefficientBelow a (by simp);have h':=i.isLt;omega

theorem physical_leaf (L : Layout) (n d I P count : ℕ) (x : Fin n→ℂ) (c : ℂ) (s : State)
    (hpc:s.pc=8) (hh:Headers L s) (hc:Cursor d I P c s) (hcount:s.natReg 8=count)
    (hd:d=L.ell) (hfits:Fits [] I P count L) (hsrc:SourceAt L s) (hs:WordBound L.B s) :
    BoundedRuns program n x L.B s 8 (leaf s) ∧ Effect [] d I P count c L s (leaf s) := by
  have hI:I<L.volume:=by simpa [Fits,radices] using hfits.1
  obtain ⟨v,hv⟩:=hsrc I hI
  have run:=leaf_bounded n L.B x s c v hpc (by rw [hc.1,hh.axes,hd];omega) hh.one
    hc.2.2.2 (by simpa only [hh.source,hc.2.1] using hv) L.codeBound
    (by have b:=L.destinationBound;have hP:=hfits.2.1;simp [radices] at hP
        rw [hh.destination,hc.2.2.1];omega)
    (by have b:=L.destinationBound;have hC:=hfits.2.2;simp [radices] at hC
        rw [hcount];omega) hs
  have e:=leaf_effect s c v hh.one hc.2.2.2 (by simpa only [hh.source,hc.2.1] using hv)
  have heap:(leaf s).scalarHeap=Function.update s.scalarHeap (L.destination+P) (some (product c v)):=by
    simpa only [hh.destination,hc.2.2.1] using e.2.2.1
  refine ⟨run,⟨e.1,(headers_blocks L s hh).2.2.1,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa [Cursor,leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,writeScalar,next] using hc
  · simpa [radices,hcount] using e.2.1
  · intro a _;exact congrFun e.2.2.2.1 a
  · intro a ha
    rw [heap,Function.update_of_ne]
    have b:=L.destinationAbove;omega
  · intro a _ ha
    rw [heap,Function.update_of_ne]
    simp only [radices,List.map_nil,List.prod_nil,Nat.mul_one] at ha
    omega
  · intro J Q z hp v' hv'
    cases hp
    have hvv:v'=v:=by rw [hv] at hv';exact Option.some.inj hv'.symm
    subst v'
    simp [heap]


/-- Loop footprints use the actual local permutation. A later sibling may
    overwrite neither a completed sibling block nor a read-only bank. -/
structure LoopEffect (a : Axis) (axes : List Axis) (d I P count i k : ℕ) (c : ℂ)
    (L : Layout) (s t : State) : Prop where
  pc : t.pc=46
  headers : Headers L t
  cursor : Cursor d I P c t
  count : t.natReg 8=count+k*(radices axes).prod
  natFrame : ∀b,b<L.natStack+d*3 ∨ L.natStack+L.ell*3≤b→t.natHeap b=s.natHeap b
  scalarLow : ∀b,b<L.scalarStack+d→t.scalarHeap b=s.scalarHeap b
  scalarFrame : ∀b,(b<L.scalarStack+d ∨ L.scalarStack+L.ell≤b)→
    (∀j:Fin a.radix,i ≤ j.val→j.val < i + k→
      b<L.destination+(P*a.radix+(a.permutation j).val)*(radices axes).prod ∨
      L.destination+(P*a.radix+(a.permutation j).val+1)*(radices axes).prod≤b)→
    t.scalarHeap b=s.scalarHeap b
  output : ∀j:Fin a.radix,i ≤ j.val→j.val < i + k→∀J Q z,
    Path axes (I*a.radix+j.val) (P*a.radix+(a.permutation j).val)
      (c*a.coefficient j) J Q z→∀v,
    s.scalarHeap (L.source+J)=some v→t.scalarHeap (L.destination+Q)=some (product z v)

def PhysicalTree (visit : State→State) (axes : List Axis) : Prop :=
  ∀(L : Layout) (n d I P count : ℕ) (x : Fin n→ℂ) (c : ℂ) (s : State),
    s.pc=8→Headers L s→Cursor d I P c s→s.natReg 8=count→d+axes.length=L.ell→
    Banks axes d L s→Fits axes I P count L→SourceAt L s→WordBound L.B s→
    BoundedRuns program n x L.B s (treeCost (radices axes)) (visit s) ∧
      Effect axes d I P count c L s (visit s)

theorem layout_volume_bound (L : Layout) : L.volume≤L.B := by
  have h:=L.destinationBound;omega

theorem physical_child_bounds (a : Axis) (axes : List Axis) (d I P count : ℕ)
    (i : Fin a.radix) (L : Layout) (s : State) (hlen:d+(a::axes).length=L.ell)
    (h:Banks (a::axes) d L s) (hf:Fits axes (I*a.radix+i.val)
      (P*a.radix+(a.permutation i).val) count L) (hs:WordBound L.B s) :
    ChildBounds L.B d I P a.radix i.val (a.permutation i).val a.permutationBase
      a.coefficientBase L.natStack L.scalarStack := by
  have hd:d+1≤L.ell:=by simp only [List.length_cons] at hlen;omega
  have hN:=L.natStackBound
  have hS:=L.scalarStackBound
  have hV:=layout_volume_bound L
  have hp:=volume_positive axes
  have hI:=hf.1
  have hP:=hf.2.1
  have hrB:a.radix≤L.B:=(hs.2.2.1 _ _ h.rows.1).2
  have hi:=i.isLt
  have hn:=h.permutationBelow a (by simp)
  have hc:=h.coefficientBelow a (by simp)
  refine ⟨by omega,by omega,by omega,by omega,?_,?_,by omega,by omega⟩
  · nlinarith
  · nlinarith

theorem pop_heaps (s : State) : (popped s).natHeap=s.natHeap ∧ (popped s).scalarHeap=s.scalarHeap := by
  simp [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,writeScalar,next]
theorem enter_heaps (s : State) : (entered s).natHeap=s.natHeap ∧ (entered s).scalarHeap=s.scalarHeap := by
  simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next]


/-- The physical-bank induction: every child reads a real prepared entry,
    and every pop reads the three exact parent values that were stored. -/
theorem physical_children (visit : State→State) (axes : List Axis) (hv:PhysicalTree visit axes)
    (a : Axis) (L : Layout) (n d I P count i k : ℕ) (x : Fin n→ℂ) (c : ℂ) (s : State)
    (hpc:s.pc=17) (hh:Headers L s) (hcursor:Cursor d I P c s) (hcount:s.natReg 8=count)
    (hi:s.natReg 3=i) (hr:s.natReg 4=a.radix) (hp:s.natReg 18=a.permutationBase)
    (ha:s.natReg 17=a.coefficientBase) (hlen:d+(a::axes).length=L.ell)
    (hik:i+k=a.radix) (hb:Banks (a::axes) d L s)
    (hI:(I+1)*(radices (a::axes)).prod≤L.volume)
    (hP:(P+1)*(radices (a::axes)).prod≤L.volume)
    (hC:count+k*(radices axes).prod≤L.volume)
    (hsrc:SourceAt L s) (hs:WordBound L.B s) :
    BoundedRuns program n x L.B s (1+k*(treeCost (radices axes)+41)) (children visit k s) ∧
      LoopEffect a axes d I P count i k c L s (children visit k s) := by
  induction k generalizing s count i with
  | zero =>
    have stop:Exhausted s:=⟨hpc,by rw [hi,hr];omega⟩
    refine ⟨by simpa [children] using safe_exhausted n L.B x s L.codeBound stop hs,?_,⟩
    refine ⟨rfl,headers_setPC L s hh 46,hcursor,by simpa [children,setPC] using hcount,?_,?_,?_,?_⟩
    · intro b _;rfl
    · intro b _;rfl
    · intro b _ _;rfl
    · intro j hj hj' J Q z path v value;omega
  | succ k ih =>
    have hd:d<L.ell:=by simp only [List.length_cons] at hlen;omega
    let digit:Fin a.radix:=⟨i,by omega⟩
    have ready:=child_ready_of_banks a axes d I P c digit L s hh hcursor hr hi hp ha hb
    have ht:count+(radices axes).prod≤L.volume:=by
      have :count+(radices axes).prod≤count+(k+1)*(radices axes).prod:=by
        simp only [Nat.add_mul,Nat.one_mul];omega
      exact this.trans hC
    have fits:=child_fits a axes I P count digit L hI hP ht
    have bounds:=physical_child_bounds a axes d I P count digit L s hlen hb fits hs
    have descent:=child_bounded n L.B d I P a.radix digit.val (a.permutation digit).val
      a.permutationBase a.coefficientBase L.natStack L.scalarStack x c (a.coefficient digit)
      s ready hpc digit.isLt L.codeBound bounds hs
    have cp:=child_properties d I P a.radix digit.val (a.permutation digit).val
      a.permutationBase a.coefficientBase L.natStack L.scalarStack c (a.coefficient digit) s ready
    have cHeaders:Headers L (child s):=(headers_blocks L s hh).2.1
    have cBanks:Banks (a::axes) d L (child s):=banks_transfer (a::axes) d L s (child s)
      (by omega) hb
      (fun b h=>child_nat_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd (Or.inl (by omega)))
      (fun b h=>child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd (Or.inl (by omega)))
    have cSource:SourceAt L (child s):=source_transfer L s (child s) hsrc
      (fun b h=>child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd (Or.inl (by omega)))
    obtain ⟨sub,e⟩:=hv L n (d+1) (I*a.radix+digit.val) (P*a.radix+(a.permutation digit).val)
      count x (c*a.coefficient digit) (child s) cp.1 cHeaders cp.2.1 (cp.2.2.1.trans hcount)
      (by simp only [List.length_cons] at hlen;omega) (banks_tail a axes d L (child s) cBanks)
      fits cSource descent.final_bound
    have eBanks:Banks (a::axes) d L (visit (child s)):=banks_transfer (a::axes) d L (child s)
      (visit (child s)) (by omega) cBanks
      (fun b h=>e.natFrame b (Or.inl (by omega)))
      (fun b h=>e.scalarLow b (by omega))
    have saved:=child_saved d I P a.radix digit.val (a.permutation digit).val a.permutationBase
      a.coefficientBase L.natStack L.scalarStack c (a.coefficient digit) s ready
    have retReady:PopReady d I P (i+1) a.radix a.permutationBase a.coefficientBase L.row
        L.natStack L.scalarStack c (visit (child s)):=by
      refine ⟨e.cursor.1,e.headers.one,e.headers.three,e.headers.zero,e.headers.row,
        e.headers.natStack,e.headers.scalarStack,?_,?_,?_,?_,eBanks.rows.1,
        eBanks.rows.2.1,eBanks.rows.2.2.1⟩
      · exact (e.natFrame _ (Or.inl (by omega))).trans saved.1
      · exact (e.natFrame _ (Or.inl (by omega))).trans saved.2.1
      · exact (e.natFrame _ (Or.inl (by omega))).trans saved.2.2.1
      · exact (e.scalarLow _ (by omega)).trans saved.2.2.2
    have ret:=pop_bounded n L.B d I P (i+1) a.radix a.permutationBase a.coefficientBase L.row
      L.natStack L.scalarStack x c (visit (child s)) retReady e.pc L.codeBound
      (by have b:=L.natStackBound;omega)
      (by have b:=L.rowsBelow;have b':=L.natStackBound;omega)
      (by have b:=L.scalarStackBound;omega) sub.final_bound
    let t:=popped (visit (child s))
    have pp:=pop_properties d I P (i+1) a.radix a.permutationBase a.coefficientBase L.row
      L.natStack L.scalarStack c (visit (child s)) retReady
    have tHeaders:Headers L t:=(headers_blocks L (visit (child s)) e.headers).2.2.2
    have tBanks:Banks (a::axes) d L t:=by
      exact banks_transfer (a::axes) d L _ _ (by omega) eBanks
        (fun b _=>congrFun (pop_heaps _).1 b) (fun b _=>congrFun (pop_heaps _).2 b)
    have tSource:SourceAt L t:=source_transfer L _ _ (source_transfer L _ _ cSource
      (fun b h=>e.scalarLow b (by omega))) (fun b _=>congrFun (pop_heaps _).2 b)
    have tCount:t.natReg 8=count+(radices axes).prod:=pp.2.2.2.2.2.2.1.trans e.count
    obtain ⟨rest,f⟩:=ih (count+(radices axes).prod) (i+1) t pp.1 tHeaders pp.2.1 tCount
      pp.2.2.1 pp.2.2.2.1 pp.2.2.2.2.1 pp.2.2.2.2.2.1 (by omega) tBanks
      (by convert hC using 1;ring) tSource ret.final_bound
    have eq:22+(treeCost (radices axes)+(19+(1+k*(treeCost (radices axes)+41))))=
        1+(k+1)*(treeCost (radices axes)+41):=by ring
    rw [show children visit (k+1) s=children visit k t by rfl]
    refine ⟨by simpa only [eq] using descent.trans (sub.trans (ret.trans rest)),?_,⟩
    refine ⟨f.pc,f.headers,f.cursor,?_,?_,?_,?_,?_⟩
    · rw [f.count];ring
    · intro b h
      rw [f.natFrame b h,show t.natHeap=(visit (child s)).natHeap from (pop_heaps _).1,
        e.natFrame b (by rcases h with h|h;exact Or.inl (by omega);exact Or.inr h)]
      exact child_nat_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd h
    · intro b h
      rw [f.scalarLow b h,show t.scalarHeap=(visit (child s)).scalarHeap from (pop_heaps _).2,
        e.scalarLow b (by omega)]
      exact child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd (Or.inl h)
    · intro b hstack hfoot
      rw [f.scalarFrame b hstack (by intro j hj hj';exact hfoot j (by omega) (by omega)),
        show t.scalarHeap=(visit (child s)).scalarHeap from (pop_heaps _).2,
        e.scalarFrame b (by rcases hstack with h|h;exact Or.inl (by omega);exact Or.inr h)
          (hfoot digit (by simp [digit]) (by simp [digit]))]
      exact child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell b hd hstack
    · intro j hj hj' J Q z path v value
      have hJ:J<L.volume:=(path_bounds (Path.cons a j path)).2.1.trans_le hI
      have sourceLow:L.source+J<L.scalarStack:=by have b:=L.sourceBelow;omega
      by_cases hji:j.val=i
      · have heq:j=digit:=Fin.ext hji
        subst j
        have firstValue:(visit (child s)).scalarHeap (L.destination+Q)=some (product z v):=
          e.output J Q z path v (by
            rw [child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready L.ell _ hd
              (Or.inl (by omega))];exact value)
        have hQ:=(path_bounds path).2.2
        have frame:=f.scalarFrame (L.destination+Q)
            (Or.inr (by have b:=L.destinationAbove;omega)) (by
              intro j hlow _
              have hne:(a.permutation digit).val≠(a.permutation j).val:=by
                intro heq
                have e':digit=j:=a.permutation.injective (Fin.ext heq)
                have :=congrArg Fin.val e';simp only [digit] at this;omega
              have blocks:P*a.radix+(a.permutation digit).val≠P*a.radix+(a.permutation j).val:=by omega
              rcases block_disjoint (radices axes).prod _ _ Q blocks hQ.1 hQ.2 with h|h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega))
        rw [frame,show t.scalarHeap=(visit (child s)).scalarHeap from (pop_heaps _).2]
        exact firstValue
      · exact f.output j (by omega) (by omega) J Q z path v (by
          rw [show t.scalarHeap=(visit (child s)).scalarHeap from (pop_heaps _).2,
            e.scalarLow _ (by omega),child_scalar_frame _ _ _ _ _ _ _ _ _ _ _ _ _ ready
              L.ell _ hd (Or.inl (by omega))]
          exact value)


/-- Universal exact-width tensor traversal from one incoming physical bank.
    No per-node safety or action hypothesis remains. -/
theorem physical_tree (axes : List Axis) : PhysicalTree (tree (radices axes)) axes := by
  induction axes with
  | nil =>
    intro L n d I P count x c s hpc hh hc hcount hlen hb hf hsrc hs
    exact physical_leaf L n d I P count x c s hpc hh hc hcount (by simpa using hlen) hf hsrc hs
  | cons a axes ih =>
    intro L n d I P count x c s hpc hh hc hcount hlen hb hf hsrc hs
    have hd:d<L.ell:=by simp only [List.length_cons] at hlen;omega
    have entry:=enter_bounded n L.B d a.radix a.permutationBase a.coefficientBase x s hpc
      (by rw [hc.1,hh.axes];omega) hc.1 hh.one hh.three
      (by simpa only [hh.row] using hb.rows.1)
      (by simpa only [hh.row] using hb.rows.2.1)
      (by simpa only [hh.row] using hb.rows.2.2.1) L.codeBound
      (by have h:=L.rowsBelow;have h':=L.natStackBound;rw [hh.row];omega) hs
    have ep:=enter_properties s d a.radix a.permutationBase a.coefficientBase hc.1 hh.one hh.three
      (by simpa only [hh.row] using hb.rows.1)
      (by simpa only [hh.row] using hb.rows.2.1)
      (by simpa only [hh.row] using hb.rows.2.2.1)
    have eh:Headers L (entered s):=(headers_blocks L s hh).1
    have ec:=entered_cursor L d I P count c s hc hcount
    have eb:Banks (a::axes) d L (entered s):=banks_transfer (a::axes) d L s (entered s)
      (by omega) hb (fun b _=>congrFun (enter_heaps s).1 b) (fun b _=>congrFun (enter_heaps s).2 b)
    have es:SourceAt L (entered s):=source_transfer L s (entered s) hsrc
      (fun b _=>congrFun (enter_heaps s).2 b)
    obtain ⟨loop,e⟩:=physical_children (tree (radices axes)) axes ih a L n d I P count 0 a.radix x c
      (entered s) ep.1 eh ec.1 ec.2 ep.2.2.2.2.1 ep.2.1 ep.2.2.1 ep.2.2.2.1 hlen
      (by omega) eb hf.1 hf.2.1 (by simpa only [radices,List.map_cons,List.prod_cons] using hf.2.2)
      es entry.final_bound
    change BoundedRuns program n x L.B s
      (10+a.radix*(treeCost (radices axes)+41))
      (children (tree (radices axes)) a.radix (entered s)) ∧ _
    refine ⟨by simpa only [show 9+(1+a.radix*(treeCost (radices axes)+41))=
          10+a.radix*(treeCost (radices axes)+41) by omega] using entry.trans loop,?_,⟩
    refine ⟨e.pc,e.headers,e.cursor,?_,?_,?_,?_,?_⟩
    · exact e.count
    · intro b h
      exact (e.natFrame b h).trans (congrFun (enter_heaps s).1 b)
    · intro b h
      exact (e.scalarLow b h).trans (congrFun (enter_heaps s).2 b)
    · intro b hstack hfoot
      apply (e.scalarFrame b hstack ?_).trans (congrFun (enter_heaps s).2 b)
      intro j _ _
      have hj:=(a.permutation j).isLt
      change b<L.destination+P*(a.radix*(radices axes).prod) ∨
        L.destination+(P+1)*(a.radix*(radices axes).prod)≤b at hfoot
      rcases hfoot with h|h
      · left
        have b':P*(a.radix*(radices axes).prod)≤
            (P*a.radix+(a.permutation j).val)*(radices axes).prod:=by
          rw [←Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        exact h.trans_le (Nat.add_le_add_left b' _)
      · right
        have b':(P*a.radix+(a.permutation j).val+1)*(radices axes).prod≤
            (P+1)*(a.radix*(radices axes).prod):=by
          rw [←Nat.mul_assoc]
          apply Nat.mul_le_mul_right
          nlinarith
        exact (Nat.add_le_add_left b' _).trans h
    · intro J Q z path v value
      cases path with
      | cons a j tail =>
        exact e.output j (by omega) (by simp only [Nat.zero_add];exact j.isLt) J Q z tail v
          (by rw [(enter_heaps s).2];exact value)


/-- Incoming header values only; scratch constants/cursors may be dirty. -/
structure Call (L : Layout) (s : State) : Prop where
  axes : s.natReg 1=L.ell
  row : s.natReg 5=L.row
  natStack : s.natReg 6=L.natStack
  source : s.natReg 7=L.source
  destination : s.natReg 15=L.destination
  scalarStack : s.natReg 16=L.scalarStack

theorem call_initialized (L : Layout) (s : State) (h:Call L s) : Headers L (initialized s) := by
  rcases h with ⟨hA,hR,hN,hS,hD,hT⟩
  constructor <;> simp [initialized,applyBlock,boot,Op.apply,writeNat,writeScalar,next,
    hA,hR,hN,hS,hD,hT]

def finalState (axes : List Axis) (s : State) : State :=
  setPC (tree (radices axes) (initialized s)) 65

structure Result (axes : List Axis) (L : Layout) (s t : State) : Prop where
  pc : t.pc=65
  cursor : Cursor 0 0 0 1 t
  count : t.natReg 8=L.volume
  frame : Frame s t
  natFrame : ∀a,a<L.natStack ∨ L.natStack+L.ell*3≤a→t.natHeap a=s.natHeap a
  scalarLow : ∀a,a<L.scalarStack→t.scalarHeap a=s.scalarHeap a
  scalarFrame : ∀a,(a<L.scalarStack ∨ L.scalarStack+L.ell≤a)→
    (a<L.destination ∨ L.destination+L.volume≤a)→t.scalarHeap a=s.scalarHeap a
  output : ∀J Q z,Path axes 0 0 1 J Q z→∀v,
    s.scalarHeap (L.source+J)=some v→t.scalarHeap (L.destination+Q)=some (product z v)

/-- One fixed bytecode from dirty caller registers, including literal1 boot,
    every table/index/stack/field step, continuation and the final halt. -/
theorem complete_execution (axes : List Axis) (L : Layout) (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hell:L.ell=axes.length) (hvolume:L.volume=(radices axes).prod)
    (hcall:Call L s) (hb:Banks axes 0 L s) (hsrc:SourceAt L s) (hs:WordBound L.B s) :
    BoundedExecution program n x L.B s (treeCost (radices axes)+10) (finalState axes s) ∧
      Result axes L s (finalState axes s) := by
  have bootrun:=boot_bounded n L.B x s hpc L.codeBound hs
  have hp:=boot_properties s
  have headers:=call_initialized L s hcall
  have banks:Banks axes 0 L (initialized s):=banks_transfer axes 0 L s (initialized s)
    (by omega) hb (fun a _=>congrFun hp.2.2.2.1 a) (fun a _=>congrFun hp.2.2.2.2 a)
  have source:SourceAt L (initialized s):=source_transfer L s (initialized s) hsrc
    (fun a _=>congrFun hp.2.2.2.2 a)
  obtain ⟨run,e⟩:=physical_tree axes L n 0 0 0 0 x 1 (initialized s)
    (by rw [initialized,applyBlock_pc,boot_length,hpc]) headers hp.2.1 hp.2.2.1
    (by omega) banks (by simp [Fits,hvolume]) source bootrun.final_bound
  let t:=tree (radices axes) (initialized s)
  let u:=setPC t 65
  have ub:WordBound L.B u:=changePC_bound L.B t 65 run.final_bound (by have h:=L.codeBound;omega)
  have tail:BoundedExecution program n x L.B t 2 u:=by
    refine .next run.final_bound ?_ (.halt ub ?_)
    · simp [UniformMachine.step,e.pc,pop_branch,e.headers.zero,e.cursor.1,u,setPC,t]
    · simp [UniformMachine.step,u,setPC,halt_at]
  refine ⟨?_,?_,⟩
  · simpa only [finalState,t,u,show 8+(treeCost (radices axes)+2)=treeCost (radices axes)+10 by omega]
      using bootrun.executes (run.executes tail)
  · refine ⟨rfl,e.cursor,?_,?_,?_,?_,?_,?_⟩
    · simpa only [finalState,setPC,Nat.zero_add,←hvolume] using e.count
    · have f:=frame_trans (all_blocks_frame s).1 (tree_frame (radices axes) (initialized s))
      exact f
    · intro a ha
      simpa only [finalState,setPC,Nat.zero_mul,Nat.add_zero] using
        (e.natFrame a (by simpa only [Nat.zero_mul,Nat.add_zero] using ha)).trans
          (congrFun hp.2.2.2.1 a)
    · intro a ha
      exact (e.scalarLow a (by omega)).trans (congrFun hp.2.2.2.2 a)
    · intro a hstack hout
      exact (e.scalarFrame a (by simpa using hstack)
        (by simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.one_mul,←hvolume] using hout)).trans
          (congrFun hp.2.2.2.2 a)
    · intro J Q z path v value
      exact e.output J Q z path v (by rw [hp.2.2.2.2];exact value)

theorem complete_instruction_bound (axes : List Axis) :
    treeCost (radices axes)+10≤51*UniformTraversal.nodeCount (radices axes)+10 :=
  treeCost_bound (radices axes)

/-- A unit axis is permitted; the charged linear consequence uses only an
    actual node-count bound, rather than a false radix≥2 assumption. -/
theorem complete_linear_bound (axes : List Axis) (C : ℕ)
    (h:UniformTraversal.nodeCount (radices axes)≤C*(radices axes).prod) :
    treeCost (radices axes)+10≤51*C*(radices axes).prod+10 :=
  treeCost_linear (radices axes) C h


/-- Canonical role-outer mixed-radix tensor coordinates. These finite
    equivalences describe the semantics; the program uses carried ordinals. -/
def tensorPermutation : (axes : List Axis)→Fin (radices axes).prod≃Fin (radices axes).prod
  | []=>Equiv.refl _
  | a::axes=>(finProdFinEquiv.symm.trans
      (a.permutation.prodCongr (tensorPermutation axes))).trans finProdFinEquiv

def tensorCoefficient : (axes : List Axis)→Fin (radices axes).prod→ℂ
  | [],_=>1
  | a::axes,j=>a.coefficient (finProdFinEquiv.symm j).1 *
      tensorCoefficient axes (finProdFinEquiv.symm j).2

theorem canonical_path (axes : List Axis) (I P : ℕ) (c : ℂ)
    (j : Fin (radices axes).prod) :
    Path axes I P c (I*(radices axes).prod+j.val)
      (P*(radices axes).prod+(tensorPermutation axes j).val) (c*tensorCoefficient axes j) := by
  induction axes generalizing I P c with
  | nil =>
    have hj:j.val=0:=by have h:=j.isLt;change j.val<1 at h;omega
    change Path [] I P c (I*1+j.val) (P*1+j.val) (c*1)
    rw [hj]
    simpa using Path.nil I P c
  | cons a axes ih =>
    let pair:Fin a.radix×Fin (radices axes).prod:=finProdFinEquiv.symm j
    have hj:j.val=pair.2.val+(radices axes).prod*pair.1.val:=by
      have h:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
      change pair.2.val+(radices axes).prod*pair.1.val=j.val at h
      exact h.symm
    have hp:(tensorPermutation (a::axes) j).val=
        (tensorPermutation axes pair.2).val+(radices axes).prod*(a.permutation pair.1).val:=rfl
    have tail:=ih (I*a.radix+pair.1.val) (P*a.radix+(a.permutation pair.1).val)
      (c*a.coefficient pair.1) pair.2
    have path:=Path.cons a pair.1 tail
    convert path using 1
    · change I*(a.radix*(radices axes).prod)+j.val=
        (I*a.radix+pair.1.val)*(radices axes).prod+pair.2.val
      rw [hj];ring
    · change P*(a.radix*(radices axes).prod)+(tensorPermutation (a::axes) j).val=
        (P*a.radix+(a.permutation pair.1).val)*(radices axes).prod+(tensorPermutation axes pair.2).val
      rw [hp];ring
    · change c*(a.coefficient pair.1*tensorCoefficient axes pair.2)=
        (c*a.coefficient pair.1)*tensorCoefficient axes pair.2
      ring

/-- Whole tensor monomial, arbitrary input-dependent data tags, retained zero
    coefficients, all charged preparation reads/indices and dirty stacks. -/
theorem tensor_execution (axes : List Axis) (L : Layout) (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hell:L.ell=axes.length) (hvolume:L.volume=(radices axes).prod)
    (hcall:Call L s) (hb:Banks axes 0 L s) (hsrc:SourceAt L s) (hs:WordBound L.B s) :
    BoundedExecution program n x L.B s (treeCost (radices axes)+10) (finalState axes s) ∧
    Result axes L s (finalState axes s) ∧
    ∀j:Fin (radices axes).prod,∀v,s.scalarHeap (L.source+j.val)=some v→
      (finalState axes s).scalarHeap (L.destination+(tensorPermutation axes j).val)=
        some (product (tensorCoefficient axes j) v) := by
  obtain ⟨run,e⟩:=complete_execution axes L n x s hpc hell hvolume hcall hb hsrc hs
  refine ⟨run,e,?_,⟩
  intro j v hv
  have h:=e.output _ _ _ (canonical_path axes 0 0 1 j) v
  simpa only [Nat.zero_mul,Nat.zero_add,one_mul] using h (by simpa only [Nat.zero_mul,Nat.zero_add] using hv)


theorem instruction_bound_radices_two (axes : List Axis) (h:∀a∈axes,2≤a.radix) :
    treeCost (radices axes)+10≤102*(radices axes).prod+10 := by
  apply complete_linear_bound axes 2
  exact (UniformTraversal.nodeCount_lt_twice_product (radices axes) (by
    intro r hr
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
    exact h a ha)).le

theorem instruction_bound_unit_final (axes : List Axis) (last : Axis)
    (h:∀a∈axes,2≤a.radix) :
    treeCost (radices (axes++[last]))+10≤153*(radices (axes++[last])).prod+10 := by
  apply complete_linear_bound (axes++[last]) 3
  have nodes:=UniformSelectedDFSMachine.nodeCount_append_one (radices axes) last.radix last.positive
    (by intro r hr;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr;exact h a ha)
  have eq:radices (axes++[last])=radices axes++[last.radix]:=by simp [radices]
  rw [eq,List.prod_append]
  simp only [List.prod_cons,List.prod_nil,Nat.mul_one] at *
  omega

theorem instruction_bound_selected (axes : List Axis) (n : ℕ)
    (h:radices axes=UniformSelectedDFSMachine.selectedRadices n) :
    treeCost (radices axes)+10≤153*UniformInitialPreparation.len n+10 := by
  have b:=complete_instruction_bound axes
  have nodes:=UniformSelectedDFSMachine.selectedRadices_nodes n
  rw [h] at b
  have bound:=Nat.mul_le_mul_left 51 nodes
  calc
    treeCost (radices axes)+10≤51*UniformTraversal.nodeCount (UniformSelectedDFSMachine.selectedRadices n)+10:=by simpa only [h] using b
    _≤51*(3*UniformInitialPreparation.len n)+10:=Nat.add_le_add_right bound 10
    _=153*UniformInitialPreparation.len n+10:=by ring

end
end ExactFourierCircuits.UniformTensorMonomialMachine
