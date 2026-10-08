import UniformRadixTwoMachine
import UniformMachineRuns

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRadixInstructionMachine
open UniformRadixTwoDAG

/-- Arithmetic embedding of a recursively selected child FFT. -/
def address (N off bit stride k : ℕ) : Ref k → ℕ
  | .inl i => bit+stride*i.val
  | .inr j => N+off+(nodeFin k j).val

/-- Scale exponents are multiplied by the stride of the selected FFT. -/
def liftOp (stride : ℕ) {α β : Type} (f : α→β) : Op α→Op β
  | .add a b => .add (f a) (f b)
  | .sub a b => .sub (f a) (f b)
  | .scale c a => .scale (stride*c) (f a)

def childOutput (N off bit stride k i : ℕ) : ℕ :=
  if k=0 then bit+stride*i else N+off+(count k-width k)+i

/-- A total arithmetic decoder. The zero-height default is unreachable for a
valid ordinal because count 0=0. No typed node or complex scalar is constructed. -/
def decode (N off bit stride : ℕ) : ℕ→ℕ→Op ℕ
  | 0,_ => .add 0 0
  | k+1,j =>
    let c:=count k
    let w:=width k
    if j<c then decode N off bit (2*stride) k j
    else if j<c+c then decode N (off+c) (bit+stride) (2*stride) k (j-c)
    else if j<c+c+w then
      .scale (stride*(j-(c+c))) (childOutput N (off+c) (bit+stride) (2*stride) k (j-(c+c)))
    else if j<c+c+(w+w) then
      .add (childOutput N off bit (2*stride) k (j-(c+c+w)))
        (N+off+(c+c)+(j-(c+c+w)))
    else .sub (childOutput N off bit (2*stride) k (j-(c+c+(w+w))))
        (N+off+(c+c)+(j-(c+c+(w+w))))

@[simp] theorem address_even (N off bit stride k : ℕ) (r:Ref k) :
    address N off bit stride (k+1) (evenRef r)=address N off bit (2*stride) k r := by
  cases r with
  | inl i => simp [address,evenRef,OAI.ExactFourier.RadixTwo.evenIndex];ring
  | inr j => rfl

@[simp] theorem address_odd (N off bit stride k : ℕ) (r:Ref k) :
    address N off bit stride (k+1) (oddRef r)=
      address N (off+count k) (bit+stride) (2*stride) k r := by
  cases r with
  | inl i => simp [address,oddRef,OAI.ExactFourier.RadixTwo.oddIndex];ring
  | inr j => change N+off+(count k+(nodeFin k j).val)=N+(off+count k)+(nodeFin k j).val;omega

theorem address_output (N off bit stride k : ℕ) (i:Fin (width k)) :
    address N off bit stride k (output k i)=childOutput N off bit stride k i.val := by
  cases k with
  | zero => simp [output,address,childOutput]
  | succ k =>
    have hc:width (k+1) ≤ count (k+1):=by simp only [width,count];omega
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [output,Fin.addCases_left,childOutput,Nat.add_one_ne_zero,ite_false,Fin.val_castAdd]
      change N+off+((count k+count k)+(width k+j.val))=
        N+off+(count (k+1)-width (k+1))+j.val
      simp only [count,width];omega
    · simp only [output,Fin.addCases_right,childOutput,Nat.add_one_ne_zero,ite_false,Fin.val_natAdd]
      change N+off+((count k+count k)+((width k+width k)+j.val))=
        N+off+(count (k+1)-width (k+1))+(width k+j.val)
      simp only [count,width];omega

@[simp] theorem liftOp_double_even (N off bit stride k : ℕ) (o:Op (Ref k)) :
    liftOp stride (address N off bit stride (k+1)) (o.double.map evenRef)=
      liftOp (2*stride) (address N off bit (2*stride) k) o := by
  cases o <;> simp [Op.double,Op.map,liftOp];ring

@[simp] theorem liftOp_double_odd (N off bit stride k : ℕ) (o:Op (Ref k)) :
    liftOp stride (address N off bit stride (k+1)) (o.double.map oddRef)=
      liftOp (2*stride) (address N (off+count k) (bit+stride) (2*stride) k) o := by
  cases o <;> simp [Op.double,Op.map,liftOp];ring

/-- Symbolic correctness for every printed gate, not a sampled comparison. -/
theorem decode_node {k : ℕ} (q:Node k) (N off bit stride : ℕ) :
    decode N off bit stride k (nodeFin k q).val=
      liftOp stride (address N off bit stride k) (gate q) := by
  induction q generalizing N off bit stride with
  | @even k q ih =>
    have hq: (nodeFin _ q).val<count _ := (nodeFin _ q).isLt
    change decode N off bit stride (k+1) (nodeFin k q).val=_
    simp only [decode,hq,ite_true,gate]
    exact (ih N off bit (2*stride)).trans (liftOp_double_even N off bit stride k (gate q)).symm
  | @odd k q ih =>
    have hq: (nodeFin _ q).val<count _ := (nodeFin _ q).isLt
    change decode N off bit stride (k+1) (count k+(nodeFin k q).val)=_
    simp only [decode]
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel_left,gate]
    exact (ih N (off+count k) (bit+stride) (2*stride)).trans (liftOp_double_odd N off bit stride k (gate q)).symm
  | @scale k i =>
    have hi:=i.isLt
    change decode N off bit stride (k+1) ((count k+count k)+i.val)=_
    simp only [decode]
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel_left,gate,liftOp]
    rw [address_odd,address_output]
  | @add k i =>
    have hi:=i.isLt
    change decode N off bit stride (k+1) ((count k+count k)+(width k+i.val))=_
    simp only [decode]
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
    have he:(count k+count k+(width k+i.val))-(count k+count k+width k)=i.val:=by omega
    rw [he]
    change Op.add _ _=Op.add (address N off bit stride (k+1) (evenRef (output k i)))
      (N+off+((count k+count k)+i.val))
    rw [address_even,address_output]
    congr 1;omega
  | @sub k i =>
    have hi:=i.isLt
    change decode N off bit stride (k+1) ((count k+count k)+((width k+width k)+i.val))=_
    simp only [decode]
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
    have he:(count k+count k+((width k+width k)+i.val))-(count k+count k+(width k+width k))=i.val:=by omega
    rw [he]
    change Op.sub _ _=Op.sub (address N off bit stride (k+1) (evenRef (output k i)))
      (N+off+((count k+count k)+i.val))
    rw [address_even,address_output]
    congr 1;omega

/-- The default decoder is exactly the frozen printed instruction. -/
theorem decode_instruction (k : ℕ) (j:Fin (count k)) :
    decode (width k) 0 0 1 k j.val=instruction k j := by
  have h:=decode_node ((nodeFin k).symm j) (width k) 0 0 1
  simp only [Equiv.apply_symm_apply] at h
  rw [h,instruction]
  cases gate ((nodeFin k).symm j) <;> simp [liftOp,Op.map,address,refNat] <;> try rfl
  all_goals exact ⟨rfl,rfl⟩


open UniformMachine

/-- Fixed natural-only straight-line pieces of the decoder. -/
inductive AOp where
  | lit (dst value : ℕ)
  | bin (op : NatOp) (dst left right : ℕ)
  deriving DecidableEq

def AOp.code : AOp→Instruction
  | .lit d v => .natLiteral d v
  | .bin op d l r => .natBinary op d l r

def AOp.value : AOp→State→ℕ
  | .lit _ v,_ => v
  | .bin op _ l r,s => (evalNat op (s.natReg l) (s.natReg r)).getD 0

def AOp.apply (o:AOp) (s:State) : State :=
  match o with
  | .lit d _ => writeNat s d (o.value s)
  | .bin _ d _ _ => writeNat s d (o.value s)

def AOp.valid : AOp→State→Prop
  | .lit _ _,_ => True
  | .bin op _ l r,s => evalNat op (s.natReg l) (s.natReg r)=some
      ((evalNat op (s.natReg l) (s.natReg r)).getD 0)

def block : List AOp→State→State
  | [],s => s
  | o::os,s => block os (o.apply s)

def validBlock : List AOp→State→Prop
  | [],_ => True
  | o::os,s => o.valid s ∧ validBlock os (o.apply s)

def peakBlock : List AOp→State→ℕ
  | [],_ => 0
  | o::os,s => max (o.value s) (peakBlock os (o.apply s))

theorem AOp.pc (o:AOp) (s:State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl

theorem block_pc (b:List AOp) (s:State) : (block b s).pc=s.pc+b.length := by
  induction b generalizing s with
  | nil => simp [block]
  | cons o os ih => rw [block,ih,AOp.pc];simp;omega

theorem block_append (a b:List AOp) (s:State) : block (a++b) s=block b (block a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => simpa [block] using ih (o.apply s)

theorem AOp.step (o:AOp) (p:Program) (n:ℕ) (x:Fin n→ℂ) (s:State)
    (hc:p[s.pc]?=some o.code) (hv:o.valid s) : step p n x s=.running (o.apply s) := by
  cases o with
  | lit d v => simp [UniformMachine.step,hc,AOp.code,AOp.apply,AOp.value]
  | bin op d l r =>
    simp only [AOp.valid] at hv
    simp only [UniformMachine.step,hc,AOp.code]
    rw [hv]
    rfl

/-- Literal placement, not a precomputed instruction table. -/
def BlockAt (b:List AOp) (p:Program) (base:ℕ) : Prop :=
  ∀j:Fin b.length,p[base+j.val]?=some (b[j].code)

theorem block_runs (b:List AOp) (p:Program) (base n B:ℕ) (x:Fin n→ℂ) (s:State)
    (hc:BlockAt b p base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+b.length ≤ B) (hv:validBlock b s) (hpeak:peakBlock b s ≤ B) :
    BoundedRuns p n x B s b.length (block b s) := by
  induction b generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have hu:WordBound B (o.apply s):=by
      cases o <;> apply writeNat_bound B s _ _ hs (by simp only [List.length_cons] at hb;omega) (le_trans (le_max_left _ _) hpeak)
    have hfirst:p[s.pc]?=some o.code:=by simpa [hp] using hc ⟨0,by simp⟩
    have htail:BlockAt os p (base+1):=by
      intro j
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc ⟨j.val+1,by have:=j.isLt;simp only [List.length_cons];omega⟩
    have hr:=ih (base+1) (o.apply s) htail (by rw [AOp.pc,hp]) hu (by simp at hb;omega)
      hv.2 ((le_max_right _ _).trans hpeak)
    simpa [block] using BoundedRuns.next hs (AOp.step o p n x s hfirst hv.1) hr

/-- Output registers90..93 contain opcode (add0/sub1/scale2), exponent,
left/source and right. Register70=height,71=ordinal are entry arguments.
Only registers72..96 are written; all heaps and scalar state are untouched. -/
def setup : List AOp := [.lit 72 1,.lit 73 0,.lit 75 0,.lit 76 0,.lit 77 1,
  .lit 78 0,.lit 79 1,.lit 80 2,.lit 81 3]
def grow : List AOp := [.bin .mul 72 72 80,.bin .add 73 73 79]
def start : List AOp := [.bin .add 74 72 78,.bin .add 94 71 78,.bin .add 73 70 78]
def inspect : List AOp := [.bin .sub 82 73 79,.bin .div 83 74 80,
  .bin .mul 84 81 82,.bin .mul 84 84 83,.bin .div 84 84 80,.bin .add 85 84 84]
def evenStep : List AOp := [.bin .add 73 82 78,.bin .add 74 83 78,.bin .mul 77 77 80]
def oddStep : List AOp := [.bin .sub 94 94 84,.bin .add 75 75 84,.bin .add 76 76 77,
  .bin .add 73 82 78,.bin .add 74 83 78,.bin .mul 77 77 80]
def scaleStep : List AOp := [.bin .sub 86 94 85,.lit 90 2,.bin .mul 91 77 86]
def addStep : List AOp := [.bin .sub 86 94 95,.lit 90 0]
def subStep : List AOp := [.bin .sub 86 94 96,.lit 90 1]
def inputOutput : List AOp := [.bin .mul 87 80 77,.bin .mul 87 87 86,.bin .add 87 76 87]
def gateOutput : List AOp := [.bin .sub 87 84 83,.bin .add 87 87 86,
  .bin .add 87 87 75,.bin .add 87 87 72]
def scaleOutput : List AOp := [.bin .add 89 72 75,.bin .add 89 89 85,.bin .add 89 89 86]
def binaryResult : List AOp := [.bin .add 92 87 78,.bin .add 93 89 78]
def scaleResult : List AOp := [.bin .add 92 88 78,.lit 93 0]

def program : Program := setup.map AOp.code ++ [
  .branchLT 73 70 10 13] ++ grow.map AOp.code ++ [.jump 9] ++ start.map AOp.code ++
  inspect.map AOp.code ++ [.branchLT 94 84 23 27] ++ evenStep.map AOp.code ++ [.jump 16,
  .branchLT 94 85 28 35] ++ oddStep.map AOp.code ++ [.jump 16,.natBinary .add 95 85 83,
  .branchLT 94 95 37 41] ++ scaleStep.map AOp.code ++ [.jump 49,.natBinary .add 96 95 83,
  .branchLT 94 96 43 46] ++ addStep.map AOp.code ++ [.jump 48] ++ subStep.map AOp.code ++
  [.natLiteral 91 0,.branchLT 82 79 50 54] ++ inputOutput.map AOp.code ++ [.jump 58] ++
  gateOutput.map AOp.code ++ [.branchLT 82 79 59 61,.natBinary .add 88 87 77,.jump 62,
  .natBinary .add 88 87 84] ++ scaleOutput.map AOp.code ++ [.branchLT 90 80 66 69] ++
  binaryResult.map AOp.code ++ [.jump 71] ++ scaleResult.map AOp.code ++ [.halt]

theorem program_length : program.length=72 := rfl

def rawInstruction (s:State) : Op ℕ :=
  if s.natReg 90=0 then .add (s.natReg 92) (s.natReg 93)
  else if s.natReg 90=1 then .sub (s.natReg 92) (s.natReg 93)
  else .scale (s.natReg 91) (s.natReg 92)

/-- Protected global metadata including Nat100..106 lies outside this range. -/
def Frame (s u:State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀i,(i < 72 ∨ 97 ≤ i)→u.natReg i=s.natReg i



theorem branch_runs (p:Program) (n B l r yes no:ℕ) (x:Fin n→ℂ) (s:State)
    (hs:WordBound B s) (hy:yes ≤ B) (hn:no ≤ B)
    (hc:p[s.pc]?=some (.branchLT l r yes no)) :
    BoundedRuns p n x B s 1 {s with pc:=if s.natReg l<s.natReg r then yes else no} :=
  .next hs (by simp [UniformMachine.step,hc]) (.refl (changePC_bound B s _ hs (by split_ifs <;> assumption)))

theorem jump_runs (p:Program) (n B target:ℕ) (x:Fin n→ℂ) (s:State)
    (hs:WordBound B s) (ht:target ≤ B) (hc:p[s.pc]?=some (.jump target)) :
    BoundedRuns p n x B s 1 {s with pc:=target} :=
  .next hs (by simp [UniformMachine.step,hc]) (.refl (changePC_bound B s target hs ht))

structure Constants (s:State) : Prop where
  zero:s.natReg 78=0
  one:s.natReg 79=1
  two:s.natReg 80=2
  three:s.natReg 81=3

structure Config (N off bit stride k j:ℕ) (s:State) : Prop extends Constants s where
  Nreg:s.natReg 72=N
  kreg:s.natReg 73=k
  wreg:s.natReg 74=width k
  offreg:s.natReg 75=off
  bitreg:s.natReg 76=bit
  sreg:s.natReg 77=stride
  jreg:s.natReg 94=j

structure Scanned (N off bit stride k j:ℕ) (s:State) : Prop extends Config N off bit stride (k+1) j s where
  childK:s.natReg 82=k
  childW:s.natReg 83=width k
  childC:s.natReg 84=count k
  twiceC:s.natReg 85=count k+count k

structure Shape (N G K off bit stride k j:ℕ) : Prop where
  height:k ≤ K
  widthEq:stride*width k=N
  bitLt:bit<stride
  ord:off+count k ≤ G
  ordinal:j<count k

/-- A coarse polynomial envelope for all intermediate natural operations.
The caller's unrelated metadata must fit the same bound as well. -/
def cap (N G K:ℕ) : ℕ := 100*(N+G+K+1)^2+200

theorem cap_code (N G K:ℕ) : 100 ≤ cap N G K := by unfold cap;omega

theorem cap_linear (N G K:ℕ) : 100*(N+G+K+1) ≤ cap N G K := by
  have ht:1 ≤ N+G+K+1:=by omega
  have hl:=Nat.mul_le_mul_left (N+G+K+1) ht
  simp only [Nat.mul_one,←pow_two] at hl
  unfold cap;omega

theorem cap_product (N G K a b:ℕ) (ha:a ≤ N+G+K+1) (hb:b ≤ N+G+K+1) :
    a*b ≤ cap N G K := by
  have hm:=Nat.mul_le_mul ha hb
  simp only [←pow_two] at hm
  unfold cap;omega

theorem width_mono {k K:ℕ} (h:k ≤ K) : width k ≤ width K := by
  rw [width_eq,width_eq]
  exact Nat.pow_le_pow_right (by decide) h

theorem Shape.bounds {N G K off bit stride k j:ℕ} (h:Shape N G K off bit stride k j) :
    off ≤ G ∧ bit ≤ N ∧ stride ≤ N ∧ j ≤ G ∧ width k ≤ N := by
  have hw:=width_pos k
  have hs:0<stride:=by have:=h.bitLt;omega
  have hn:stride ≤ N:=by nlinarith [h.widthEq]
  have hnw:width k ≤ N:=by nlinarith [h.widthEq]
  exact ⟨by have:=h.ord;omega,by have:=h.bitLt;omega,hn,by have:=h.ordinal;have:=h.ord;omega,hnw⟩

theorem Shape.even {N G K off bit stride k j:ℕ}
    (h:Shape N G K off bit stride (k+1) j) (hj:j<count k) :
    Shape N G K off bit (2*stride) k j := by
  constructor
  · have:=h.height;omega
  · have hw:=h.widthEq;simp only [width] at hw;nlinarith
  · have:=h.bitLt;omega
  · have hc:=h.ord;simp only [count] at hc;omega
  · exact hj

theorem Shape.odd {N G K off bit stride k j:ℕ}
    (h:Shape N G K off bit stride (k+1) j) (hj:count k ≤ j) (hj':j<count k+count k) :
    Shape N G K (off+count k) (bit+stride) (2*stride) k (j-count k) := by
  constructor
  · have:=h.height;omega
  · have hw:=h.widthEq;simp only [width] at hw;nlinarith
  · have:=h.bitLt;omega
  · have hc:=h.ord;simp only [count] at hc;omega
  · omega

theorem Constants.withPC {s:State} {pc:ℕ} (h:Constants s) : Constants {s with pc:=pc} := by
  cases h;constructor <;> assumption

theorem Config.withPC {N off bit stride k j pc:ℕ} {s:State}
    (h:Config N off bit stride k j s) : Config N off bit stride k j {s with pc:=pc} := by
  cases h with | mk hc hN hk hw ho hb hs hj => exact ⟨hc.withPC,hN,hk,hw,ho,hb,hs,hj⟩

theorem Scanned.withPC {N off bit stride k j pc:ℕ} {s:State}
    (h:Scanned N off bit stride k j s) : Scanned N off bit stride k j {s with pc:=pc} := by
  cases h with | mk hc hk hw hn ht => exact ⟨hc.withPC,hk,hw,hn,ht⟩

theorem inspect_at : BlockAt inspect program 16 := by intro j;fin_cases j <;> rfl
theorem setup_at : BlockAt setup program 0 := by intro j;fin_cases j <;> rfl
theorem grow_at : BlockAt grow program 10 := by intro j;fin_cases j <;> rfl
theorem start_at : BlockAt start program 13 := by intro j;fin_cases j <;> rfl
theorem even_at : BlockAt evenStep program 23 := by intro j;fin_cases j <;> rfl
theorem odd_at : BlockAt oddStep program 28 := by intro j;fin_cases j <;> rfl

theorem count_div (k:ℕ) : 3*k*width k/2=count k := by have:=count_exact k;omega

theorem inspect_spec (N off bit stride k j:ℕ) (s:State) (h:Config N off bit stride (k+1) j s) :
    Scanned N off bit stride k j (block inspect s) := by
  have hd:(width k+width k)/2=width k:=by omega
  have hc:=count_div k
  constructor
  · constructor
    · constructor <;> simp [block,inspect,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three]
    all_goals simp [block,inspect,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.kreg,h.wreg,h.offreg,h.bitreg,h.sreg,h.jreg]
  all_goals simp [block,inspect,AOp.apply,AOp.value,evalNat,writeNat,next,h.kreg,h.one,h.two,h.three,h.wreg,width,hd,hc]

theorem inspect_valid (N off bit stride k j:ℕ) (s:State) (h:Config N off bit stride (k+1) j s) :
    validBlock inspect s := by
  simp [validBlock,inspect,AOp.valid,AOp.apply,AOp.value,evalNat,writeNat,next,h.two]

theorem inspect_peak (N G K off bit stride k j:ℕ) (s:State)
    (h:Config N off bit stride (k+1) j s) (hh:Shape N G K off bit stride (k+1) j) :
    peakBlock inspect s ≤ cap N G K := by
  have b:=hh.bounds
  have hw:width k ≤ N:=by have:=b.2.2.2.2;simp only [width] at this;omega
  have hk:k ≤ K:=by have:=hh.height;omega
  have hn:1 ≤ N:=by have:=width_pos (k+1);have:=b.2.2.2.2;omega
  have hd:(width k+width k)/2=width k:=by omega
  simp [peakBlock,inspect,AOp.value,AOp.apply,evalNat,writeNat,next,
    h.kreg,h.one,h.two,h.three,h.wreg,width,hd,count_div,cap]
  have hc:count k ≤ G:=by have:=hh.ord;simp only [count] at this;omega
  have hkw:=Nat.mul_le_mul hk hw
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (N+G+K+1)]

theorem even_spec (N off bit stride k j:ℕ) (s:State) (h:Scanned N off bit stride k j s) :
    Config N off bit (2*stride) k j (block evenStep s) := by
  constructor
  · constructor <;> simp [block,evenStep,AOp.value,AOp.apply,evalNat,writeNat,next,h.zero,h.one,h.two,h.three]
  all_goals simp [block,evenStep,AOp.value,AOp.apply,evalNat,writeNat,next,
    h.Nreg,h.childK,h.childW,h.offreg,h.bitreg,h.sreg,h.jreg,h.zero,h.two,Nat.mul_comm]

theorem odd_spec (N off bit stride k j:ℕ) (s:State) (h:Scanned N off bit stride k j s) :
    Config N (off+count k) (bit+stride) (2*stride) k (j-count k) (block oddStep s) := by
  constructor
  · constructor <;> simp [block,oddStep,AOp.value,AOp.apply,evalNat,writeNat,next,h.zero,h.one,h.two,h.three]
  all_goals simp [block,oddStep,AOp.value,AOp.apply,evalNat,writeNat,next,
    h.Nreg,h.childK,h.childW,h.childC,h.offreg,h.bitreg,h.sreg,h.jreg,h.zero,h.two,Nat.mul_comm]



structure Initializing (K J t:ℕ) (s:State) : Prop extends Constants s where
  height:s.natReg 70=K
  ordinal:s.natReg 71=J
  Nreg:s.natReg 72=width t
  index:s.natReg 73=t
  offreg:s.natReg 75=0
  bitreg:s.natReg 76=0
  sreg:s.natReg 77=1

theorem Initializing.withPC {K J t pc:ℕ} {s:State} (h:Initializing K J t s) :
    Initializing K J t {s with pc:=pc} := by
  cases h with | mk hc hK hJ hN ht ho hb hr => exact ⟨hc.withPC,hK,hJ,hN,ht,ho,hb,hr⟩

theorem setup_spec (K J:ℕ) (s:State) (hK:s.natReg 70=K) (hJ:s.natReg 71=J) :
    Initializing K J 0 (block setup s) := by
  constructor
  · constructor <;> rfl
  all_goals simp [block,setup,AOp.apply,AOp.value,writeNat,next,hK,hJ,width]

theorem setup_valid (s:State) : validBlock setup s := by simp [validBlock,setup,AOp.valid]

theorem setup_peak (s:State) : peakBlock setup s=3 := rfl

theorem grow_spec (K J t:ℕ) (s:State) (h:Initializing K J t s) :
    Initializing K J (t+1) (block grow s) := by
  constructor
  · constructor <;> simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three]
  all_goals simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.ordinal,
    h.Nreg,h.index,h.offreg,h.bitreg,h.sreg,h.one,h.two,width, Nat.mul_two]

theorem grow_valid (s:State) : validBlock grow s := by simp [validBlock,grow,AOp.valid,evalNat]

theorem grow_peak (K J t:ℕ) (s:State) (h:Initializing K J t s) (ht:t<K) :
    peakBlock grow s ≤ cap (width K) (count K) K := by
  have hw:=width_mono (show t ≤ K by omega)
  have hl:=cap_linear (width K) (count K) K
  unfold cap at hl
  simp [peakBlock,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.index,h.one,h.two,cap]
  constructor <;> omega

theorem start_valid (s:State) : validBlock start s := by simp [validBlock,start,AOp.valid,evalNat]

theorem start_spec (K J:ℕ) (s:State) (h:Initializing K J K s) :
    Config (width K) 0 0 1 K J (block start s) := by
  constructor
  · constructor <;> simp [block,start,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three]
  all_goals simp [block,start,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.ordinal,
    h.Nreg,h.offreg,h.bitreg,h.sreg,h.zero]

theorem start_peak (K J:ℕ) (s:State) (h:Initializing K J K s) (hj:J<count K) :
    peakBlock start s ≤ cap (width K) (count K) K := by
  have hl:=cap_linear (width K) (count K) K
  unfold cap at hl
  simp [peakBlock,start,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.ordinal,h.height,h.zero,cap]
  refine ⟨?_,?_,?_⟩ <;> omega

/-- The actual width-doubling loop charges its branch, multiply, increment and
jump. No width/power table is supplied by the caller. -/
theorem initialize_loop (n K J t fuel B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Initializing K J t s) (ht:t+fuel=K) (hs:WordBound B s)
    (hB:cap (width K) (count K) K ≤ B) (hp:s.pc=9) : ∃u,
    BoundedRuns program n x B s (4*fuel+1) u ∧ Initializing K J K u ∧ u.pc=13 := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  induction fuel generalizing t s with
  | zero =>
    have he:t=K:=by omega
    subst t
    have hc:program[s.pc]?=some (.branchLT 73 70 10 13):=by rw [hp];rfl
    have hb:=branch_runs program n B 73 70 10 13 x s hs (by omega) (by omega) hc
    have he:¬s.natReg 73<s.natReg 70:=by rw [h.index,h.height];omega
    simp only [he,ite_false] at hb
    exact ⟨_,by simpa using hb,h.withPC,rfl⟩
  | succ fuel ih =>
    have htK:t<K:=by omega
    have hc:program[s.pc]?=some (.branchLT 73 70 10 13):=by rw [hp];rfl
    have hb:=branch_runs program n B 73 70 10 13 x s hs (by omega) (by omega) hc
    have he:s.natReg 73<s.natReg 70:=by rw [h.index,h.height];exact htK
    simp only [he,ite_true] at hb
    let v:State:={s with pc:=10}
    have hg:=block_runs grow program 10 n B x v grow_at rfl hb.final_bound (by change 10+2 ≤ B;omega)
      (grow_valid v) ((grow_peak K J t v h.withPC htK).trans hB)
    have hv:Initializing K J (t+1) (block grow v):=grow_spec K J t v h.withPC
    have hpc:(block grow v).pc=12:=by rw [block_pc];rfl
    have hj:=jump_runs program n B 9 x (block grow v) hg.final_bound (by omega)
      (by rw [hpc];rfl)
    obtain ⟨u,hu,hi,hpu⟩:=ih (t+1) {block grow v with pc:=9} hv.withPC (by omega)
      hj.final_bound rfl
    refine ⟨u,?_,hi,hpu⟩
    convert hb.trans (hg.trans (hj.trans hu)) using 1
    simp only [show grow.length=2 from rfl];omega



def AOp.dst : AOp→ℕ
  | .lit d _ => d
  | .bin _ d _ _ => d

theorem block_keeps (b:List AOp) (s:State) (r:ℕ) (h:∀o∈b,o.dst≠r) :
    (block b s).natReg r=s.natReg r := by
  induction b generalizing s with
  | nil => rfl
  | cons o os ih =>
    rw [block,ih _ (fun q hq=>h q (by simp [hq]))]
    have hr:=h o (by simp)
    cases o <;> simp_all [AOp.apply,writeNat,next,AOp.dst,Ne.symm]

structure Terminal (N off bit stride k j i op exponent:ℕ) (s:State) : Prop extends Scanned N off bit stride k j s where
  index:s.natReg 86=i
  opcode:s.natReg 90=op
  exponent:s.natReg 91=exponent

def control : List ℕ := [72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,90,91,94]

theorem Terminal.withPC {N off bit stride k j i op exponent pc:ℕ} {s:State}
    (h:Terminal N off bit stride k j i op exponent s) :
    Terminal N off bit stride k j i op exponent {s with pc:=pc} := by
  cases h with | mk hc hi ho he => exact ⟨hc.withPC,hi,ho,he⟩

theorem Terminal.congr {N off bit stride k j i op exponent:ℕ} {s u:State}
    (h:Terminal N off bit stride k j i op exponent s)
    (hkeep:∀r∈control,u.natReg r=s.natReg r) : Terminal N off bit stride k j i op exponent u := by
  constructor
  · constructor
    · constructor
      · constructor <;> (rw [hkeep _ (by simp [control])];first | exact h.zero | exact h.one | exact h.two | exact h.three)
      all_goals rw [hkeep _ (by simp [control])] ; first | exact h.Nreg | exact h.kreg | exact h.wreg | exact h.offreg | exact h.bitreg | exact h.sreg | exact h.jreg
    all_goals rw [hkeep _ (by simp [control])] ; first | exact h.childK | exact h.childW | exact h.childC | exact h.twiceC
  all_goals rw [hkeep _ (by simp [control])] ; first | exact h.index | exact h.opcode | exact h.exponent

theorem Terminal.block {N off bit stride k j i op exponent:ℕ} {s:State}
    (h:Terminal N off bit stride k j i op exponent s) (b:List AOp)
    (hb:∀o∈b,o.dst∉control) : Terminal N off bit stride k j i op exponent (block b s) :=
  h.congr (fun r hr=>block_keeps b s r (fun o ho he=>hb o ho (he ▸ hr)))

theorem inputOutput_at : BlockAt inputOutput program 50 := by intro j;fin_cases j <;> rfl
theorem gateOutput_at : BlockAt gateOutput program 54 := by intro j;fin_cases j <;> rfl
theorem scaleOutput_at : BlockAt scaleOutput program 62 := by intro j;fin_cases j <;> rfl
theorem binaryResult_at : BlockAt binaryResult program 66 := by intro j;fin_cases j <;> rfl
theorem scaleResult_at : BlockAt scaleResult program 69 := by intro j;fin_cases j <;> rfl

theorem terminal_blocks_valid (s:State) : validBlock inputOutput s ∧ validBlock gateOutput s ∧
    validBlock scaleOutput s ∧ validBlock binaryResult s ∧ validBlock scaleResult s := by
  simp [validBlock,inputOutput,gateOutput,scaleOutput,binaryResult,scaleResult,AOp.valid,evalNat]

theorem terminal_blocks_keep :
    (∀o∈inputOutput,o.dst∉control) ∧ (∀o∈gateOutput,o.dst∉control) ∧
    (∀o∈scaleOutput,o.dst∉control) ∧ (∀o∈binaryResult,o.dst∉control) ∧
    (∀o∈scaleResult,o.dst∉control) := by
  simp [inputOutput,gateOutput,scaleOutput,binaryResult,scaleResult,AOp.dst,control]

/-- Either input coordinates or previously printed child outputs, as appropriate. -/
theorem even_output (N G K off bit stride k j i op exponent n B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Terminal N off bit stride k j i op exponent s) (hh:Shape N G K off bit stride (k+1) j)
    (hi:i<width k) (hs:WordBound B s) (hB:cap N G K ≤ B) (hp:s.pc=49) : ∃u,
    BoundedRuns program n x B s 5 u ∧ Terminal N off bit stride k j i op exponent u ∧
    u.pc=58 ∧ u.natReg 87=childOutput N off bit (2*stride) k i := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  have hb:=branch_runs program n B 82 79 50 54 x s hs (by omega) (by omega) (by rw [hp];rfl)
  have bounds:=hh.bounds
  have hw:width k ≤ N:=by have:=bounds.2.2.2.2;simp only [width] at this;omega
  have hic:i ≤ N:=by omega
  have hc:count k ≤ G:=by have:=hh.ord;simp only [count] at this;omega
  have hl:=cap_linear N G K
  by_cases hk:k=0
  · have hcond:s.natReg 82<s.natReg 79:=by rw [h.childK,h.one,hk];omega
    simp only [hcond,ite_true] at hb
    let v:State:={s with pc:=50}
    have hi0:i=0:=by have hi':=hi;simp only [hk,width] at hi';omega
    have hpeak:peakBlock inputOutput v ≤ cap N G K:=by
      simp [peakBlock,inputOutput,AOp.apply,AOp.value,evalNat,writeNat,next,h.two,h.sreg,h.index,h.bitreg,v,hi0]
      all_goals omega
    have hr:=block_runs inputOutput program 50 n B x v inputOutput_at rfl hb.final_bound
      (by change 50+3 ≤ B;omega) (terminal_blocks_valid v).1 (hpeak.trans hB)
    have hpv:(block inputOutput v).pc=53:=by rw [block_pc];rfl
    have hj:=jump_runs program n B 58 x (block inputOutput v) hr.final_bound (by omega) (by rw [hpv];rfl)
    refine ⟨{block inputOutput v with pc:=58},?_,
      (h.withPC (pc:=50) |>.block inputOutput terminal_blocks_keep.1).withPC,rfl,?_⟩
    · convert hb.trans (hr.trans hj) using 1;rfl
    · simp [block,inputOutput,AOp.apply,AOp.value,evalNat,writeNat,next,h.two,h.sreg,h.index,h.bitreg,v,childOutput,hk,Nat.mul_comm,Nat.mul_left_comm]
  · have hcond:¬s.natReg 82<s.natReg 79:=by rw [h.childK,h.one];omega
    simp only [hcond,ite_false] at hb
    let v:State:={s with pc:=54}
    have hpeak:peakBlock gateOutput v ≤ cap N G K:=by
      simp [peakBlock,gateOutput,AOp.apply,AOp.value,evalNat,writeNat,next,h.childC,h.childW,
        h.index,h.offreg,h.Nreg,v]
      all_goals omega
    have hr:=block_runs gateOutput program 54 n B x v gateOutput_at rfl hb.final_bound
      (by change 54+4 ≤ B;omega) (terminal_blocks_valid v).2.1 (hpeak.trans hB)
    refine ⟨block gateOutput v,?_,h.withPC (pc:=54) |>.block gateOutput terminal_blocks_keep.2.1,?_,?_⟩
    · convert hb.trans hr using 1;rfl
    · rw [block_pc];rfl
    · simp [block,gateOutput,AOp.apply,AOp.value,evalNat,writeNat,next,h.childC,h.childW,h.index,
        h.offreg,h.Nreg,v,childOutput,hk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]



theorem Terminal.write {N off bit stride k j i op exponent:ℕ} {s:State}
    (h:Terminal N off bit stride k j i op exponent s) (dst value:ℕ) (hd:dst∉control) :
    Terminal N off bit stride k j i op exponent (writeNat s dst value) :=
  h.congr (fun r hr=>by simp [writeNat,next,Function.update_of_ne (show r≠dst from fun he=>hd (he ▸ hr))])

theorem one_runs (o:AOp) (pc n B:ℕ) (x:Fin n→ℂ) (s:State)
    (hp:s.pc=pc) (hc:program[pc]?=some o.code) (hs:WordBound B s)
    (hpc:pc+1 ≤ B) (hv:o.valid s) (hval:o.value s ≤ B) :
    BoundedRuns program n x B s 1 (o.apply s) := by
  have hbound:WordBound B (o.apply s):=by cases o <;> exact writeNat_bound B s _ _ hs (by omega) hval
  exact .next hs (AOp.step o program n x s (by rw [hp];exact hc) hv) (.refl hbound)

theorem child_output_bound {N G K off bit stride k j:ℕ}
    (h:Shape N G K off bit stride (k+1) j) (i:ℕ) (hi:i<width k) :
    childOutput N off bit (2*stride) k i ≤ N+G ∧
    childOutput N (off+count k) (bit+stride) (2*stride) k i ≤ N+G := by
  have b:=h.bounds
  have hc:off+2*count k ≤ G:=by have:=h.ord;simp only [count] at this;omega
  by_cases hk:k=0
  · subst k
    have hi0:i=0:=by simp only [width] at hi;omega
    subst i
    have hw:=h.widthEq
    simp only [width] at hw
    have hb:=h.bitLt
    simp [childOutput]
    constructor <;> omega
  · have hd:width k ≤ count k:=by
      cases k with
      | zero => contradiction
      | succ k => simp only [width,count];omega
    simp [childOutput,hk]
    constructor <;> omega

/-- Actual input/gate address conversion for the odd child. -/
theorem odd_output (N G K off bit stride k j i op exponent n B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Terminal N off bit stride k j i op exponent s) (hh:Shape N G K off bit stride (k+1) j)
    (hi:i<width k) (hs:WordBound B s) (hB:cap N G K ≤ B) (hp:s.pc=58)
    (h87:s.natReg 87=childOutput N off bit (2*stride) k i) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 3 ∧ Terminal N off bit stride k j i op exponent u ∧
    u.pc=62 ∧ u.natReg 87=s.natReg 87 ∧
    u.natReg 88=childOutput N (off+count k) (bit+stride) (2*stride) k i := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  have hb:=branch_runs program n B 82 79 59 61 x s hs (by omega) (by omega) (by rw [hp];rfl)
  have bounds:=hh.bounds
  have hout:=child_output_bound hh i hi
  have hl:=cap_linear N G K
  by_cases hk:k=0
  · have hcond:s.natReg 82<s.natReg 79:=by rw [h.childK,h.one,hk];omega
    simp only [hcond,ite_true] at hb
    let v:State:={s with pc:=59}
    have he:childOutput N off bit (2*stride) k i+stride=
        childOutput N (off+count k) (bit+stride) (2*stride) k i:=by simp [childOutput,hk];omega
    have hv:(AOp.bin .add 88 87 77).value v ≤ B:=by
      simp only [AOp.value,evalNat,Option.getD_some];change s.natReg 87+s.natReg 77 ≤ B
      rw [h87,h.sreg,he];omega
    have hr:=one_runs (.bin .add 88 87 77) 59 n B x v rfl rfl hb.final_bound (by omega)
      (by simp [AOp.valid,evalNat]) hv
    have hj:=jump_runs program n B 62 x ((AOp.bin .add 88 87 77).apply v) hr.final_bound
      (by omega) (by change program[60]?=_;rfl)
    refine ⟨{(AOp.bin .add 88 87 77).apply v with pc:=62},3,?_,by omega,
      (h.withPC (pc:=59) |>.write 88 ((AOp.bin .add 88 87 77).value v) (by simp [control])).withPC,rfl,?_,?_⟩
    · convert hb.trans (hr.trans hj) using 1
    · simp [AOp.apply,writeNat,next,v]
    · simp [AOp.apply,AOp.value,evalNat,writeNat,next,v,h87,h.sreg,he]
  · have hcond:¬s.natReg 82<s.natReg 79:=by rw [h.childK,h.one];omega
    simp only [hcond,ite_false] at hb
    let v:State:={s with pc:=61}
    have he:childOutput N off bit (2*stride) k i+count k=
        childOutput N (off+count k) (bit+stride) (2*stride) k i:=by simp [childOutput,hk];omega
    have hv:(AOp.bin .add 88 87 84).value v ≤ B:=by
      simp only [AOp.value,evalNat,Option.getD_some];change s.natReg 87+s.natReg 84 ≤ B
      rw [h87,h.childC,he];omega
    have hr:=one_runs (.bin .add 88 87 84) 61 n B x v rfl rfl hb.final_bound (by omega)
      (by simp [AOp.valid,evalNat]) hv
    refine ⟨(AOp.bin .add 88 87 84).apply v,2,?_,by omega,
      h.withPC (pc:=61) |>.write 88 ((AOp.bin .add 88 87 84).value v) (by simp [control]),rfl,?_,?_⟩
    · convert hb.trans hr using 1
    · simp [AOp.apply,writeNat,next,v]
    · simp [AOp.apply,AOp.value,evalNat,writeNat,next,v,h87,h.childC,he]



def terminalOp (N off bit stride k i op exponent:ℕ) : Op ℕ :=
  if op=0 then .add (childOutput N off bit (2*stride) k i) (N+off+(count k+count k)+i)
  else if op=1 then .sub (childOutput N off bit (2*stride) k i) (N+off+(count k+count k)+i)
  else .scale exponent (childOutput N (off+count k) (bit+stride) (2*stride) k i)

/-- The terminal conversion is the literal branch/address bytecode, followed by
its halt. The scalar-power exponent is left as a natural prepared-bank key. -/
theorem emit_terminal (N G K off bit stride k j i op exponent n B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Terminal N off bit stride k j i op exponent s) (hh:Shape N G K off bit stride (k+1) j)
    (hi:i<width k) (hs:WordBound B s) (hB:cap N G K ≤ B) (hp:s.pc=49) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 16 ∧
    rawInstruction u=terminalOp N off bit stride k i op exponent := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  obtain ⟨u,hu,hui,hpu,hu87⟩:=even_output N G K off bit stride k j i op exponent n B x s h hh hi hs hB hp
  obtain ⟨w,t,hw,ht,hwi,hpw,hw87,hw88⟩:=odd_output N G K off bit stride k j i op exponent n B x u hui hh hi
    hu.final_bound hB hpu hu87
  have hc:off+(count k+count k)+i ≤ G:=by have:=hh.ord;simp only [count] at this;omega
  have hl:=cap_linear N G K
  have hpeak:peakBlock scaleOutput w ≤ cap N G K:=by
    simp [peakBlock,scaleOutput,AOp.apply,AOp.value,evalNat,writeNat,next,hwi.Nreg,hwi.offreg,hwi.twiceC,hwi.index]
    all_goals omega
  have hscale:=block_runs scaleOutput program 62 n B x w scaleOutput_at hpw hw.final_bound
    (by change 62+3 ≤ B;omega) (terminal_blocks_valid w).2.2.1 (hpeak.trans hB)
  let v:=block scaleOutput w
  have hvi:Terminal N off bit stride k j i op exponent v:=hwi.block scaleOutput terminal_blocks_keep.2.2.1
  have hpv:v.pc=65:=by dsimp [v];rw [block_pc,hpw];rfl
  have hv87:v.natReg 87=childOutput N off bit (2*stride) k i:=by
    dsimp [v];rw [block_keeps scaleOutput w 87 (by simp [scaleOutput,AOp.dst]),hw87,hu87]
  have hv88:v.natReg 88=childOutput N (off+count k) (bit+stride) (2*stride) k i:=by
    dsimp [v];rw [block_keeps scaleOutput w 88 (by simp [scaleOutput,AOp.dst]),hw88]
  have hv89:v.natReg 89=N+off+(count k+count k)+i:=by
    simp [v,block,scaleOutput,AOp.apply,AOp.value,evalNat,writeNat,next,hwi.Nreg,hwi.offreg,hwi.twiceC,hwi.index]
  have hout:=child_output_bound hh i hi
  have hbranch:=branch_runs program n B 90 80 66 69 x v hscale.final_bound (by omega) (by omega) (by rw [hpv];rfl)
  by_cases hop:op<2
  · have cond:v.natReg 90<v.natReg 80:=by rw [hvi.opcode,hvi.two];exact hop
    simp only [cond,ite_true] at hbranch
    let z:State:={v with pc:=66}
    have hpeak:peakBlock binaryResult z ≤ cap N G K:=by
      simp [peakBlock,binaryResult,AOp.apply,AOp.value,evalNat,writeNat,next,hvi.zero,z,hv87,hv89]
      all_goals omega
    have hr:=block_runs binaryResult program 66 n B x z binaryResult_at rfl hbranch.final_bound
      (by change 66+2 ≤ B;omega) (terminal_blocks_valid z).2.2.2.1 (hpeak.trans hB)
    have hpc:(block binaryResult z).pc=68:=by rw [block_pc];rfl
    have hj:=jump_runs program n B 71 x (block binaryResult z) hr.final_bound (by omega) (by rw [hpc];rfl)
    let result:State:={block binaryResult z with pc:=71}
    have halt:BoundedExecution program n x B result 1 result:=.halt hj.final_bound (by change step program n x {block binaryResult z with pc:=71}=_;rfl)
    refine ⟨result,5+t+3+1+2+1+1,?_,by omega,?_⟩
    · convert hu.executes (hw.executes (hscale.executes (hbranch.executes (hr.executes (hj.executes halt))))) using 1
      norm_num [scaleOutput,binaryResult];omega
    · have casesOp:op=0 ∨ op=1:=by omega
      rcases casesOp with ho|ho <;>
        simp [rawInstruction,terminalOp,result,z,block,binaryResult,AOp.apply,AOp.value,
          evalNat,writeNat,next,hvi.opcode,hvi.zero,hv87,hv89,ho]
  · have cond:¬v.natReg 90<v.natReg 80:=by rw [hvi.opcode,hvi.two];exact hop
    simp only [cond,ite_false] at hbranch
    let z:State:={v with pc:=69}
    have hpeak:peakBlock scaleResult z ≤ cap N G K:=by
      simp [peakBlock,scaleResult,AOp.value,evalNat,hvi.zero,z,hv88]
      all_goals omega
    have hr:=block_runs scaleResult program 69 n B x z scaleResult_at rfl hbranch.final_bound
      (by change 69+2 ≤ B;omega) (terminal_blocks_valid z).2.2.2.2 (hpeak.trans hB)
    let result:=block scaleResult z
    have hpc:result.pc=71:=by dsimp [result];rw [block_pc];rfl
    have halt:BoundedExecution program n x B result 1 result:=.halt hr.final_bound (by rw [step,hpc];rfl)
    refine ⟨result,5+t+3+1+2+1,?_,by omega,?_⟩
    · convert hu.executes (hw.executes (hscale.executes (hbranch.executes (hr.executes halt)))) using 1
      norm_num [scaleOutput,scaleResult];omega
    · have ho0:op≠0:=by omega
      have ho1:op≠1:=by omega
      simp [rawInstruction,terminalOp,result,z,block,scaleResult,AOp.apply,AOp.value,
        evalNat,writeNat,next,hvi.opcode,hvi.exponent,hvi.zero,hv88,ho0,ho1]



def scanControl : List ℕ := [72,73,74,75,76,77,78,79,80,81,82,83,84,85,94]

theorem Scanned.congr {N off bit stride k j:ℕ} {s u:State}
    (h:Scanned N off bit stride k j s) (hkeep:∀r∈scanControl,u.natReg r=s.natReg r) :
    Scanned N off bit stride k j u := by
  constructor
  · constructor
    · constructor <;> (rw [hkeep _ (by simp [scanControl])];first | exact h.zero | exact h.one | exact h.two | exact h.three)
    all_goals rw [hkeep _ (by simp [scanControl])] ; first | exact h.Nreg | exact h.kreg | exact h.wreg | exact h.offreg | exact h.bitreg | exact h.sreg | exact h.jreg
  all_goals rw [hkeep _ (by simp [scanControl])] ; first | exact h.childK | exact h.childW | exact h.childC | exact h.twiceC

theorem Scanned.write {N off bit stride k j:ℕ} {s:State}
    (h:Scanned N off bit stride k j s) (dst value:ℕ) (hd:dst∉scanControl) :
    Scanned N off bit stride k j (writeNat s dst value) :=
  h.congr (fun r hr=>by simp [writeNat,next,Function.update_of_ne (show r≠dst from fun he=>hd (he ▸ hr))])

theorem Scanned.block {N off bit stride k j:ℕ} {s:State}
    (h:Scanned N off bit stride k j s) (b:List AOp) (hb:∀o∈b,o.dst∉scanControl) :
    Scanned N off bit stride k j (block b s) :=
  h.congr (fun r hr=>block_keeps b s r (fun o ho he=>hb o ho (he ▸ hr)))

theorem select_blocks_at : BlockAt scaleStep program 37 ∧ BlockAt addStep program 43 ∧
    BlockAt subStep program 46 := by
  constructor
  · intro j;fin_cases j <;> rfl
  constructor <;> intro j <;> fin_cases j <;> rfl

theorem select_blocks_keep : (∀o∈scaleStep,o.dst∉scanControl) ∧
    (∀o∈addStep,o.dst∉scanControl) ∧ (∀o∈subStep,o.dst∉scanControl) := by
  simp [scaleStep,addStep,subStep,AOp.dst,scanControl]

theorem select_blocks_valid (s:State) : validBlock scaleStep s ∧ validBlock addStep s ∧
    validBlock subStep s := by simp [validBlock,scaleStep,addStep,subStep,AOp.valid,evalNat]

theorem terminal_decode_scale (N off bit stride k j:ℕ) (hlo:count k+count k ≤ j)
    (hhi:j<count k+count k+width k) :
    terminalOp N off bit stride k (j-(count k+count k)) 2 (stride*(j-(count k+count k)))=
      decode N off bit stride (k+1) j := by
  simp only [decode]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left hhi]
  rfl

theorem terminal_decode_add (N off bit stride k j:ℕ) (hlo:count k+count k+width k ≤ j)
    (hhi:j<count k+count k+(width k+width k)) :
    terminalOp N off bit stride k (j-(count k+count k+width k)) 0 0=
      decode N off bit stride (k+1) j := by
  simp only [decode]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left hhi]
  rfl

theorem terminal_decode_sub (N off bit stride k j:ℕ) (hlo:count k+count k+(width k+width k) ≤ j) :
    terminalOp N off bit stride k (j-(count k+count k+(width k+width k))) 1 0=
      decode N off bit stride (k+1) j := by
  simp only [decode]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
  rfl

/-- The terminal ordinal is decoded by charged comparisons and subtraction. -/
theorem select_terminal (N G K off bit stride k j n B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Scanned N off bit stride k j s) (hh:Shape N G K off bit stride (k+1) j)
    (hj:count k+count k ≤ j) (hs:WordBound B s) (hB:cap N G K ≤ B) (hp:s.pc=35) :
    ∃u t i op exponent,
    BoundedRuns program n x B s t u ∧ t ≤ 8 ∧ Terminal N off bit stride k j i op exponent u ∧
    u.pc=49 ∧ i<width k ∧ terminalOp N off bit stride k i op exponent=decode N off bit stride (k+1) j := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  have b:=hh.bounds
  have hc:count k ≤ G:=by have:=hh.ord;simp only [count] at this;omega
  have hw:width k ≤ N:=by have:=b.2.2.2.2;simp only [width] at this;omega
  have hl:=cap_linear N G K
  have hr:=one_runs (.bin .add 95 85 83) 35 n B x s hp rfl hs (by omega)
    (by simp [AOp.valid,evalNat]) (by simp [AOp.value,evalNat,h.twiceC,h.childW];omega)
  let v:=(AOp.bin .add 95 85 83).apply s
  have hvi:Scanned N off bit stride k j v:=h.write 95 _ (by simp [scanControl])
  have hvp:v.pc=36:=by simp [v,AOp.apply,writeNat,next,hp]
  have hv95:v.natReg 95=count k+count k+width k:=by simp [v,AOp.apply,AOp.value,evalNat,writeNat,next,h.twiceC,h.childW]
  have hb:=branch_runs program n B 94 95 37 41 x v hr.final_bound (by omega) (by omega) (by rw [hvp];rfl)
  by_cases hj':j<count k+count k+width k
  · have cond:v.natReg 94<v.natReg 95:=by rw [hvi.jreg,hv95];exact hj'
    simp only [cond,ite_true] at hb
    let z:State:={v with pc:=37}
    let i:=j-(count k+count k)
    have hi:i<width k:=by dsimp [i];omega
    have hiz:i ≤ N:=by omega
    have he:stride*(j-(count k+count k)) ≤ cap N G K:=
      cap_product N G K stride (j-(count k+count k)) (by omega) (by dsimp [i] at hiz;omega)
    have hpeak:peakBlock scaleStep z ≤ cap N G K:=by
      simp [peakBlock,scaleStep,AOp.apply,AOp.value,evalNat,writeNat,next,
        z,hvi.jreg,hvi.twiceC,hvi.sreg]
      all_goals omega
    have hscale:=block_runs scaleStep program 37 n B x z select_blocks_at.1 rfl hb.final_bound
      (by change 37+3 ≤ B;omega) (select_blocks_valid z).1 (hpeak.trans hB)
    have hpc:(block scaleStep z).pc=40:=by rw [block_pc];rfl
    have hterminal:Terminal N off bit stride k j i 2 (stride*i) (block scaleStep z):=by
      constructor
      · exact hvi.withPC.block scaleStep select_blocks_keep.1
      all_goals simp [block,scaleStep,AOp.apply,AOp.value,evalNat,writeNat,next,z,
        hvi.jreg,hvi.twiceC,hvi.sreg,i]
    have hJump:=jump_runs program n B 49 x (block scaleStep z) hscale.final_bound (by omega) (by rw [hpc];rfl)
    refine ⟨{block scaleStep z with pc:=49},6,i,2,stride*i,?_,by omega,hterminal.withPC,rfl,hi,?_⟩
    · convert hr.trans (hb.trans (hscale.trans hJump)) using 1;rfl
    · exact terminal_decode_scale N off bit stride k j hj hj'
  · have cond:¬v.natReg 94<v.natReg 95:=by rw [hvi.jreg,hv95];exact hj'
    simp only [cond,ite_false] at hb
    let z:State:={v with pc:=41}
    have hNext:=one_runs (.bin .add 96 95 83) 41 n B x z rfl rfl hb.final_bound (by omega)
      (by simp [AOp.valid,evalNat]) (by simp [AOp.value,evalNat,z,hv95,hvi.childW];omega)
    let w:=(AOp.bin .add 96 95 83).apply z
    have hwi:Scanned N off bit stride k j w:=hvi.withPC.write 96 _ (by simp [scanControl])
    have hwp:w.pc=42:=rfl
    have hw95:w.natReg 95=count k+count k+width k:=by simp [w,AOp.apply,writeNat,next,z,hv95]
    have hw96:w.natReg 96=count k+count k+(width k+width k):=by
      simp [w,AOp.apply,AOp.value,evalNat,writeNat,next,z,hv95,hvi.childW,Nat.add_assoc]
    have hbranch:=branch_runs program n B 94 96 43 46 x w hNext.final_bound (by omega) (by omega) (by rw [hwp];rfl)
    by_cases hj'':j<count k+count k+(width k+width k)
    · have cond:w.natReg 94<w.natReg 96:=by rw [hwi.jreg,hw96];exact hj''
      simp only [cond,ite_true] at hbranch
      let a:State:={w with pc:=43}
      let i:=j-(count k+count k+width k)
      have hi:i<width k:=by dsimp [i];omega
      have hpeak:peakBlock addStep a ≤ cap N G K:=by
        simp [peakBlock,addStep,AOp.value,evalNat,a,hwi.jreg,hw95]
        omega
      have hAdd:=block_runs addStep program 43 n B x a select_blocks_at.2.1 rfl hbranch.final_bound
        (by change 43+2 ≤ B;omega) (select_blocks_valid a).2.1 (hpeak.trans hB)
      have ha:Scanned N off bit stride k j (block addStep a):=hwi.withPC.block addStep select_blocks_keep.2.1
      have ha86:(block addStep a).natReg 86=i:=by
        simp [block,addStep,AOp.apply,AOp.value,evalNat,writeNat,next,a,hwi.jreg,hw95,i]
      have ha90:(block addStep a).natReg 90=0:=by simp [block,addStep,AOp.apply,AOp.value,writeNat,next]
      have hpc:(block addStep a).pc=45:=by rw [block_pc];rfl
      have hJump:=jump_runs program n B 48 x (block addStep a) hAdd.final_bound (by omega) (by rw [hpc];rfl)
      let endState:State:={block addStep a with pc:=48}
      have hZero:=one_runs (.lit 91 0) 48 n B x endState rfl rfl hJump.final_bound (by omega)
        (by trivial) (by simp [AOp.value])
      have hterminal:Terminal N off bit stride k j i 0 0 ((AOp.lit 91 0).apply endState):=by
        constructor
        · exact ha.withPC.write 91 0 (by simp [scanControl])
        all_goals simp [endState,AOp.apply,writeNat,next,AOp.value,ha86,ha90]
      refine ⟨_,8,i,0,0,?_,by omega,hterminal,rfl,hi,?_⟩
      · convert hr.trans (hb.trans (hNext.trans (hbranch.trans (hAdd.trans (hJump.trans hZero))))) using 1;rfl
      · exact terminal_decode_add N off bit stride k j (by omega) hj''
    · have cond:¬w.natReg 94<w.natReg 96:=by rw [hwi.jreg,hw96];exact hj''
      simp only [cond,ite_false] at hbranch
      let a:State:={w with pc:=46}
      let i:=j-(count k+count k+(width k+width k))
      have hi:i<width k:=by have hjp:=hh.ordinal;simp only [count] at hjp;dsimp [i];omega
      have hpeak:peakBlock subStep a ≤ cap N G K:=by
        simp [peakBlock,subStep,AOp.value,evalNat,a,hwi.jreg,hw96]
        all_goals omega
      have hSub:=block_runs subStep program 46 n B x a select_blocks_at.2.2 rfl hbranch.final_bound
        (by change 46+2 ≤ B;omega) (select_blocks_valid a).2.2 (hpeak.trans hB)
      have ha:Scanned N off bit stride k j (block subStep a):=hwi.withPC.block subStep select_blocks_keep.2.2
      have ha86:(block subStep a).natReg 86=i:=by
        simp [block,subStep,AOp.apply,AOp.value,evalNat,writeNat,next,a,hwi.jreg,hw96,i]
      have ha90:(block subStep a).natReg 90=1:=by simp [block,subStep,AOp.apply,AOp.value,writeNat,next]
      have hpc:(block subStep a).pc=48:=by rw [block_pc];rfl
      have hZero:=one_runs (.lit 91 0) 48 n B x (block subStep a) hpc rfl hSub.final_bound (by omega)
        (by trivial) (by simp [AOp.value])
      have hterminal:Terminal N off bit stride k j i 1 0 ((AOp.lit 91 0).apply (block subStep a)):=by
        constructor
        · exact ha.write 91 0 (by simp [scanControl])
        all_goals simp [AOp.apply,writeNat,next,AOp.value,ha86,ha90]
      refine ⟨_,7,i,1,0,?_,by omega,hterminal,?_,hi,?_⟩
      · convert hr.trans (hb.trans (hNext.trans (hbranch.trans (hSub.trans hZero)))) using 1;rfl
      · simp [AOp.apply,writeNat,next,hpc]
      · exact terminal_decode_sub N off bit stride k j (by omega)



theorem even_valid (s:State) : validBlock evenStep s := by simp [validBlock,evenStep,AOp.valid,evalNat]
theorem odd_valid (s:State) : validBlock oddStep s := by simp [validBlock,oddStep,AOp.valid,evalNat]

theorem descent_peaks (N G K off bit stride k j:ℕ) (s:State)
    (h:Scanned N off bit stride k j s) (hh:Shape N G K off bit stride (k+1) j) :
    peakBlock evenStep s ≤ cap N G K ∧ peakBlock oddStep s ≤ cap N G K := by
  have b:=hh.bounds
  have hk:k ≤ K:=by have:=hh.height;omega
  have hw:width k ≤ N:=by have:=b.2.2.2.2;simp only [width] at this;omega
  have hc:off+count k ≤ G:=by have:=hh.ord;simp only [count] at this;omega
  have hl:=cap_linear N G K
  constructor
  · simp [peakBlock,evenStep,AOp.apply,AOp.value,evalNat,writeNat,next,h.childK,h.childW,h.sreg,h.zero,h.two]
    all_goals omega
  · simp [peakBlock,oddStep,AOp.apply,AOp.value,evalNat,writeNat,next,
      h.childK,h.childW,h.childC,h.sreg,h.offreg,h.bitreg,h.jreg,h.zero,h.two]
    all_goals omega

/-- Recursive ordinal descent executes the same fixed RAM program. Each strict
child descent reduces the natural height; no host instruction table is supplied. -/
theorem decode_runs (N G K off bit stride k j n B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Config N off bit stride k j s) (hh:Shape N G K off bit stride k j)
    (hs:WordBound B s) (hB:cap N G K ≤ B) (hp:s.pc=16) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 15*k+32 ∧
    rawInstruction u=decode N off bit stride k j := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  induction k generalizing off bit stride j s with
  | zero => have hj:=hh.ordinal;simp only [count] at hj;omega
  | succ k ih =>
    have hscan:=block_runs inspect program 16 n B x s inspect_at hp hs (by change 16+6 ≤ B;omega)
      (inspect_valid N off bit stride k j s h) ((inspect_peak N G K off bit stride k j s h hh).trans hB)
    let v:=block inspect s
    have hvi:Scanned N off bit stride k j v:=inspect_spec N off bit stride k j s h
    have hpv:v.pc=22:=by dsimp [v];rw [block_pc,hp];rfl
    have hb:=branch_runs program n B 94 84 23 27 x v hscan.final_bound (by omega) (by omega) (by rw [hpv];rfl)
    by_cases hj:j<count k
    · have cond:v.natReg 94<v.natReg 84:=by rw [hvi.jreg,hvi.childC];exact hj
      simp only [cond,ite_true] at hb
      let z:State:={v with pc:=23}
      have hr:=block_runs evenStep program 23 n B x z even_at rfl hb.final_bound
        (by change 23+3 ≤ B;omega) (even_valid z)
        ((descent_peaks N G K off bit stride k j z hvi.withPC hh).1.trans hB)
      have hzi:=even_spec N off bit stride k j z hvi.withPC
      have hpz:(block evenStep z).pc=26:=by rw [block_pc];rfl
      have hJump:=jump_runs program n B 16 x (block evenStep z) hr.final_bound (by omega) (by rw [hpz];rfl)
      obtain ⟨u,t,hu,ht,hraw⟩:=ih off bit (2*stride) j {block evenStep z with pc:=16} hzi.withPC (hh.even hj)
        hJump.final_bound rfl
      refine ⟨u,6+1+3+1+t,?_,by omega,?_⟩
      · convert hscan.executes (hb.executes (hr.executes (hJump.executes hu))) using 1
        norm_num [inspect,evenStep];omega
      · rw [hraw];simp only [decode,hj,ite_true]
    · have cond:¬v.natReg 94<v.natReg 84:=by rw [hvi.jreg,hvi.childC];exact hj
      simp only [cond,ite_false] at hb
      let z:State:={v with pc:=27}
      have hb':=branch_runs program n B 94 85 28 35 x z hb.final_bound (by omega) (by omega) rfl
      by_cases hj':j<count k+count k
      · have cond:z.natReg 94<z.natReg 85:=by change v.natReg 94<v.natReg 85;rw [hvi.jreg,hvi.twiceC];exact hj'
        simp only [cond,ite_true] at hb'
        let w:State:={z with pc:=28}
        have hr:=block_runs oddStep program 28 n B x w odd_at rfl hb'.final_bound
          (by change 28+6 ≤ B;omega) (odd_valid w)
          ((descent_peaks N G K off bit stride k j w (hvi.withPC (pc:=27)).withPC hh).2.trans hB)
        have hwi:=odd_spec N off bit stride k j w (hvi.withPC (pc:=27)).withPC
        have hpw:(block oddStep w).pc=34:=by rw [block_pc];rfl
        have hJump:=jump_runs program n B 16 x (block oddStep w) hr.final_bound (by omega) (by rw [hpw];rfl)
        obtain ⟨u,t,hu,ht,hraw⟩:=ih (off+count k) (bit+stride) (2*stride) (j-count k)
          {block oddStep w with pc:=16} hwi.withPC (hh.odd (by omega) hj') hJump.final_bound rfl
        refine ⟨u,6+1+1+6+1+t,?_,by omega,?_⟩
        · convert hscan.executes (hb.executes (hb'.executes (hr.executes (hJump.executes hu)))) using 1
          norm_num [inspect,oddStep];omega
        · rw [hraw];simp only [decode,hj,ite_false,hj',ite_true]
      · have cond:¬z.natReg 94<z.natReg 85:=by change ¬v.natReg 94<v.natReg 85;rw [hvi.jreg,hvi.twiceC];exact hj'
        simp only [cond,ite_false] at hb'
        let w:State:={z with pc:=35}
        obtain ⟨a,t,i,op,exponent,ha,hta,hai,hpa,hi,hdecode⟩:=select_terminal N G K off bit stride k j n B x w
          (hvi.withPC (pc:=27)).withPC hh (by omega) hb'.final_bound hB rfl
        obtain ⟨u,t',hu,htu,hraw⟩:=emit_terminal N G K off bit stride k j i op exponent n B x a hai hh hi
          ha.final_bound hB hpa
        refine ⟨u,6+1+1+t+t',?_,by omega,hraw.trans hdecode⟩
        convert hscan.executes (hb.executes (hb'.executes (ha.executes hu))) using 1
        norm_num [inspect];omega



theorem Frame.refl (s:State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

theorem Frame.trans {s u v:State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi=>(h'.2.2.2.2.2 i hi).trans (h.2.2.2.2.2 i hi)⟩

def safe : Instruction→Prop
  | .natLiteral d _ => 72 ≤ d ∧ d ≤ 96
  | .natBinary _ d _ _ => 72 ≤ d ∧ d ≤ 96
  | .branchLT _ _ _ _ => True
  | .jump _ => True
  | .halt => True
  | _ => False

theorem program_safe : ∀q∈program,safe q := by
  simp [program,setup,grow,start,inspect,evenStep,oddStep,scaleStep,addStep,subStep,
    inputOutput,gateOutput,scaleOutput,binaryResult,scaleResult,AOp.code,safe]

theorem step_frame (n:ℕ) (x:Fin n→ℂ) (s u:State) (h:step program n x s=.running u) : Frame s u := by
  cases hc:program[s.pc]? with
  | none => simp [step,hc] at h
  | some q =>
    have hsafe:safe q:=program_safe q (List.mem_of_getElem? hc)
    cases q <;> try {change False at hsafe;exact False.elim hsafe}
    case natLiteral d v =>
      change 72 ≤ d ∧ d ≤ 96 at hsafe
      simp only [step,hc,StepResult.running.injEq] at h
      subst u
      refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
      intro r hr
      simp [writeNat,next,Function.update_of_ne (show r≠d by omega)]
    case natBinary op d l r =>
      change 72 ≤ d ∧ d ≤ 96 at hsafe
      cases he:evalNat op (s.natReg l) (s.natReg r) with
      | none => simp [step,hc,he] at h
      | some v =>
        simp only [step,hc,he,StepResult.running.injEq] at h
        subst u
        refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
        intro r hr
        simp [writeNat,next,Function.update_of_ne (show r≠d by omega)]
    case branchLT l r yes no =>
      simp only [step,hc,StepResult.running.injEq] at h
      subst u;exact .refl s
    case jump pc =>
      simp only [step,hc,StepResult.running.injEq] at h
      subst u;exact .refl s
    case halt => simp [step,hc] at h

theorem execution_frame {n t:ℕ} {x:Fin n→ℂ} {s u:State} (h:Executes program n x s t u) : Frame s u := by
  induction h with
  | halt _ => exact .refl _
  | next hs _ ih => exact (step_frame _ _ _ _ hs).trans ih

/-- Complete charged decoder from height and ordinal alone. Width, recursive
counts, branch selection and operand addresses are all computed by the fixed
72-instruction program. Initial unrelated state must fit the same word bound. -/
theorem execution (n K J B:ℕ) (x:Fin n→ℂ) (s:State) (hJ:J<count K)
    (hp:s.pc=0) (hK:s.natReg 70=K) (hj:s.natReg 71=J)
    (hs:WordBound B s) (hB:cap (width K) (count K) K ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 19*K+45 ∧
    rawInstruction u=instruction K ⟨J,hJ⟩ ∧ Frame s u := by
  have hcode:100 ≤ B:=(cap_code _ _ _).trans hB
  have hsetup:=block_runs setup program 0 n B x s setup_at hp hs (by change 0+9 ≤ B;omega)
    (setup_valid s) (by rw [setup_peak];omega)
  have hsi:=setup_spec K J s hK hj
  have hsp:(block setup s).pc=9:=by rw [block_pc,hp];rfl
  obtain ⟨v,hv,hvi,hvp⟩:=initialize_loop n K J 0 K B x (block setup s) hsi (by omega)
    hsetup.final_bound hB hsp
  have hstart:=block_runs start program 13 n B x v start_at hvp hv.final_bound (by change 13+3 ≤ B;omega)
    (start_valid v) ((start_peak K J v hvi hJ).trans hB)
  have hstarti:=start_spec K J v hvi
  have hstartp:(block start v).pc=16:=by rw [block_pc,hvp];rfl
  have shape:Shape (width K) (count K) K 0 0 1 K J:=⟨le_rfl,by simp,by omega,by simp,hJ⟩
  obtain ⟨u,t,hu,ht,hraw⟩:=decode_runs (width K) (count K) K 0 0 1 K J n B x (block start v)
    hstarti shape hstart.final_bound hB hstartp
  have hAll:BoundedExecution program n x B s (9+(4*K+1)+(3+t)) u:=by
    convert hsetup.executes (hv.executes (hstart.executes hu)) using 1
    norm_num [setup,start];omega
  exact ⟨u,_,hAll,by omega,hraw.trans (decode_instruction K ⟨J,hJ⟩),execution_frame hAll.executes⟩

/-- The allocation envelope is bounded by 2^(4K+12), before unrelated
caller metadata is included. It is polynomial in the FFT width. -/
theorem cap_power (K:ℕ) : cap (width K) (count K) K ≤ 2^(4*K+12) := by
  have hr:=register_bound K
  have hk:=width_ge_height K
  have hn:=width_pos K
  have ht:width K+count K+K+1 ≤ 6*(width K)^2:=by nlinarith
  have hm:=Nat.mul_le_mul ht ht
  rw [show (6*(width K)^2)*(6*(width K)^2)=36*(width K)^4 by ring] at hm
  have hpos:0<(width K)^4:=pow_pos hn _
  have hcap:cap (width K) (count K) K ≤ 4096*(width K)^4:=by
    unfold cap
    simp only [←pow_two] at hm
    omega
  have he:4096*(width K)^4=2^(4*K+12):=by
    rw [width_eq,pow_add,show 4*K=K*4 by omega,pow_mul]
    norm_num
    ring
  exact hcap.trans_eq he

theorem runtime_bound (K:ℕ) : 19*K+45 ≤ 45*(K+1) := by omega

/-- Pure adaptation of the decoded raw opcode to the existing prepared-power
row layout. This theorem does not claim a row-table producer. -/
theorem decoded_row (K:ℕ) (j:Fin (count K)) :
    UniformRadixTwoMachine.rowOf K (decode (width K) 0 0 1 K j.val)=UniformRadixTwoMachine.row K j := by
  rw [decode_instruction];rfl

end ExactFourierCircuits.UniformRadixInstructionMachine
