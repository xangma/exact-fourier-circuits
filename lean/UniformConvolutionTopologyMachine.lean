import UniformConvolutionDAG
import UniformRadixInstructionMachine
import UniformPreparationRowTableMachine
import UniformBoundedAssembly
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false

namespace ExactFourierCircuits.UniformConvolutionTopologyMachine
open UniformMachine UniformRadixTwoDAG

/-- Five natural fields. Binary records have no coefficient; kind1 is a
prepared-bank slot, kind0 a positive reciprocal denominator. The frozen
convolution graph has no negative prepared slots or other rational scales. -/
structure Row where
  opcode : ℕ
  left : ℕ
  right : ℕ
  kind : ℕ
  payload : ℕ
  deriving DecidableEq, Repr

def encode {r : ℕ} : UniformConvolutionDAG.Expr r ℕ → Row
  | .add a b=>⟨0,a,b,0,0⟩
  | .sub a b=>⟨1,a,b,0,0⟩
  | .scale (.prepared i _) a=>⟨2,a,0,1,i.val⟩
  | .scale (.rational q) a=>⟨2,a,0,0,q.den⟩

def rawRow : Op ℕ → Row
  | .add a b=>⟨0,a,b,0,0⟩
  | .sub a b=>⟨1,a,b,0,0⟩
  | .scale c a=>⟨2,a,0,1,c⟩

def shift (a : ℕ) (r : Row) : Row :=
  {r with left:=a+r.left,right:=if r.opcode<2 then a+r.right else 0}

def outputAddress (k i : ℕ) : ℕ := count k+i

/-- The ordinary ordered FFT output is G+i, including height zero. -/
theorem output_ref (k : ℕ) (i : Fin (width k)) : refNat (output k i)=outputAddress k i.val := by
  cases k with
  | zero=>simp [output,refNat,outputAddress,count]
  | succ k=>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [output,Fin.addCases_left,Fin.val_castAdd]
      change width (k+1)+(nodeFin (k+1) (.add j)).val=count (k+1)+j.val
      rw [nodeFin_add]
      simp only [count,width];omega
    · simp only [output,Fin.addCases_right,Fin.val_natAdd]
      change width (k+1)+(nodeFin (k+1) (.sub j)).val=count (k+1)+(width k+j.val)
      rw [nodeFin_sub]
      simp only [count,width];omega

theorem reciprocal_den (k : ℕ) : ((width k : ℚ)⁻¹).den=width k := by
  rw [Rat.den_inv_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt (width_pos k))),Rat.num_natCast]
  simp

/-- Backward FFT addresses are uniformly translated by N+G. -/
theorem backward_address {k : ℕ} (r : Ref k) :
    UniformConvolutionDAG.address (UniformConvolutionDAG.backwardRef r)=width k+count k+refNat r := by
  cases r <;> simp [UniformConvolutionDAG.address,UniformConvolutionDAG.backwardRef,refNat,UniformConvolutionDAG.nodeFin_diagonal,UniformConvolutionDAG.nodeFin_backward]
  all_goals omega

theorem power_raw (k : ℕ) (g : Op ℕ)
    (h : ∀c∈g.scalars,c<width k) : encode (UniformConvolutionDAG.prepareOp (UniformConvolutionDAG.powerCoefficient k) g)=rawRow g := by
  cases g with
  | add a b=>rfl
  | sub a b=>rfl
  | scale c a=>
    have hc : c<width k:=h c (by simp [Op.scalars])
    simp [UniformConvolutionDAG.prepareOp,UniformConvolutionDAG.powerCoefficient,hc,encode,rawRow]

theorem fft_forward (k : ℕ) (q : UniformRadixTwoDAG.Node k) :
    encode ((UniformConvolutionDAG.gate (.forward q)).map UniformConvolutionDAG.address)=rawRow (instruction k (nodeFin k q)) := by
  have hc : ∀c∈(instruction k (nodeFin k q)).scalars,c<width k:=instruction_scalar_bound k _
  rw [←power_raw k _ hc]
  unfold instruction UniformConvolutionDAG.gate
  rw [Equiv.symm_apply_apply]
  cases hg : gate q <;> simp [UniformConvolutionDAG.prepareOp,UniformConvolutionDAG.Expr.map,Op.map,UniformConvolutionDAG.address_forward,hg]

theorem fft_backward (k : ℕ) (q : UniformRadixTwoDAG.Node k) :
    encode ((UniformConvolutionDAG.gate (.backward q)).map UniformConvolutionDAG.address)=shift (width k+count k) (rawRow (instruction k (nodeFin k q))) := by
  have hc : ∀c∈(instruction k (nodeFin k q)).scalars,c<width k:=instruction_scalar_bound k _
  unfold instruction UniformConvolutionDAG.gate
  rw [Equiv.symm_apply_apply]
  cases hg : gate q with
  | add a b=>simp [UniformConvolutionDAG.prepareOp,UniformConvolutionDAG.Expr.map,Op.map,encode,rawRow,shift,backward_address,hg]
  | sub a b=>simp [UniformConvolutionDAG.prepareOp,UniformConvolutionDAG.Expr.map,Op.map,encode,rawRow,shift,backward_address,hg]
  | scale c a=>
    have hcc : c<width k:=by simpa [instruction,hg,Op.map,Op.scalars] using hc c (by simp [instruction,hg,Op.map,Op.scalars])
    simp [UniformConvolutionDAG.prepareOp,UniformConvolutionDAG.Expr.map,Op.map,UniformConvolutionDAG.powerCoefficient,hcc,encode,rawRow,shift,backward_address,hg]

def rowAt (k j : ℕ) : Row :=
  if j<count k then rawRow (UniformRadixInstructionMachine.decode (width k) 0 0 1 k j)
  else if j<count k+width k then ⟨2,outputAddress k (j-count k),0,1,width k+(j-count k)⟩
  else if j<(count k+width k)+count k then
    shift (width k+count k) (rawRow (UniformRadixInstructionMachine.decode (width k) 0 0 1 k (j-(count k+width k))))
  else ⟨2,width k+count k+outputAddress k ((width k-(j-((count k+width k)+count k)))%width k),0,0,width k⟩

theorem rowAt_node (k : ℕ) (q : UniformConvolutionDAG.Node k) :
    rowAt k (UniformConvolutionDAG.nodeFin k q).val=encode ((UniformConvolutionDAG.gate q).map UniformConvolutionDAG.address) := by
  cases q with
  | forward q=>
    have hq : (nodeFin k q).val<count k:=(nodeFin k q).isLt
    simp only [UniformConvolutionDAG.nodeFin_forward,rowAt,hq,ite_true]
    rw [UniformRadixInstructionMachine.decode_instruction k (nodeFin k q),fft_forward]
  | diagonal i=>
    have hi:=i.isLt
    rw [UniformConvolutionDAG.nodeFin_diagonal]
    unfold rowAt
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode,UniformConvolutionDAG.address_forward,output_ref,outputAddress]
    omega
  | backward q=>
    have hq : (nodeFin k q).val<count k:=(nodeFin k q).isLt
    rw [UniformConvolutionDAG.nodeFin_backward]
    unfold rowAt
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [UniformRadixInstructionMachine.decode_instruction k (nodeFin k q),fft_backward]
  | normalize i=>
    have hi:=i.isLt
    rw [UniformConvolutionDAG.nodeFin_normalize]
    unfold rowAt
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
    simp only [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode,reciprocal_den,backward_address,output_ref,UniformConvolutionDAG.reverseIndex]
    simp [outputAddress]

theorem rowAt_instruction (k : ℕ) (j : Fin (UniformConvolutionDAG.total k)) : rowAt k j.val=encode (UniformConvolutionDAG.instruction k j) := by
  have h:=rowAt_node k ((UniformConvolutionDAG.nodeFin k).symm j)
  simpa [UniformConvolutionDAG.instruction] using h

theorem rowAt_records (k : ℕ) :
    (List.finRange (UniformConvolutionDAG.total k)).map (fun j=>rowAt k j.val)=(UniformConvolutionDAG.records k).map encode := by
  simp only [UniformConvolutionDAG.records,List.map_map]
  apply List.map_congr_left;intro j _;exact rowAt_instruction k j

/-- Nat400=height, Nat401=fresh natural tape base. No coefficients or
preprinted node tape are read. Only Nat70..96 and400..419 are written. -/
def head : Program := [
  .natLiteral 408 0,.natLiteral 409 1,.natLiteral 410 2,.natLiteral 411 3,.natLiteral 412 5,
  .natLiteral 402 1,.natLiteral 403 0,.branchLT 403 400 8 11,
  .natBinary .mul 402 402 410,.natBinary .add 403 403 409,.jump 7,
  .natBinary .mul 403 411 400,.natBinary .mul 403 403 402,.natBinary .div 403 403 410,
  .natBinary .add 404 403 402,.natBinary .add 404 404 403,.natBinary .add 404 404 402,
  .natLiteral 405 0,.natBinary .add 406 401 408,.branchLT 405 404 20 153,
  .branchLT 405 403 21 25,.natBinary .add 70 400 408,.natBinary .add 71 405 408,
  .natLiteral 407 0,.jump 33,.natBinary .add 413 403 402,.branchLT 405 413 135 27,
  .natBinary .add 419 413 403,.branchLT 405 419 29 142,
  .natBinary .add 70 400 408,.natBinary .sub 71 405 413,.natLiteral 407 1,.jump 33]

def tail : Program := [
  .branchLT 90 410 106 112,.natBinary .add 414 90 408,.natBinary .add 415 92 408,
  .natBinary .add 416 93 408,.natLiteral 417 0,.natLiteral 418 0,.jump 117,
  .natLiteral 414 2,.natBinary .add 415 92 408,.natLiteral 416 0,.natLiteral 417 1,.natBinary .add 418 91 408,
  .branchLT 407 409 123 118,.natBinary .add 413 402 403,.natBinary .add 415 415 413,
  .branchLT 414 410 121 123,.natBinary .add 416 416 413,.jump 123,
  .storeNat 406 414,.natBinary .add 406 406 409,.storeNat 406 415,.natBinary .add 406 406 409,
  .storeNat 406 416,.natBinary .add 406 406 409,.storeNat 406 417,.natBinary .add 406 406 409,
  .storeNat 406 418,.natBinary .add 406 406 409,.natBinary .add 405 405 409,.jump 19,
  .natBinary .sub 419 405 403,.natLiteral 414 2,.natLiteral 416 0,.natLiteral 417 1,
  .natBinary .add 418 402 419,.natBinary .add 415 403 419,.jump 123,
  .natBinary .sub 419 405 419,.natBinary .sub 413 402 419,.natBinary .mod 413 413 402,
  .natLiteral 414 2,.natLiteral 416 0,.natLiteral 417 0,.natBinary .add 418 402 408,
  .natBinary .add 415 403 413,.natBinary .add 415 415 403,.natBinary .add 415 415 402,.jump 123,.halt]

def program : Program := UniformAssembly.embed head UniformRadixInstructionMachine.program tail 105

theorem head_length : head.length=33 := rfl
theorem tail_length : tail.length=49 := rfl
theorem program_length : program.length=154 := by
  rw [program,UniformAssembly.embed_length,head_length,UniformRadixInstructionMachine.program_length,tail_length]

theorem decoder_code : UniformAssembly.CodeAt UniformRadixInstructionMachine.program program 33 105 := by
  simpa only [program,head_length] using UniformAssembly.embed_code head UniformRadixInstructionMachine.program tail 105


open UniformRadixInstructionMachine (AOp block validBlock peakBlock BlockAt block_runs block_pc block_keeps)
noncomputable section

def allocation (K d : ℕ) : ℕ := d+5*UniformConvolutionDAG.total K+
  UniformRadixInstructionMachine.cap (width K) (count K) K+500

theorem allocation_code (K d : ℕ) : 500 ≤ allocation K d := by unfold allocation;omega

theorem allocation_cap (K d : ℕ) :
    UniformRadixInstructionMachine.cap (width K) (count K) K ≤ allocation K d := by unfold allocation;omega

theorem allocation_tape (K d : ℕ) : d+5*UniformConvolutionDAG.total K ≤ allocation K d := by unfold allocation;omega

structure Constants (s : State) : Prop where
  zero : s.natReg 408=0
  one : s.natReg 409=1
  two : s.natReg 410=2
  three : s.natReg 411=3
  five : s.natReg 412=5

structure Context (K d j : ℕ) (s : State) : Prop extends Constants s where
  height : s.natReg 400=K
  base : s.natReg 401=d
  Nreg : s.natReg 402=width K
  Greg : s.natReg 403=count K
  total : s.natReg 404=UniformConvolutionDAG.total K
  index : s.natReg 405=j
  pointer : s.natReg 406=d+5*j

def controls : List ℕ := [400,401,402,403,404,405,406,408,409,410,411,412]

theorem Context.withPC {K d j pc : ℕ} {s : State} (h : Context K d j s) : Context K d j {s with pc:=pc} := by
  rcases h with ⟨⟨hz,ho,ht,h3,h5⟩,hk,hd,hN,hG,hT,hj,hp⟩
  exact ⟨⟨hz,ho,ht,h3,h5⟩,hk,hd,hN,hG,hT,hj,hp⟩

theorem Context.congr {K d j : ℕ} {s u : State} (h : Context K d j s)
    (he : ∀r∈controls,u.natReg r=s.natReg r) : Context K d j u := by
  constructor
  · constructor <;> rw [he _ (by simp [controls])] <;>
      first | exact h.zero | exact h.one | exact h.two | exact h.three | exact h.five
  all_goals rw [he _ (by simp [controls])] ; first | exact h.height | exact h.base | exact h.Nreg | exact h.Greg | exact h.total | exact h.index | exact h.pointer

theorem Context.block {K d j : ℕ} {s : State} (h : Context K d j s)
    (b : List AOp) (hb : ∀o∈b,o.dst∉controls) : Context K d j (block b s) :=
  h.congr (fun r hr=>block_keeps b s r (fun o ho he=>hb o ho (he ▸ hr)))

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀r,((r<70 ∨ 96<r) ∧ (r<400 ∨ 419<r)) → u.natReg r=s.natReg r

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem Frame.withPC (s : State) (pc : ℕ) : Frame s {s with pc:=pc} := Frame.refl s

theorem Frame.decoder {s u : State} (h : UniformRadixInstructionMachine.Frame s u) : Frame s u :=
  ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,fun r hr=>h.2.2.2.2.2 r (by omega)⟩

def safe : Instruction → Prop
  | .natLiteral d _ | .natBinary _ d _ _ => (70 ≤ d ∧ d ≤ 96) ∨ (400 ≤ d ∧ d ≤ 419)
  | .storeNat _ _ | .branchLT _ _ _ _ | .jump _ | .halt=>True
  | _=>False

theorem safe_relocate (b r : ℕ) (q : Instruction) : safe (UniformAssembly.relocate b r q)=safe q := by
  cases q <;> rfl

theorem safe_decoder (q : Instruction) (h : UniformRadixInstructionMachine.safe q) : safe q := by
  cases q <;> simp_all [safe,UniformRadixInstructionMachine.safe] <;> omega

theorem program_safe : ∀q∈program,safe q := by
  intro q hq
  simp only [program,UniformAssembly.embed,List.mem_append,List.mem_map] at hq
  rcases hq with (h|⟨a,ha,rfl⟩)|h
  · have hh : ∀q∈head,safe q := by simp [head,safe]
    exact hh q h
  · rw [safe_relocate];exact safe_decoder a (UniformRadixInstructionMachine.program_safe a ha)
  · have hh : ∀q∈tail,safe q := by simp [tail,safe]
    exact hh q h

theorem step_frame (n : ℕ) (x : Fin n → ℂ) (s u : State) (h : step program n x s=.running u) : Frame s u := by
  cases hc : program[s.pc]? with
  | none=>simp [step,hc] at h
  | some q=>
    have hq:=program_safe q (List.mem_of_getElem? hc)
    cases q <;> try {change False at hq;exact False.elim hq}
    case natLiteral d v=>
      simp only [step,hc,StepResult.running.injEq] at h;subst u
      refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr
      simp [writeNat,next,Function.update_of_ne (show r ≠ d by simp only [safe] at hq;omega)]
    case natBinary op d l r=>
      cases he : evalNat op (s.natReg l) (s.natReg r) with
      | none=>simp [step,hc,he] at h
      | some v=>
        simp only [step,hc,he,StepResult.running.injEq] at h;subst u
        refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro z hz
        simp [writeNat,next,Function.update_of_ne (show z ≠ d by simp only [safe] at hq;omega)]
    case storeNat a r=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case branchLT l r y n=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case jump pc=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case halt=>simp [step,hc] at h

theorem execution_frame {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : Executes program n x s t u) : Frame s u := by
  induction h with
  | halt _=>exact Frame.refl _
  | next hs _ ih=>exact (step_frame _ _ _ _ hs).trans ih

structure Fields (r : Row) (s : State) : Prop where
  opcode : s.natReg 414=r.opcode
  left : s.natReg 415=r.left
  right : s.natReg 416=r.right
  kind : s.natReg 417=r.kind
  payload : s.natReg 418=r.payload

def storeRow (heap : ℕ → Option ℕ) (a : ℕ) (r : Row) : ℕ → Option ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update heap a (some r.opcode))
    (a+1) (some r.left)) (a+2) (some r.right)) (a+3) (some r.kind)) (a+4) (some r.payload)

def Printed (K d j : ℕ) (s : State) : Prop := ∀q : Fin (UniformConvolutionDAG.total K),q.val<j → 
  s.natHeap (d+5*q.val)=some (rowAt K q.val).opcode ∧
  s.natHeap (d+5*q.val+1)=some (rowAt K q.val).left ∧
  s.natHeap (d+5*q.val+2)=some (rowAt K q.val).right ∧
  s.natHeap (d+5*q.val+3)=some (rowAt K q.val).kind ∧
  s.natHeap (d+5*q.val+4)=some (rowAt K q.val).payload

def Outside (d m : ℕ) (heap : ℕ → Option ℕ) (s : State) : Prop :=
  ∀a,(a<d ∨ d+m ≤ a) → s.natHeap a=heap a

theorem storeRow_fields (heap : ℕ → Option ℕ) (a : ℕ) (r : Row) :
    storeRow heap a r a=some r.opcode ∧ storeRow heap a r (a+1)=some r.left ∧
    storeRow heap a r (a+2)=some r.right ∧ storeRow heap a r (a+3)=some r.kind ∧
    storeRow heap a r (a+4)=some r.payload := by simp [storeRow]

theorem storeRow_keeps (heap : ℕ → Option ℕ) (a : ℕ) (r : Row) (i : ℕ)
    (hi : i < a ∨ a+5 ≤ i) : storeRow heap a r i=heap i := by
  simp [storeRow,Function.update_of_ne (show i ≠ a by omega),Function.update_of_ne (show i ≠ a+1 by omega),
    Function.update_of_ne (show i ≠ a+2 by omega),Function.update_of_ne (show i ≠ a+3 by omega),Function.update_of_ne (show i ≠ a+4 by omega)]


def setup : List AOp := [.lit 408 0,.lit 409 1,.lit 410 2,.lit 411 3,.lit 412 5,.lit 402 1,.lit 403 0]
def grow : List AOp := [.bin .mul 402 402 410,.bin .add 403 403 409]
def sizes : List AOp := [.bin .mul 403 411 400,.bin .mul 403 403 402,.bin .div 403 403 410,
  .bin .add 404 403 402,.bin .add 404 404 403,.bin .add 404 404 402,.lit 405 0,.bin .add 406 401 408]

theorem setup_code : BlockAt setup program 0 := by intro j;fin_cases j <;> rfl
theorem grow_code : BlockAt grow program 8 := by intro j;fin_cases j <;> rfl
theorem sizes_code : BlockAt sizes program 11 := by intro j;fin_cases j <;> rfl

theorem block_heap (os : List AOp) (s : State) : (block os s).natHeap=s.natHeap := by
  induction os generalizing s with
  | nil=>rfl
  | cons o os ih=>rw [block,ih];cases o <;> rfl

structure Initializing (K d t : ℕ) (s : State) : Prop extends Constants s where
  height : s.natReg 400=K
  base : s.natReg 401=d
  Nreg : s.natReg 402=width t
  index : s.natReg 403=t

theorem Initializing.withPC {K d t pc : ℕ} {s : State} (h : Initializing K d t s) :
    Initializing K d t {s with pc:=pc} := by
  rcases h with ⟨⟨hz,ho,ht,h3,h5⟩,hk,hd,hN,hj⟩;exact ⟨⟨hz,ho,ht,h3,h5⟩,hk,hd,hN,hj⟩

theorem setup_spec (K d : ℕ) (s : State) (hk : s.natReg 400=K) (hd : s.natReg 401=d) :
    Initializing K d 0 (block setup s) := by
  constructor
  · constructor <;> rfl
  all_goals simp [block,setup,AOp.apply,AOp.value,writeNat,next,hk,hd,width]

theorem setup_valid (s : State) : validBlock setup s := by simp [validBlock,setup,AOp.valid]
theorem setup_peak (s : State) : peakBlock setup s=5 := rfl

theorem grow_spec (K d t : ℕ) (s : State) (h : Initializing K d t s) :
    Initializing K d (t+1) (block grow s) := by
  constructor
  · constructor <;> simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three,h.five]
  all_goals simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.base,h.Nreg,h.index,h.one,h.two,width,Nat.mul_two]

theorem grow_valid (s : State) : validBlock grow s := by simp [validBlock,grow,AOp.valid,evalNat]

theorem grow_peak (K d t : ℕ) (s : State) (h : Initializing K d t s) (ht : t<K) :
    peakBlock grow s ≤ allocation K d := by
  have hw:=UniformRadixInstructionMachine.width_mono (show t ≤ K by omega)
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  simp [peakBlock,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.index,h.one,h.two]
  constructor <;> omega

/-- Width is formed by the literal doubling loop rather than supplied. -/
theorem initialize_loop (n K d t fuel B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Initializing K d t s) (ht : t+fuel=K) (hs : WordBound B s)
    (hB : allocation K d ≤ B) (hp : s.pc=7) : ∃u,
    BoundedRuns program n x B s (4*fuel+1) u ∧ Initializing K d K u ∧ u.pc=11 ∧ u.natHeap=s.natHeap := by
  have hcode : 500 ≤ B := (allocation_code K d).trans hB
  induction fuel generalizing t s with
  | zero=>
    have he : t=K := by omega
    have hb:=UniformRadixInstructionMachine.branch_runs program n B 403 400 8 11 x s hs (by omega) (by omega)
      (by rw [hp];rfl)
    have hc : ¬s.natReg 403<s.natReg 400 := by rw [h.index,h.height,he];omega
    simp only [hc,ite_false] at hb
    exact ⟨{s with pc:=11},by simpa using hb,by simpa [he] using h.withPC (pc:=11),rfl,rfl⟩
  | succ fuel ih=>
    have htK : t<K := by omega
    have hb:=UniformRadixInstructionMachine.branch_runs program n B 403 400 8 11 x s hs (by omega) (by omega)
      (by rw [hp];rfl)
    have hc : s.natReg 403<s.natReg 400 := by rw [h.index,h.height];exact htK
    simp only [hc,ite_true] at hb
    let v : State := {s with pc:=8}
    have hg:=block_runs grow program 8 n B x v grow_code rfl hb.final_bound (by change 8+2 ≤ B;omega)
      (grow_valid v) ((grow_peak K d t v h.withPC htK).trans hB)
    have hv:=grow_spec K d t v h.withPC
    have hpv : (block grow v).pc=10 := by rw [block_pc];rfl
    have hj:=UniformRadixInstructionMachine.jump_runs program n B 7 x (block grow v) hg.final_bound (by omega)
      (by rw [hpv];rfl)
    obtain ⟨u,hu,hui,hup,hheap⟩:=ih (t+1) {block grow v with pc:=7} hv.withPC (by omega) hj.final_bound rfl
    refine ⟨u,?_,hui,hup,hheap.trans (block_heap grow v)⟩
    convert hb.trans (hg.trans (hj.trans hu)) using 1
    simp only [show grow.length=2 from rfl];omega

theorem sizes_valid (s : State) (h : s.natReg 410=2) : validBlock sizes s := by
  simp [validBlock,sizes,AOp.valid,AOp.apply,AOp.value,evalNat,writeNat,next,h]

theorem sizes_spec (K d : ℕ) (s : State) (h : Initializing K d K s) : Context K d 0 (block sizes s) := by
  have hc:=UniformRadixInstructionMachine.count_div K
  constructor
  · constructor <;> simp [block,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three,h.five]
  all_goals simp [block,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.base,h.Nreg,h.zero,h.two,h.three,hc,UniformConvolutionDAG.total]

theorem sizes_peak (K d : ℕ) (s : State) (h : Initializing K d K s) : peakBlock sizes s ≤ allocation K d := by
  have hc:=UniformRadixInstructionMachine.count_div K
  have hcount : 3*K*width K=2*count K := by have h:=count_exact K;omega
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  have ht:=allocation_tape K d
  simp [peakBlock,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.base,h.Nreg,h.zero,h.two,h.three,hcount]
  all_goals omega

/-- The startup derives both the FFT and convolution gate counts. -/
theorem startup (n K d B : ℕ) (x : Fin n → ℂ) (s : State)
    (hk : s.natReg 400=K) (hd : s.natReg 401=d) (hp : s.pc=0)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u,
    BoundedRuns program n x B s (4*K+16) u ∧ Context K d 0 u ∧ u.pc=19 ∧ u.natHeap=s.natHeap := by
  have hcode : 500 ≤ B := (allocation_code K d).trans hB
  have hsetup:=block_runs setup program 0 n B x s setup_code hp hs (by change 0+7 ≤ B;omega)
    (setup_valid s) (by rw [setup_peak];omega)
  have hsi:=setup_spec K d s hk hd
  have hsp : (block setup s).pc=7 := by rw [block_pc,hp];rfl
  obtain ⟨v,hv,hvi,hvp,hheap⟩:=initialize_loop n K d 0 K B x (block setup s) hsi (by omega) hsetup.final_bound hB hsp
  have hsize:=block_runs sizes program 11 n B x v sizes_code hvp hv.final_bound (by change 11+8 ≤ B;omega)
    (sizes_valid v hvi.two) ((sizes_peak K d v hvi).trans hB)
  refine ⟨block sizes v,?_,sizes_spec K d v hvi,?_,(block_heap sizes v).trans (hheap.trans (block_heap setup s))⟩
  · convert (hsetup.trans hv).trans hsize using 1
    simp only [show setup.length=7 from rfl,show sizes.length=8 from rfl];omega
  · rw [block_pc,hvp];rfl


def binary : List AOp := [.bin .add 414 90 408,.bin .add 415 92 408,.bin .add 416 93 408,.lit 417 0,.lit 418 0]
def scale : List AOp := [.lit 414 2,.bin .add 415 92 408,.lit 416 0,.lit 417 1,.bin .add 418 91 408]
def shiftLeft : List AOp := [.bin .add 413 402 403,.bin .add 415 415 413]
def shiftRight : List AOp := [.bin .add 416 416 413]

theorem binary_code : BlockAt binary program 106 := by intro j;fin_cases j <;> rfl
theorem scale_code : BlockAt scale program 112 := by intro j;fin_cases j <;> rfl
theorem shiftLeft_code : BlockAt shiftLeft program 118 := by intro j;fin_cases j <;> rfl
theorem shiftRight_code : BlockAt shiftRight program 121 := by intro j;fin_cases j;rfl

theorem adapters_valid (s : State) : validBlock binary s ∧ validBlock scale s ∧
    validBlock shiftLeft s ∧ validBlock shiftRight s := by
  simp [validBlock,binary,scale,shiftLeft,shiftRight,AOp.valid,evalNat]

theorem adapters_keep : (∀o∈binary,o.dst∉controls) ∧ (∀o∈scale,o.dst∉controls) ∧
    (∀o∈shiftLeft,o.dst∉controls) ∧ (∀o∈shiftRight,o.dst∉controls) := by
  simp [binary,scale,shiftLeft,shiftRight,AOp.dst,controls]

theorem Fields.withPC {r : Row} {s : State} {pc : ℕ} (h : Fields r s) : Fields r {s with pc:=pc} :=
  ⟨h.opcode,h.left,h.right,h.kind,h.payload⟩

theorem raw_bound (K : ℕ) (q : Fin (count K)) (s : State)
    (hr : UniformRadixInstructionMachine.rawInstruction s=instruction K q) :
    s.natReg 92<width K+count K ∧
    (s.natReg 90<2 → s.natReg 93<width K+count K) ∧
    (¬s.natReg 90<2 → s.natReg 91<width K) := by
  have hleft : s.natReg 92∈(UniformRadixInstructionMachine.rawInstruction s).refs := by
    unfold UniformRadixInstructionMachine.rawInstruction;split_ifs <;> simp [Op.refs]
  have hl:=printed_refs_before K q (s.natReg 92) (by change s.natReg 92∈(instruction K q).refs;rw [←hr];exact hleft)
  refine ⟨by have hq:=q.isLt;omega,?_,?_⟩
  · intro hop
    have hright : s.natReg 93∈(UniformRadixInstructionMachine.rawInstruction s).refs := by
      unfold UniformRadixInstructionMachine.rawInstruction
      split_ifs <;> simp [Op.refs];omega
    have h:=printed_refs_before K q (s.natReg 93) (by change s.natReg 93∈(instruction K q).refs;rw [←hr];exact hright)
    have hq:=q.isLt;omega
  · intro hop
    have hc : s.natReg 91∈(UniformRadixInstructionMachine.rawInstruction s).scalars := by
      simp [UniformRadixInstructionMachine.rawInstruction,show s.natReg 90 ≠ 0 by omega,
        show s.natReg 90 ≠ 1 by omega,Op.scalars]
    exact instruction_scalar_bound K q _ (hr ▸ hc)

theorem binary_spec {K d j : ℕ} {s : State} (h : Context K d j s) (hop : s.natReg 90<2) :
    Fields (rawRow (UniformRadixInstructionMachine.rawInstruction s)) (block binary s) := by
  by_cases h0 : s.natReg 90=0
  · constructor <;> simp [block,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,
      rawRow,UniformRadixInstructionMachine.rawInstruction,h0]
  · have h1 : s.natReg 90=1 := by omega
    constructor <;> simp [block,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,
      rawRow,UniformRadixInstructionMachine.rawInstruction,h1]

theorem scale_spec {K d j : ℕ} {s : State} (h : Context K d j s) (hop : ¬s.natReg 90<2) :
    Fields (rawRow (UniformRadixInstructionMachine.rawInstruction s)) (block scale s) := by
  have h0 : s.natReg 90 ≠ 0 := by omega
  have h1 : s.natReg 90 ≠ 1 := by omega
  constructor <;> simp [block,scale,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,
    rawRow,UniformRadixInstructionMachine.rawInstruction,h0,h1]

theorem adapter_peaks {K d j B : ℕ} {s : State} (h : Context K d j s) (hs : WordBound B s)
    (hc : 500 ≤ B) : peakBlock binary s ≤ B ∧ peakBlock scale s ≤ B := by
  have h90:=hs.2.1 90
  have h91:=hs.2.1 91
  have h92:=hs.2.1 92
  have h93:=hs.2.1 93
  simp [peakBlock,binary,scale,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero]
  omega

def afterShift (backward : Bool) (K : ℕ) (r : Row) : Row := if backward then shift (width K+count K) r else r

/-- Backward input and internal references receive the same charged offset. -/
theorem shift_finish (n K d j B : ℕ) (r : Row) (backward : Bool) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hf : Fields r s) (hb : s.natReg 407=if backward then 1 else 0)
    (hl : r.left ≤ width K+count K) (hr : r.right ≤ width K+count K)
    (hz : ¬ r.opcode < 2 → r.right=0)
    (hp : s.pc=117) (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 6 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (afterShift backward K r) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hcap:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans ((allocation_cap K d).trans hB)
  have hbranch:=UniformRadixInstructionMachine.branch_runs program n B 407 409 123 118 x s hs (by omega) (by omega)
    (by rw [hp];rfl)
  cases backward with
  | false=>
    have hcond : s.natReg 407<s.natReg 409 := by rw [hb,h.one];decide
    simp only [hcond,ite_true] at hbranch
    exact ⟨{s with pc:=123},1,hbranch,by omega,h.withPC,rfl,hf.withPC,rfl⟩
  | true=>
    have hcond : ¬s.natReg 407<s.natReg 409 := by rw [hb,h.one];decide
    simp only [hcond,ite_false] at hbranch
    let v : State := {s with pc:=118}
    have hv:=block_runs shiftLeft program 118 n B x v shiftLeft_code rfl hbranch.final_bound
      (by change 118+2 ≤ B;omega) (adapters_valid v).2.2.1
      (by simp [peakBlock,shiftLeft,AOp.apply,AOp.value,evalNat,writeNat,next,v,h.Nreg,h.Greg,hf.left];omega)
    let w:=block shiftLeft v
    have hwc : Context K d j w := h.withPC.block shiftLeft adapters_keep.2.2.1
    have hwp : w.pc=120 := by rw [block_pc];rfl
    have hwf : Fields {r with left:=width K+count K+r.left} w := by
      constructor <;> simp [w,v,block,shiftLeft,AOp.apply,AOp.value,evalNat,writeNat,next,
        h.Nreg,h.Greg,hf.opcode,hf.left,hf.right,hf.kind,hf.payload,Nat.add_comm]
    have hwo : w.natReg 413=width K+count K := by
      simp [w,v,block,shiftLeft,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.Greg]
    have hb':=UniformRadixInstructionMachine.branch_runs program n B 414 410 121 123 x w hv.final_bound
      (by omega) (by omega) (by rw [hwp];rfl)
    by_cases hop : r.opcode<2
    · have hcond : w.natReg 414<w.natReg 410 := by rw [hwf.opcode,hwc.two];exact hop
      simp only [hcond,ite_true] at hb'
      let z : State := {w with pc:=121}
      have hz:=block_runs shiftRight program 121 n B x z shiftRight_code rfl hb'.final_bound
        (by change 121+1 ≤ B;omega) (adapters_valid z).2.2.2
        (by simp [peakBlock,shiftRight,AOp.value,evalNat,z,hwf.right,hwo];omega)
      let u:=block shiftRight z
      have hup : u.pc=122 := by rw [block_pc];rfl
      have hu':=UniformRadixInstructionMachine.jump_runs program n B 123 x u hz.final_bound (by omega)
        (by rw [hup];rfl)
      refine ⟨{u with pc:=123},6,?_,by omega,(hwc.withPC.block shiftRight adapters_keep.2.2.2).withPC,rfl,?_,?_⟩
      · convert ((hbranch.trans hv).trans hb').trans (hz.trans hu') using 1;rfl
      · constructor <;> simp [afterShift,shift,hop,u,z,block,shiftRight,AOp.apply,AOp.value,evalNat,writeNat,next,
          hwf.opcode,hwf.left,hwf.right,hwf.kind,hwf.payload,hwo,Nat.add_comm]
      · exact (block_heap shiftRight z).trans (block_heap shiftLeft v)
    · have hcond : ¬w.natReg 414<w.natReg 410 := by rw [hwf.opcode,hwc.two];exact hop
      simp only [hcond,ite_false] at hb'
      refine ⟨{w with pc:=123},4,(hbranch.trans hv).trans hb',by omega,hwc.withPC,rfl,?_,block_heap shiftLeft v⟩
      constructor <;> simp [afterShift,shift,hop,hwf.opcode,hwf.left,hwf.right,hwf.kind,hwf.payload,hz hop]
      -- Scale fields have a syntactic zero right operand.


theorem rawRow_zero (o : Op ℕ) : ¬(rawRow o).opcode<2 → (rawRow o).right=0 := by
  cases o <;> simp [rawRow]

theorem rawRow_bound (K : ℕ) (q : Fin (count K)) (s : State)
    (h : UniformRadixInstructionMachine.rawInstruction s=instruction K q) :
    (rawRow (UniformRadixInstructionMachine.rawInstruction s)).left ≤ width K+count K ∧
    (rawRow (UniformRadixInstructionMachine.rawInstruction s)).right ≤ width K+count K := by
  have hb:=raw_bound K q s h
  unfold UniformRadixInstructionMachine.rawInstruction
  split_ifs <;> simp only [rawRow]
  all_goals constructor
  all_goals first | exact hb.1.le | exact (hb.2.1 (by omega)).le | omega

/-- The common decoder-result adapter uses real branches and adds, including
both backward operand offsets. It reads no coefficient values. -/
theorem adapter (n K d j B : ℕ) (q : Fin (count K)) (backward : Bool) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hr : UniformRadixInstructionMachine.rawInstruction s=instruction K q)
    (hb : s.natReg 407=if backward then 1 else 0) (hp : s.pc=105)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 13 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (afterShift backward K (rawRow (instruction K q))) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hbounds:=rawRow_bound K q s hr
  have hfinish : ∀v : State,Context K d j v → Fields (rawRow (UniformRadixInstructionMachine.rawInstruction s)) v → 
      v.natReg 407=(if backward then 1 else 0) → v.pc=117 → WordBound B v → v.natHeap=s.natHeap → ∃u t,
      BoundedRuns program n x B v t u ∧ t ≤ 6 ∧ Context K d j u ∧ u.pc=123 ∧
      Fields (afterShift backward K (rawRow (instruction K q))) u ∧ u.natHeap=s.natHeap := by
    intro v hv hf hphase hpv hsv hheap
    obtain ⟨u,t,hu,ht,huc,hup,huf,huh⟩:=shift_finish n K d j B _ backward x v hv hf hphase hbounds.1 hbounds.2
      (rawRow_zero _) hpv hsv hB
    exact ⟨u,t,hu,ht,huc,hup,by simpa [hr] using huf,huh.trans hheap⟩
  have hbranch:=UniformRadixInstructionMachine.branch_runs program n B 90 410 106 112 x s hs (by omega) (by omega)
    (by rw [hp];rfl)
  by_cases hop : s.natReg 90<2
  · have hcond : s.natReg 90<s.natReg 410 := by rw [h.two];exact hop
    simp only [hcond,ite_true] at hbranch
    let v : State := {s with pc:=106}
    have hv:=block_runs binary program 106 n B x v binary_code rfl hbranch.final_bound
      (by change 106+5 ≤ B;omega) (adapters_valid v).1 (adapter_peaks h.withPC hbranch.final_bound hc).1
    let w:=block binary v
    have hwc : Context K d j w := h.withPC.block binary adapters_keep.1
    have hwp : w.pc=111 := by rw [block_pc];rfl
    have hj:=UniformRadixInstructionMachine.jump_runs program n B 117 x w hv.final_bound (by omega) (by rw [hwp];rfl)
    obtain ⟨u,t,hu,ht,huc,hup,huf,huh⟩:=hfinish {w with pc:=117} hwc.withPC
      (binary_spec (h.withPC (pc:=106)) hop).withPC
      (by rw [block_keeps binary v 407 (by simp [binary,AOp.dst])];exact hb)
      rfl hj.final_bound (block_heap binary v)
    refine ⟨u,1+5+1+t,?_,by omega,huc,hup,huf,huh⟩
    exact ((hbranch.trans hv).trans hj).trans hu
  · have hcond : ¬s.natReg 90<s.natReg 410 := by rw [h.two];exact hop
    simp only [hcond,ite_false] at hbranch
    let v : State := {s with pc:=112}
    have hv:=block_runs scale program 112 n B x v scale_code rfl hbranch.final_bound
      (by change 112+5 ≤ B;omega) (adapters_valid v).2.1 (adapter_peaks h.withPC hbranch.final_bound hc).2
    let w:=block scale v
    have hwc : Context K d j w := h.withPC.block scale adapters_keep.2.1
    have hwp : w.pc=117 := by rw [block_pc];rfl
    obtain ⟨u,t,hu,ht,huc,hup,huf,huh⟩:=hfinish w hwc (scale_spec (h.withPC (pc:=112)) hop)
      (by rw [block_keeps scale v 407 (by simp [scale,AOp.dst])];exact hb)
      hwp hv.final_bound (block_heap scale v)
    exact ⟨u,1+5+t,hbranch.trans hv |>.trans hu,by omega,huc,hup,huf,huh⟩

def stores : List UniformPreparationRowTableMachine.Op := [
  .put 406 414,.add 406 406 409,.put 406 415,.add 406 406 409,
  .put 406 416,.add 406 406 409,.put 406 417,.add 406 406 409,
  .put 406 418,.add 406 406 409,.add 405 405 409]

theorem stores_code : UniformPreparationRowTableMachine.BlockAt stores program 123 := by
  intro i hi;change i<11 at hi;interval_cases i <;> rfl

theorem stores_readable (s : State) : UniformPreparationRowTableMachine.readable stores s := by
  simp [UniformPreparationRowTableMachine.readable,stores,UniformPreparationRowTableMachine.Op.readable]

theorem stores_spec (K d j : ℕ) (r : Row) (s : State) (h : Context K d j s) (hf : Fields r s) :
    Context K d (j+1) (UniformPreparationRowTableMachine.applyBlock stores s) ∧
    (UniformPreparationRowTableMachine.applyBlock stores s).natHeap=storeRow s.natHeap (d+5*j) r := by
  constructor
  · constructor
    · constructor <;> simp [UniformPreparationRowTableMachine.applyBlock,stores,UniformPreparationRowTableMachine.Op.apply,
        writeNat,next,h.zero,h.one,h.two,h.three,h.five]
    all_goals simp [UniformPreparationRowTableMachine.applyBlock,stores,UniformPreparationRowTableMachine.Op.apply,
      writeNat,next,h.height,h.base,h.Nreg,h.Greg,h.total,h.index,h.pointer,h.one]
    all_goals omega
  · simp [UniformPreparationRowTableMachine.applyBlock,stores,UniformPreparationRowTableMachine.Op.apply,writeNat,next,
      h.one,h.pointer,hf.opcode,hf.left,hf.right,hf.kind,hf.payload,storeRow,Nat.add_assoc]

/-- Previously emitted records are retained; all five new fields are stored. -/
theorem stores_printed (K d j : ℕ) (s : State) (h : Context K d j s) (_hj : j<UniformConvolutionDAG.total K)
    (hf : Fields (rowAt K j) s) (hp : Printed K d j s) :
    Printed K d (j+1) (UniformPreparationRowTableMachine.applyBlock stores s) := by
  intro q hq
  rw [(stores_spec K d j (rowAt K j) s h hf).2]
  by_cases he : q.val=j
  · rw [he];exact storeRow_fields s.natHeap (d+5*j) (rowAt K j)
  · have hq' : q.val<j := by omega
    have hold:=hp q hq'
    rw [storeRow_keeps s.natHeap (d+5*j) (rowAt K j) (d+5*q.val) (by omega),
      storeRow_keeps s.natHeap (d+5*j) (rowAt K j) (d+5*q.val+1) (by omega),
      storeRow_keeps s.natHeap (d+5*j) (rowAt K j) (d+5*q.val+2) (by omega),
      storeRow_keeps s.natHeap (d+5*j) (rowAt K j) (d+5*q.val+3) (by omega),
      storeRow_keeps s.natHeap (d+5*j) (rowAt K j) (d+5*q.val+4) (by omega)]
    exact hold

theorem stores_outside (K d j : ℕ) (s : State) (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K)
    (r : Row) (hf : Fields r s) (heap : ℕ → Option ℕ) (ho : Outside d (5*UniformConvolutionDAG.total K) heap s) :
    Outside d (5*UniformConvolutionDAG.total K) heap (UniformPreparationRowTableMachine.applyBlock stores s) := by
  intro a ha
  rw [(stores_spec K d j r s h hf).2,storeRow_keeps s.natHeap (d+5*j) r a (by omega)]
  exact ho a ha


theorem encode_left_mem {r : ℕ} (e : UniformConvolutionDAG.Expr r ℕ) : (encode e).left∈e.refs := by
  cases e with
  | add a b | sub a b=>simp [encode,UniformConvolutionDAG.Expr.refs]
  | scale c a=>cases c <;> simp [encode,UniformConvolutionDAG.Expr.refs]

theorem encode_right_mem {r : ℕ} (e : UniformConvolutionDAG.Expr r ℕ)
    (h : (encode e).opcode<2) : (encode e).right∈e.refs := by
  cases e with
  | add a b | sub a b=>simp [encode,UniformConvolutionDAG.Expr.refs]
  | scale c a=>cases c <;> simp [encode] at h

theorem encode_zero_right {r : ℕ} (e : UniformConvolutionDAG.Expr r ℕ) :
    ¬(encode e).opcode<2 → (encode e).right=0 := by
  cases e with
  | add a b | sub a b=>simp [encode]
  | scale c a=>cases c <;> simp [encode]

theorem rowAt_data_bound (K : ℕ) (q : Fin (UniformConvolutionDAG.total K)) :
    (rowAt K q.val).left<width K+UniformConvolutionDAG.total K ∧
    (rowAt K q.val).right<width K+UniformConvolutionDAG.total K := by
  rw [rowAt_instruction]
  have hl:=UniformConvolutionDAG.printed_refs_before K q _ (encode_left_mem (UniformConvolutionDAG.instruction K q))
  refine ⟨by have hq:=q.isLt;omega,?_⟩
  by_cases hop : (encode (UniformConvolutionDAG.instruction K q)).opcode<2
  · have hr:=UniformConvolutionDAG.printed_refs_before K q _ (encode_right_mem _ hop)
    have hq:=q.isLt;omega
  · rw [encode_zero_right _ hop];have h:=width_pos K;omega

theorem encode_shape {r : ℕ} (e : UniformConvolutionDAG.Expr r ℕ) :
    (encode e).opcode ≤ 2 ∧ (encode e).kind ≤ 1 := by
  cases e with
  | add a b | sub a b=>simp [encode]
  | scale c a=>cases c <;> simp [encode]

theorem node_payload_bound (K : ℕ) (q : UniformConvolutionDAG.Node K) :
    (encode ((UniformConvolutionDAG.gate q).map UniformConvolutionDAG.address)).payload ≤ 2*width K := by
  have hw:=width_pos K
  cases q with
  | forward q | backward q=>
    cases hg : gate q with
    | add a b | sub a b=>simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,UniformConvolutionDAG.prepareOp,hg,encode]
    | scale c a=>
      by_cases hc : c<width K
      · simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,UniformConvolutionDAG.prepareOp,hg,UniformConvolutionDAG.powerCoefficient,hc,encode];omega
      · simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,UniformConvolutionDAG.prepareOp,hg,UniformConvolutionDAG.powerCoefficient,hc,encode];omega
  | diagonal i=>simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode];have hi:=i.isLt;omega
  | normalize i=>simp only [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode,reciprocal_den];omega

theorem rowAt_payload_bound (K : ℕ) (q : Fin (UniformConvolutionDAG.total K)) :
    (rowAt K q.val).payload ≤ 2*width K := by
  rw [rowAt_instruction]
  exact node_payload_bound K ((UniformConvolutionDAG.nodeFin K).symm q)

theorem stores_peak (K d j B : ℕ) (s : State) (h : Context K d j s)
    (hj : j<UniformConvolutionDAG.total K) (hf : Fields (rowAt K j) s) (hB : allocation K d ≤ B) :
    UniformPreparationRowTableMachine.peak stores s ≤ B := by
  have ht:=(allocation_tape K d).trans hB
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans ((allocation_cap K d).trans hB)
  have hd:=rowAt_data_bound K ⟨j,hj⟩
  have hs:=encode_shape (UniformConvolutionDAG.instruction K ⟨j,hj⟩)
  rw [←rowAt_instruction] at hs
  have hp:=rowAt_payload_bound K ⟨j,hj⟩
  simp only at hd hs hp
  have hw:=width_pos K
  have hT : UniformConvolutionDAG.total K=2*count K+2*width K := by unfold UniformConvolutionDAG.total;omega
  simp [UniformPreparationRowTableMachine.peak,stores,UniformPreparationRowTableMachine.Op.peak,
    UniformPreparationRowTableMachine.Op.apply,writeNat,next,h.one,h.pointer,h.index,
    hf.opcode,hf.left,hf.right,hf.kind,hf.payload]
  all_goals omega

/-- Five literal stores extend the exact tape and preserve the complement. -/
theorem store_execution (n K d j B : ℕ) (heap : ℕ → Option ℕ) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K) (hf : Fields (rowAt K j) s)
    (hp : s.pc=123) (hs : WordBound B s) (hB : allocation K d ≤ B)
    (hprinted : Printed K d j s) (houtside : Outside d (5*UniformConvolutionDAG.total K) heap s) : ∃u,
    BoundedRuns program n x B s 12 u ∧ Context K d (j+1) u ∧ u.pc=19 ∧
    Printed K d (j+1) u ∧ Outside d (5*UniformConvolutionDAG.total K) heap u := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hr:=UniformPreparationRowTableMachine.block_runs stores program 123 n B x s stores_code hp hs
    (by change 123+11 ≤ B;omega) (stores_readable s) (stores_peak K d j B s h hj hf hB)
  let u:=UniformPreparationRowTableMachine.applyBlock stores s
  have hup : u.pc=134 := by rw [UniformPreparationRowTableMachine.applyBlock_pc,hp];rfl
  have hjump:=UniformRadixInstructionMachine.jump_runs program n B 19 x u hr.final_bound (by omega) (by rw [hup];rfl)
  exact ⟨{u with pc:=19},hr.trans hjump,(stores_spec K d j _ s h hf).1.withPC,rfl,
    stores_printed K d j s h hj hf hprinted,stores_outside K d j s h hj _ hf heap houtside⟩


/-- One invocation of the frozen decoder is an actual placed72 execution. -/
theorem fft_emit (n K d j J B : ℕ) (hJ : J<count K) (backward : Bool) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (h70 : s.natReg 70=K) (h71 : s.natReg 71=J)
    (hphase : s.natReg 407=if backward then 1 else 0) (hp : s.pc=33)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 19*K+58 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (afterShift backward K (rawRow (instruction K ⟨J,hJ⟩))) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  let a : State := {s with pc:=0}
  have ha : WordBound B a := changePC_bound B s 0 hs (by omega)
  obtain ⟨v,t,hv,ht,hraw,hframe⟩:=UniformRadixInstructionMachine.execution n K J B x a hJ rfl h70 h71 ha
    ((allocation_cap K d).trans hB)
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed decoder_code (by change 33+72 ≤ B;omega) (by omega) hv
  have hrun : BoundedRuns program n x B s t {v with pc:=105} := by
    convert hplaced using 1
    cases s
    simp_all [UniformAssembly.placed,a]
  have hvc : Context K d j {v with pc:=105} := by
    apply h.congr;intro r hr
    exact hframe.2.2.2.2.2 r (Or.inr (by simp [controls] at hr;rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega))
  have hvphase : v.natReg 407=if backward then 1 else 0 :=
    (hframe.2.2.2.2.2 407 (Or.inr (by omega))).trans hphase
  obtain ⟨u,w,hu,hw,huc,hup,huf,hheap⟩:=adapter n K d j B ⟨J,hJ⟩ backward x {v with pc:=105}
    hvc hraw hvphase rfl hrun.final_bound hB
  exact ⟨u,t+w,hrun.trans hu,by omega,huc,hup,huf,hheap.trans hframe.1⟩

def forwardSetup : List AOp := [.bin .add 70 400 408,.bin .add 71 405 408,.lit 407 0]
def backwardSetup : List AOp := [.bin .add 70 400 408,.bin .sub 71 405 413,.lit 407 1]
def threshold : List AOp := [.bin .add 413 403 402]
def backwardThreshold : List AOp := [.bin .add 419 413 403]
def diagonal : List AOp := [.bin .sub 419 405 403,.lit 414 2,.lit 416 0,.lit 417 1,
  .bin .add 418 402 419,.bin .add 415 403 419]
def normalize : List AOp := [.bin .sub 419 405 419,.bin .sub 413 402 419,.bin .mod 413 413 402,
  .lit 414 2,.lit 416 0,.lit 417 0,.bin .add 418 402 408,.bin .add 415 403 413,
  .bin .add 415 415 403,.bin .add 415 415 402]

theorem forwardSetup_code : BlockAt forwardSetup program 21 := by intro j;fin_cases j <;> rfl
theorem backwardSetup_code : BlockAt backwardSetup program 29 := by intro j;fin_cases j <;> rfl
theorem threshold_code : BlockAt threshold program 25 := by intro j;fin_cases j;rfl
theorem backwardThreshold_code : BlockAt backwardThreshold program 27 := by intro j;fin_cases j;rfl
theorem diagonal_code : BlockAt diagonal program 135 := by intro j;fin_cases j <;> rfl
theorem normalize_code : BlockAt normalize program 142 := by intro j;fin_cases j <;> rfl

theorem phase_blocks_keep : (∀o∈forwardSetup,o.dst∉controls) ∧ (∀o∈backwardSetup,o.dst∉controls) ∧
    (∀o∈threshold,o.dst∉controls) ∧ (∀o∈backwardThreshold,o.dst∉controls) ∧
    (∀o∈diagonal,o.dst∉controls) ∧ (∀o∈normalize,o.dst∉controls) := by
  simp [forwardSetup,backwardSetup,threshold,backwardThreshold,diagonal,normalize,AOp.dst,controls]

theorem phase_blocks_valid (s : State) : validBlock forwardSetup s ∧ validBlock backwardSetup s ∧
    validBlock threshold s ∧ validBlock backwardThreshold s ∧ validBlock diagonal s := by
  simp [validBlock,forwardSetup,backwardSetup,threshold,backwardThreshold,diagonal,AOp.valid,evalNat]

theorem forwardSetup_spec {K d j : ℕ} {s : State} (h : Context K d j s) :
    (block forwardSetup s).natReg 70=K ∧ (block forwardSetup s).natReg 71=j ∧
    (block forwardSetup s).natReg 407=0 := by
  simp [block,forwardSetup,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.index,h.zero]

theorem backwardSetup_spec {K d j : ℕ} {s : State} (h : Context K d j s)
    (ht : s.natReg 413=count K+width K) :
    (block backwardSetup s).natReg 70=K ∧ (block backwardSetup s).natReg 71=j-(count K+width K) ∧
    (block backwardSetup s).natReg 407=1 := by
  simp [block,backwardSetup,AOp.apply,AOp.value,evalNat,writeNat,next,h.height,h.index,h.zero,ht]

theorem setup_peaks {K d j B : ℕ} {s : State} (h : Context K d j s) (hs : WordBound B s) (hc : 500 ≤ B) :
    peakBlock forwardSetup s ≤ B ∧ peakBlock backwardSetup s ≤ B := by
  have hk:=hs.2.1 400
  have hj:=hs.2.1 405
  simp [peakBlock,forwardSetup,backwardSetup,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero]
  omega

theorem diagonal_spec {K d j : ℕ} {s : State} (h : Context K d j s) :
    Fields ⟨2,count K+(j-count K),0,1,width K+(j-count K)⟩ (block diagonal s) := by
  constructor <;> simp [block,diagonal,AOp.apply,AOp.value,evalNat,writeNat,next,h.index,h.Greg,h.Nreg]

theorem normalize_valid {K d j : ℕ} {s : State} (h : Context K d j s) : validBlock normalize s := by
  have hn : width K ≠ 0 := Nat.ne_of_gt (width_pos K)
  simp [validBlock,normalize,AOp.valid,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,hn]

theorem normalize_spec {K d j : ℕ} {s : State} (h : Context K d j s)
    (ht : s.natReg 419=(count K+width K)+count K) :
    Fields ⟨2,width K+count K+outputAddress K ((width K-(j-((count K+width K)+count K)))%width K),0,0,width K⟩
      (block normalize s) := by
  have hn : width K ≠ 0 := Nat.ne_of_gt (width_pos K)
  constructor <;> simp [block,normalize,AOp.apply,AOp.value,evalNat,writeNat,next,h.index,h.Nreg,h.Greg,h.zero,hn,ht,outputAddress]
  omega

theorem diagonal_peak {K d j : ℕ} {s : State} (h : Context K d j s) (hj : j<count K+width K) :
    peakBlock diagonal s ≤ allocation K d := by
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  have hc:=allocation_code K d
  simp [peakBlock,diagonal,AOp.apply,AOp.value,evalNat,writeNat,next,h.index,h.Nreg,h.Greg]
  all_goals omega

theorem normalize_peak {K d j : ℕ} {s : State} (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K)
    (ht : s.natReg 419=(count K+width K)+count K) : peakBlock normalize s ≤ allocation K d := by
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  have hc:=allocation_code K d
  have hn : width K ≠ 0 := Nat.ne_of_gt (width_pos K)
  have htotal : UniformConvolutionDAG.total K=2*count K+2*width K := by unfold UniformConvolutionDAG.total;omega
  have hmod : (width K-(j-((count K+width K)+count K)))%width K<width K := Nat.mod_lt _ (width_pos K)
  simp [peakBlock,normalize,AOp.apply,AOp.value,evalNat,writeNat,next,h.index,h.Nreg,h.Greg,h.zero,hn,ht]
  all_goals omega



theorem threshold_spec {K d j : ℕ} {s : State} (h : Context K d j s) :
    (block threshold s).natReg 413=count K+width K := by
  simp [block,threshold,AOp.apply,AOp.value,evalNat,writeNat,next,h.Greg,h.Nreg]

theorem backwardThreshold_spec {K d j : ℕ} {s : State} (h : Context K d j s)
    (ht : s.natReg 413=count K+width K) :
    (block backwardThreshold s).natReg 419=(count K+width K)+count K := by
  simp [block,backwardThreshold,AOp.apply,AOp.value,evalNat,writeNat,next,ht,h.Greg]

theorem threshold_peak {K d j : ℕ} {s : State} (h : Context K d j s) :
    peakBlock threshold s ≤ allocation K d := by
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  simp [peakBlock,threshold,AOp.value,evalNat,h.Greg,h.Nreg];omega

theorem backwardThreshold_peak {K d j : ℕ} {s : State} (h : Context K d j s)
    (ht : s.natReg 413=count K+width K) : peakBlock backwardThreshold s ≤ allocation K d := by
  have hl:=(UniformRadixInstructionMachine.cap_linear (width K) (count K) K).trans (allocation_cap K d)
  simp [peakBlock,backwardThreshold,AOp.value,evalNat,h.Greg,ht];omega

/-- Both terminal phases execute their real block and continuation jump. -/
theorem diagonal_emit (n K d j B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hj : j<count K+width K) (hp : s.pc=135)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u,
    BoundedRuns program n x B s 7 u ∧ Context K d j u ∧ u.pc=123 ∧
    Fields ⟨2,count K+(j-count K),0,1,width K+(j-count K)⟩ u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hr:=block_runs diagonal program 135 n B x s diagonal_code hp hs (by change 135+6 ≤ B;omega)
    (phase_blocks_valid s).2.2.2.2 ((diagonal_peak h hj).trans hB)
  have hvp : (block diagonal s).pc=141 := by rw [block_pc,hp];rfl
  have hJ:=UniformRadixInstructionMachine.jump_runs program n B 123 x (block diagonal s) hr.final_bound
    (by omega) (by rw [hvp];rfl)
  exact ⟨{block diagonal s with pc:=123},hr.trans hJ,(h.block diagonal phase_blocks_keep.2.2.2.2.1).withPC,
    rfl,(diagonal_spec h).withPC,block_heap _ _⟩

theorem normalize_emit (n K d j B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K)
    (ht : s.natReg 419=(count K+width K)+count K) (hp : s.pc=142)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u,
    BoundedRuns program n x B s 11 u ∧ Context K d j u ∧ u.pc=123 ∧
    Fields ⟨2,width K+count K+outputAddress K ((width K-(j-((count K+width K)+count K)))%width K),0,0,width K⟩ u ∧
    u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hr:=block_runs normalize program 142 n B x s normalize_code hp hs (by change 142+10 ≤ B;omega)
    (normalize_valid h) ((normalize_peak h hj ht).trans hB)
  have hvp : (block normalize s).pc=152 := by rw [block_pc,hp];rfl
  have hJ:=UniformRadixInstructionMachine.jump_runs program n B 123 x (block normalize s) hr.final_bound
    (by omega) (by rw [hvp];rfl)
  exact ⟨{block normalize s with pc:=123},hr.trans hJ,(h.block normalize phase_blocks_keep.2.2.2.2.2).withPC,
    rfl,(normalize_spec h ht).withPC,block_heap _ _⟩

theorem forward_emit (n K d j B : ℕ) (hj : j<count K) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hp : s.pc=21) (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 19*K+62 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (rawRow (instruction K ⟨j,hj⟩)) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hr:=block_runs forwardSetup program 21 n B x s forwardSetup_code hp hs (by change 21+3 ≤ B;omega)
    (phase_blocks_valid s).1 (setup_peaks h hs hc).1
  have hvp : (block forwardSetup s).pc=24 := by rw [block_pc,hp];rfl
  have hJ:=UniformRadixInstructionMachine.jump_runs program n B 33 x (block forwardSetup s) hr.final_bound
    (by omega) (by rw [hvp];rfl)
  have hf:=forwardSetup_spec h
  obtain ⟨u,t,hu,ht,huc,hup,huf,hheap⟩:=fft_emit n K d j j B hj false x {block forwardSetup s with pc:=33}
    (h.block forwardSetup phase_blocks_keep.1).withPC hf.1 hf.2.1 hf.2.2 rfl hJ.final_bound hB
  exact ⟨u,3+1+t,(by simpa [forwardSetup,backwardSetup,←Nat.add_assoc] using hr.trans (hJ.trans hu)),by omega,huc,hup,by simpa [afterShift] using huf,
    hheap.trans (block_heap _ _)⟩

theorem backward_emit (n K d j B : ℕ) (hj : j-(count K+width K)<count K) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hp : s.pc=29) (ht : s.natReg 413=count K+width K)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 19*K+62 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (shift (width K+count K) (rawRow (instruction K ⟨j-(count K+width K),hj⟩))) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hr:=block_runs backwardSetup program 29 n B x s backwardSetup_code hp hs (by change 29+3 ≤ B;omega)
    (phase_blocks_valid s).2.1 (setup_peaks h hs hc).2
  have hvp : (block backwardSetup s).pc=32 := by rw [block_pc,hp];rfl
  have hJ:=UniformRadixInstructionMachine.jump_runs program n B 33 x (block backwardSetup s) hr.final_bound
    (by omega) (by rw [hvp];rfl)
  have hf:=backwardSetup_spec h ht
  obtain ⟨u,t,hu,htime,huc,hup,huf,hheap⟩:=fft_emit n K d j (j-(count K+width K)) B hj true x
    {block backwardSetup s with pc:=33} (h.block backwardSetup phase_blocks_keep.2.1).withPC
    hf.1 hf.2.1 hf.2.2 rfl hJ.final_bound hB
  exact ⟨u,3+1+t,(by simpa [forwardSetup,backwardSetup,←Nat.add_assoc] using hr.trans (hJ.trans hu)),by omega,huc,hup,by simpa [afterShift] using huf,
    hheap.trans (block_heap _ _)⟩



/-- The actual four-way dispatcher computes the next row without reading a graph tape. -/
theorem emit (n K d j B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K) (hp : s.pc=20)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 19*K+67 ∧ Context K d j u ∧ u.pc=123 ∧
    Fields (rowAt K j) u ∧ u.natHeap=s.natHeap := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hb:=UniformRadixInstructionMachine.branch_runs program n B 405 403 21 25 x s hs
    (by omega) (by omega) (by rw [hp];rfl)
  by_cases hF : j<count K
  · simp only [h.index,h.Greg,ite_eq_left hF] at hb
    obtain ⟨u,t,hu,ht,huc,hup,huf,hheap⟩:=forward_emit n K d j B hF x {s with pc:=21}
      h.withPC rfl hb.final_bound hB
    refine ⟨u,1+t,hb.trans hu,by omega,huc,hup,?_,hheap⟩
    simpa only [rowAt,hF,ite_true,UniformRadixInstructionMachine.decode_instruction K ⟨j,hF⟩] using huf
  · simp only [h.index,h.Greg,ite_eq_right hF] at hb
    let a : State := {s with pc:=25}
    have ha : Context K d j a := h.withPC
    have hr:=block_runs threshold program 25 n B x a threshold_code rfl hb.final_bound
      (by change 25+1 ≤ B;omega) (phase_blocks_valid a).2.2.1 ((threshold_peak ha).trans hB)
    let v:=block threshold a
    have hv : Context K d j v := ha.block threshold phase_blocks_keep.2.2.1
    have hvt : v.natReg 413=count K+width K := threshold_spec ha
    have hvp : v.pc=26 := by rw [block_pc];rfl
    have hd:=UniformRadixInstructionMachine.branch_runs program n B 405 413 135 27 x v hr.final_bound
      (by omega) (by omega) (by rw [hvp];rfl)
    by_cases hD : j<count K+width K
    · simp only [hv.index,hvt,ite_eq_left hD] at hd
      obtain ⟨u,hu,huc,hup,huf,hheap⟩:=diagonal_emit n K d j B x {v with pc:=135}
        hv.withPC hD rfl hd.final_bound hB
      refine ⟨u,1+1+1+7,(by simpa [threshold,←Nat.add_assoc] using hb.trans (hr.trans (hd.trans hu))),by omega,huc,hup,?_,hheap.trans (block_heap _ _)⟩
      simpa only [rowAt,hF,hD,ite_false,ite_true,outputAddress] using huf
    · simp only [hv.index,hvt,ite_eq_right hD] at hd
      let b : State := {v with pc:=27}
      have hbc : Context K d j b := hv.withPC
      have hbt : b.natReg 413=count K+width K := hvt
      have hR:=block_runs backwardThreshold program 27 n B x b backwardThreshold_code rfl hd.final_bound
        (by change 27+1 ≤ B;omega) (phase_blocks_valid b).2.2.2.1 ((backwardThreshold_peak hbc hbt).trans hB)
      let w:=block backwardThreshold b
      have hw : Context K d j w := hbc.block backwardThreshold phase_blocks_keep.2.2.2.1
      have hwt : w.natReg 419=(count K+width K)+count K := backwardThreshold_spec hbc hbt
      have hwp : w.pc=28 := by rw [block_pc];rfl
      have hw413 : w.natReg 413=count K+width K := by
        rw [block_keeps backwardThreshold b 413 (by simp [backwardThreshold,AOp.dst])];exact hbt
      have hBB:=UniformRadixInstructionMachine.branch_runs program n B 405 419 29 142 x w hR.final_bound
        (by omega) (by omega) (by rw [hwp];rfl)
      by_cases hBwd : j<(count K+width K)+count K
      · simp only [hw.index,hwt,ite_eq_left hBwd] at hBB
        have hJ : j-(count K+width K)<count K := by omega
        obtain ⟨u,t,hu,ht,huc,hup,huf,hheap⟩:=backward_emit n K d j B hJ x {w with pc:=29}
          hw.withPC rfl hw413 hBB.final_bound hB
        refine ⟨u,1+1+1+1+1+t,(by simpa [threshold,backwardThreshold,←Nat.add_assoc] using hb.trans (hr.trans (hd.trans (hR.trans (hBB.trans hu))))),by omega,
          huc,hup,?_,hheap.trans ((block_heap _ _).trans (block_heap _ _))⟩
        simpa only [rowAt,hF,hD,hBwd,ite_false,ite_true,
          UniformRadixInstructionMachine.decode_instruction K ⟨j-(count K+width K),hJ⟩] using huf
      · simp only [hw.index,hwt,ite_eq_right hBwd] at hBB
        obtain ⟨u,hu,huc,hup,huf,hheap⟩:=normalize_emit n K d j B x {w with pc:=142}
          hw.withPC hj hwt rfl hBB.final_bound hB
        refine ⟨u,1+1+1+1+1+11,(by simpa [threshold,backwardThreshold,←Nat.add_assoc] using hb.trans (hr.trans (hd.trans (hR.trans (hBB.trans hu))))),by omega,
          huc,hup,?_,hheap.trans ((block_heap _ _).trans (block_heap _ _))⟩
        simpa only [rowAt,hF,hD,hBwd,ite_false] using huf

/-- One actual iteration advances the printed prefix by one complete record. -/
theorem iteration (n K d j B : ℕ) (heap : ℕ → Option ℕ) (x : Fin n → ℂ) (s : State)
    (h : Context K d j s) (hj : j<UniformConvolutionDAG.total K) (hp : s.pc=19)
    (hs : WordBound B s) (hB : allocation K d ≤ B)
    (hprinted : Printed K d j s) (houtside : Outside d (5*UniformConvolutionDAG.total K) heap s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 19*K+80 ∧ Context K d (j+1) u ∧ u.pc=19 ∧
    Printed K d (j+1) u ∧ Outside d (5*UniformConvolutionDAG.total K) heap u := by
  have hc : 500 ≤ B := (allocation_code K d).trans hB
  have hb:=UniformRadixInstructionMachine.branch_runs program n B 405 404 20 153 x s hs
    (by omega) (by omega) (by rw [hp];rfl)
  simp only [h.index,h.total,ite_eq_left hj] at hb
  obtain ⟨v,t,hv,ht,hvc,hvp,hvf,hheap⟩:=emit n K d j B x {s with pc:=20} h.withPC hj rfl hb.final_bound hB
  have hvprinted : Printed K d j v := by simpa only [Printed,hheap] using hprinted
  have hvoutside : Outside d (5*UniformConvolutionDAG.total K) heap v := by simpa only [Outside,hheap] using houtside
  obtain ⟨u,hu,huc,hup,huprefix,huoutside⟩:=store_execution n K d j B heap x v hvc hj hvf hvp hv.final_bound hB hvprinted hvoutside
  exact ⟨u,1+t+12,(by simpa [←Nat.add_assoc] using hb.trans (hv.trans hu)),by omega,huc,hup,huprefix,huoutside⟩

/-- Prefix induction is over the actual fixed program, with all stores charged. -/
theorem print_loop (n K d B fuel : ℕ) (heap : ℕ → Option ℕ) (x : Fin n → ℂ) :
    ∀j s, j+fuel=UniformConvolutionDAG.total K → Context K d j s → s.pc=19 → WordBound B s → allocation K d ≤ B →
    Printed K d j s → Outside d (5*UniformConvolutionDAG.total K) heap s → ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ (19*K+80)*fuel+1 ∧ Context K d (UniformConvolutionDAG.total K) u ∧
    u.pc=153 ∧ Printed K d (UniformConvolutionDAG.total K) u ∧ Outside d (5*UniformConvolutionDAG.total K) heap u := by
  induction fuel with
  | zero=>
    intro j s hj h hp hs hB hprinted houtside
    have hje : j=UniformConvolutionDAG.total K := by omega
    subst j
    have hc : 500 ≤ B := (allocation_code K d).trans hB
    have hb:=UniformRadixInstructionMachine.branch_runs program n B 405 404 20 153 x s hs
      (by omega) (by omega) (by rw [hp];rfl)
    simp only [h.index,h.total,lt_self_iff_false,ite_false] at hb
    exact ⟨{s with pc:=153},1,hb,by simp,h.withPC,rfl,hprinted,houtside⟩
  | succ fuel ih=>
    intro j s hj h hp hs hB hprinted houtside
    have hjlt : j<UniformConvolutionDAG.total K := by omega
    obtain ⟨v,t,hv,ht,hvc,hvp,hvprefix,hvoutside⟩:=iteration n K d j B heap x s h hjlt hp hs hB hprinted houtside
    obtain ⟨u,w,hu,hw,huc,hup,huprefix,huoutside⟩:=ih (j+1) v (by omega) hvc hvp hv.final_bound hB hvprefix hvoutside
    exact ⟨u,t+w,hv.trans hu,by simpa [Nat.mul_succ] using (by omega : t+w ≤ (19*K+80)*fuel+(19*K+80)+1),
      huc,hup,huprefix,huoutside⟩



/-- Starting from just K, a destination base and an ordinary bounded state,
this one fixed program produces the entire actual convolution topology. -/
theorem execution (n K d B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hK : s.natReg 400=K) (hd : s.natReg 401=d)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 4*K+18+(19*K+80)*UniformConvolutionDAG.total K ∧
    u.pc=153 ∧ Context K d (UniformConvolutionDAG.total K) u ∧ Printed K d (UniformConvolutionDAG.total K) u ∧
    Outside d (5*UniformConvolutionDAG.total K) s.natHeap u ∧ Frame s u := by
  obtain ⟨v,hv,hvc,hvp,hheap⟩:=startup n K d B x s hK hd hp hs hB
  have hvprinted : Printed K d 0 v := by intro q hq;omega
  have hvoutside : Outside d (5*UniformConvolutionDAG.total K) s.natHeap v := by
    intro a ha;rw [hheap]
  obtain ⟨u,t,hu,ht,huc,hup,hprinted,houtside⟩:=print_loop n K d B (UniformConvolutionDAG.total K) s.natHeap x
    0 v (by omega) hvc hvp hv.final_bound hB hvprinted hvoutside
  have hhalt : BoundedExecution program n x B u 1 u := .halt hu.final_bound (by simp [step,hup];rfl)
  have hrun:=hv.executes (hu.executes hhalt)
  exact ⟨u,(4*K+16)+(t+1),hrun,by omega,hup,huc,hprinted,houtside,execution_frame hrun.executes⟩

/-- The public physical tape contract refers to the frozen typed instruction
itself; no supplied tape or coefficient-bank premise occurs. -/
def Tape (K d : ℕ) (s : State) : Prop := ∀q : Fin (UniformConvolutionDAG.total K),
  let r:=encode (UniformConvolutionDAG.instruction K q)
  s.natHeap (d+5*q.val)=some r.opcode ∧ s.natHeap (d+5*q.val+1)=some r.left ∧
  s.natHeap (d+5*q.val+2)=some r.right ∧ s.natHeap (d+5*q.val+3)=some r.kind ∧
  s.natHeap (d+5*q.val+4)=some r.payload

theorem printed_tape {K d : ℕ} {s : State} (h : Printed K d (UniformConvolutionDAG.total K) s) : Tape K d s := by
  intro q
  simpa only [rowAt_instruction] using h q q.isLt

theorem physical_execution (n K d B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hK : s.natReg 400=K) (hd : s.natReg 401=d)
    (hs : WordBound B s) (hB : allocation K d ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 4*K+18+(19*K+80)*UniformConvolutionDAG.total K ∧
    Tape K d u ∧ Outside d (5*UniformConvolutionDAG.total K) s.natHeap u ∧ Frame s u := by
  obtain ⟨u,t,hu,ht,_,_,hprinted,houtside,hframe⟩:=execution n K d B x s hp hK hd hs hB
  exact ⟨u,t,hu,ht,printed_tape hprinted,houtside,hframe⟩

theorem saved_headers {s u : State} (h : Frame s u) (i : ℕ) (hi : 100 ≤ i ∧ i ≤ 106) :
    u.natReg i=s.natReg i := h.2.2.2.2 i (by omega)

theorem record_count (K : ℕ) : (UniformConvolutionDAG.records K).length=3*K*2^K+2*2^K := by
  simpa only [width] using UniformConvolutionDAG.gate_count K

theorem printed_topological (K : ℕ) (q : Fin (UniformConvolutionDAG.total K)) (a : ℕ)
    (ha : a∈(UniformConvolutionDAG.instruction K q).refs) : a<width K+q.val :=
  UniformConvolutionDAG.printed_refs_before K q a ha

/-- A width-polynomial envelope for all intermediate integers and tape addresses. -/
theorem allocation_power (K d : ℕ) : allocation K d ≤ d+2^(4*K+14) := by
  have hlin:=UniformRadixInstructionMachine.cap_linear (width K) (count K) K
  have hc:=UniformRadixInstructionMachine.cap_power K
  have hn:=width_pos K
  have h500 : 500 ≤ UniformRadixInstructionMachine.cap (width K) (count K) K := by
    unfold UniformRadixInstructionMachine.cap
    nlinarith
  have htotal : 5*UniformConvolutionDAG.total K ≤ UniformRadixInstructionMachine.cap (width K) (count K) K := by
    unfold UniformConvolutionDAG.total;omega
  have hpow : 4*2^(4*K+12)=2^(4*K+14) := by
    rw [show 4*K+14=(4*K+12)+2 by omega,pow_add];ring
  unfold allocation
  rw [←hpow]
  omega



/-- Decode the exact five-field format. Rational scales use numerator one;
this is proved lossless for every actual convolution record below. -/
def decodeRow (K : ℕ) (r : Row) : UniformConvolutionDAG.Expr (width K+width K) ℕ :=
  if r.opcode=0 then .add r.left r.right
  else if r.opcode=1 then .sub r.left r.right
  else if r.kind=1 then .scale (.prepared ⟨r.payload%(width K+width K),Nat.mod_lt _ (by have h:=width_pos K;omega)⟩ false) r.left
  else .scale (.rational ((r.payload : ℚ)⁻¹)) r.left

theorem node_encoding_lossless (K : ℕ) (q : UniformConvolutionDAG.Node K) :
    decodeRow K (encode ((UniformConvolutionDAG.gate q).map UniformConvolutionDAG.address))=
      (UniformConvolutionDAG.gate q).map UniformConvolutionDAG.address := by
  cases q with
  | forward q | backward q=>
    cases hg : gate q with
    | add a b | sub a b=>simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,
        UniformConvolutionDAG.prepareOp,hg,encode,decodeRow]
    | scale c a=>
      have hc : c<width K := gate_scalar_bound q c (by rw [hg];simp [Op.scalars])
      have hcc : c<width K+width K := by have h:=width_pos K;omega
      simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,UniformConvolutionDAG.prepareOp,
        hg,UniformConvolutionDAG.powerCoefficient,hc,encode,decodeRow,Nat.mod_eq_of_lt hcc]
  | diagonal i=>
    have hilt:=i.isLt
    simp [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode,decodeRow,Fin.ext_iff,
      Nat.mod_eq_of_lt (show i.val+width K<width K+width K by omega)]
  | normalize i=>
    simp only [UniformConvolutionDAG.gate,UniformConvolutionDAG.Expr.map,encode,reciprocal_den]
    simp [decodeRow]

theorem instruction_encoding_lossless (K : ℕ) (q : Fin (UniformConvolutionDAG.total K)) :
    decodeRow K (encode (UniformConvolutionDAG.instruction K q))=UniformConvolutionDAG.instruction K q :=
  node_encoding_lossless K ((UniformConvolutionDAG.nodeFin K).symm q)

/-- In particular no sign bit or rational numerator is silently dropped on
this actual graph. Coefficient values/banks are still a separate preparation. -/
theorem records_encoding_lossless (K : ℕ) :
    ((UniformConvolutionDAG.records K).map encode).map (decodeRow K)=UniformConvolutionDAG.records K := by
  simp [UniformConvolutionDAG.records,List.map_map,Function.comp_def,instruction_encoding_lossless]



/-- Every emitted field is physically present, suitable for a later copier. -/
theorem tape_present {K d : ℕ} {s : State} (h : Tape K d s) :
    ∀i, i<5*UniformConvolutionDAG.total K → ∃v,s.natHeap (d+i)=some v := by
  intro i hi
  have hq : i/5<UniformConvolutionDAG.total K := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  have hr : i%5<5 := Nat.mod_lt _ (by omega)
  have he : i%5+5*(i/5)=i := Nat.mod_add_div i 5
  have ht:=h ⟨i/5,hq⟩
  simp only at ht
  interval_cases hrem : i%5
  · rw [show d+i=d+5*(i/5)+0 by omega]
    exact ⟨_,ht.1⟩
  · rw [show d+i=d+5*(i/5)+1 by omega]
    exact ⟨_,ht.2.1⟩
  · rw [show d+i=d+5*(i/5)+2 by omega]
    exact ⟨_,ht.2.2.1⟩
  · rw [show d+i=d+5*(i/5)+3 by omega]
    exact ⟨_,ht.2.2.2.1⟩
  · rw [show d+i=d+5*(i/5)+4 by omega]
    exact ⟨_,ht.2.2.2.2⟩

/-- The charged decoder-per-node implementation is polynomial in FFT width. -/
theorem runtime_width (K : ℕ) :
    4*K+18+(19*K+80)*UniformConvolutionDAG.total K ≤ 600*(width K)^3 := by
  have hn:=width_pos K
  have hk:=width_ge_height K
  have hc:=count_exact K
  have ht : UniformConvolutionDAG.total K ≤ 5*(width K)^2 := by
    unfold UniformConvolutionDAG.total;nlinarith
  have hcoef : 19*K+80 ≤ 99*width K := by omega
  have hprod:=Nat.mul_le_mul hcoef ht
  have hn2 : width K ≤ (width K)^2 := by nlinarith
  have hn3 : width K ≤ (width K)^3 := by nlinarith
  nlinarith

/-- Width-one includes both its diagonal and rational normalization records. -/
theorem zero_height_records : (UniformConvolutionDAG.records 0).map encode=
    [⟨2,0,0,1,1⟩,⟨2,1,0,0,1⟩] := by rw [←rowAt_records];decide

theorem one_height_count : (UniformConvolutionDAG.records 1).length=10 := by rw [record_count];decide

theorem two_height_count : (UniformConvolutionDAG.records 2).length=32 := by rw [record_count];decide

theorem one_height_last : rowAt 1 9=⟨2,9,0,0,2⟩ := by decide

theorem zero_division_guard (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=13) (hz : s.natReg 410=0) : step program n x s=.failed := by
  have hcode : program[s.pc]?=some (.natBinary .div 403 403 410) := by rw [hp];rfl
  simp [step,hcode,evalNat,hz]

theorem zero_modulus_guard (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=144) (hz : s.natReg 402=0) : step program n x s=.failed := by
  have hcode : program[s.pc]?=some (.natBinary .mod 413 413 402) := by rw [hp];rfl
  simp [step,hcode,evalNat,hz]

theorem small_word_rejected (s : State) : ¬WordBound 4 (writeNat s 412 5) := by
  intro h
  have hr:=h.2.1 412
  simp [writeNat] at hr

end

end ExactFourierCircuits.UniformConvolutionTopologyMachine
