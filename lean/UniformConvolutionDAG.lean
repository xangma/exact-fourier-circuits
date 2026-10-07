import UniformRadixTwoDAG
import UniformReplayPrint
import UniformCyclic

set_option autoImplicit false

/-! A computable, prepared-reference-only fixed-kernel convolution topology.
The spectrum of the fixed operand is a separately prepared bank; no scalar
zero test or additional root request changes the printed graph. The literal
zero port used by padding is a syntactic port, deleted by dirty replay. -/
namespace ExactFourierCircuits.UniformConvolutionDAG
open UniformRadixTwoDAG OAI.ExactFourier
open scoped BigOperators

inductive Expr (r : ℕ) (α : Type) where
  | add (left right : α)
  | sub (left right : α)
  | scale (coefficient : UniformReplayPrint.Coefficient r) (source : α)
  deriving Repr

def Expr.map {r : ℕ} {α β : Type} (f : α → β) : Expr r α → Expr r β
  | .add a b => .add (f a) (f b)
  | .sub a b => .sub (f a) (f b)
  | .scale c a => .scale c (f a)

def Expr.refs {r : ℕ} {α : Type} : Expr r α → List α
  | .add a b => [a,b]
  | .sub a b => [a,b]
  | .scale _ a => [a]

theorem Expr.refs_map {r : ℕ} {α β : Type} (f : α → β) (g : Expr r α) :
    (g.map f).refs = g.refs.map f := by cases g <;> rfl

def Expr.depth {r : ℕ} {α : Type} (d : α → ℕ) : Expr r α → ℕ
  | .add a b => max (d a) (d b)+1
  | .sub a b => max (d a) (d b)+1
  | .scale _ a => d a+1

def Expr.lower {r n : ℕ} (g : Expr r ℕ) (h : ∀ a ∈ g.refs, a < n) : UniformReplayPrint.Gate r n :=
  match g with
  | .add a b => .add ⟨a,h a (by simp [refs])⟩ ⟨b,h b (by simp [refs])⟩
  | .sub a b => .sub ⟨a,h a (by simp [refs])⟩ ⟨b,h b (by simp [refs])⟩
  | .scale c a => .scale c ⟨a,h a (by simp [refs])⟩

instance widthNeZero (k : ℕ) : NeZero (width k) := ⟨Nat.ne_of_gt (width_pos k)⟩

/-- Integer-only reversal of the Fourier output index. -/
def reverseIndex (k : ℕ) (i : Fin (width k)) : Fin (width k) :=
  ⟨(width k-i.val) % width k,Nat.mod_lt _ (width_pos k)⟩

theorem reverseIndex_involution (k : ℕ) (i : Fin (width k)) :
    reverseIndex k (reverseIndex k i) = i := by
  apply Fin.ext
  by_cases hi : i.val=0
  · simp [reverseIndex,hi]
  · have hlt : width k-i.val < width k := by omega
    have hpos : 0 < width k-i.val := by have := i.isLt; omega
    simp only [reverseIndex,Fin.val_mk,Nat.mod_eq_of_lt hlt]
    rw [Nat.sub_sub_self (Nat.le_of_lt i.isLt),Nat.mod_eq_of_lt i.isLt]

theorem reverseIndex_injective (k : ℕ) : Function.Injective (reverseIndex k) :=
  Function.LeftInverse.injective (reverseIndex_involution k)

/-- Two actual FFTs and two charged diagonal layers. -/
inductive Node (k : ℕ) where
  | forward (node : UniformRadixTwoDAG.Node k)
  | diagonal (index : Fin (width k))
  | backward (node : UniformRadixTwoDAG.Node k)
  | normalize (index : Fin (width k))

abbrev Ref (k : ℕ) := Fin (width k) ⊕ Node k

@[reducible] def total (k : ℕ) : ℕ := ((count k+width k)+count k)+width k

def splitNodes (k : ℕ) : Node k ≃
    ((UniformRadixTwoDAG.Node k ⊕ Fin (width k)) ⊕ UniformRadixTwoDAG.Node k) ⊕ Fin (width k) where
  toFun
    | .forward j => .inl (.inl (.inl j))
    | .diagonal i => .inl (.inl (.inr i))
    | .backward j => .inl (.inr j)
    | .normalize i => .inr i
  invFun
    | .inl (.inl (.inl j)) => .forward j
    | .inl (.inl (.inr i)) => .diagonal i
    | .inl (.inr j) => .backward j
    | .inr i => .normalize i
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with ((j|i)|j)|i <;> rfl

def nodeFin (k : ℕ) : Node k ≃ Fin (total k) :=
  (splitNodes k).trans
    ((Equiv.sumCongr
      ((Equiv.sumCongr
        ((Equiv.sumCongr (UniformRadixTwoDAG.nodeFin k) (Equiv.refl _)).trans finSumFinEquiv)
        (UniformRadixTwoDAG.nodeFin k)).trans finSumFinEquiv)
      (Equiv.refl _)).trans finSumFinEquiv)

@[simp] theorem nodeFin_forward {k : ℕ} (j : UniformRadixTwoDAG.Node k) :
    (nodeFin k (.forward j)).val = (UniformRadixTwoDAG.nodeFin k j).val := rfl
@[simp] theorem nodeFin_diagonal {k : ℕ} (i : Fin (width k)) :
    (nodeFin k (.diagonal i)).val = count k+i.val := rfl
@[simp] theorem nodeFin_backward {k : ℕ} (j : UniformRadixTwoDAG.Node k) :
    (nodeFin k (.backward j)).val = (count k+width k)+(UniformRadixTwoDAG.nodeFin k j).val := rfl
@[simp] theorem nodeFin_normalize {k : ℕ} (i : Fin (width k)) :
    (nodeFin k (.normalize i)).val = ((count k+width k)+count k)+i.val := rfl

def address {k : ℕ} : Ref k → ℕ
  | .inl i => i.val
  | .inr j => width k+(nodeFin k j).val

def forwardRef {k : ℕ} : UniformRadixTwoDAG.Ref k → Ref k
  | .inl i => .inl i
  | .inr j => .inr (.forward j)

def backwardRef {k : ℕ} : UniformRadixTwoDAG.Ref k → Ref k
  | .inl i => .inr (.diagonal i)
  | .inr j => .inr (.backward j)

/-- Coefficient slots0..N−1 are powers of the same supplied root. -/
def powerCoefficient (k c : ℕ) : UniformReplayPrint.Coefficient (width k+width k) :=
  if h : c < width k then .prepared (Fin.castAdd (width k) ⟨c,h⟩) false
  else .rational 0

def prepareOp {r : ℕ} {α : Type} (coeff : ℕ → UniformReplayPrint.Coefficient r) : Op α → Expr r α
  | .add a b => .add a b
  | .sub a b => .sub a b
  | .scale c a => .scale (coeff c) a

theorem prepareOp_refs {r : ℕ} {α : Type} (coeff : ℕ → UniformReplayPrint.Coefficient r)
    (g : Op α) : (prepareOp coeff g).refs = g.refs := by cases g <;> rfl

def gate {k : ℕ} : Node k → Expr (width k+width k) (Ref k)
  | .forward j => (prepareOp (powerCoefficient k) (UniformRadixTwoDAG.gate j)).map forwardRef
  | .diagonal i => .scale (.prepared (Fin.natAdd (width k) i) false)
      (forwardRef (output k i))
  | .backward j => (prepareOp (powerCoefficient k) (UniformRadixTwoDAG.gate j)).map backwardRef
  | .normalize i => .scale (.rational ((width k : ℚ)⁻¹)) (backwardRef (output k (reverseIndex k i)))

def instruction (k : ℕ) (j : Fin (total k)) : Expr (width k+width k) ℕ :=
  (gate ((nodeFin k).symm j)).map address

def records (k : ℕ) : List (Expr (width k+width k) ℕ) :=
  (List.finRange (total k)).map (instruction k)

theorem address_forward {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    address (forwardRef r) = UniformRadixTwoDAG.refNat r := by cases r <;> rfl

theorem forward_before {k : ℕ} (r : UniformRadixTwoDAG.Ref k)
    (j : UniformRadixTwoDAG.Node k)
    (h : UniformRadixTwoDAG.refNat r < width k+(UniformRadixTwoDAG.nodeFin k j).val) :
    address (forwardRef r) < width k+(nodeFin k (.forward j)).val := by
  simpa only [address_forward,nodeFin_forward] using h

theorem backward_before {k : ℕ} (r : UniformRadixTwoDAG.Ref k)
    (j : UniformRadixTwoDAG.Node k)
    (h : UniformRadixTwoDAG.refNat r < width k+(UniformRadixTwoDAG.nodeFin k j).val) :
    address (backwardRef r) < width k+(nodeFin k (.backward j)).val := by
  cases r with
  | inl i =>
    change width k+(count k+i.val) < width k+((count k+width k)+(UniformRadixTwoDAG.nodeFin k j).val)
    have := i.isLt; omega
  | inr a =>
    change width k+((count k+width k)+(UniformRadixTwoDAG.nodeFin k a).val) <
      width k+((count k+width k)+(UniformRadixTwoDAG.nodeFin k j).val)
    change width k+(UniformRadixTwoDAG.nodeFin k a).val < width k+(UniformRadixTwoDAG.nodeFin k j).val at h
    omega

theorem backward_bound {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    address (backwardRef r) < width k+((count k+width k)+count k) := by
  cases r with
  | inl i =>
    change width k+(count k+i.val) < width k+((count k+width k)+count k)
    have := i.isLt; omega
  | inr j =>
    change width k+((count k+width k)+(UniformRadixTwoDAG.nodeFin k j).val) < _
    have := (UniformRadixTwoDAG.nodeFin k j).isLt; omega

theorem gate_refs_before {k : ℕ} (j : Node k) (r : Ref k) (h : r ∈ (gate j).refs) :
    address r < width k+(nodeFin k j).val := by
  cases j with
  | forward j =>
    rw [gate,Expr.refs_map,prepareOp_refs,List.mem_map] at h
    obtain ⟨r,hr,rfl⟩ := h
    exact forward_before r j (UniformRadixTwoDAG.gate_refs_before j r hr)
  | diagonal i =>
    simp only [gate,Expr.refs,List.mem_singleton] at h
    subst r
    rw [address_forward,nodeFin_diagonal]
    have hb := refNat_bound (output k i)
    omega
  | backward j =>
    rw [gate,Expr.refs_map,prepareOp_refs,List.mem_map] at h
    obtain ⟨r,hr,rfl⟩ := h
    exact backward_before r j (UniformRadixTwoDAG.gate_refs_before j r hr)
  | normalize i =>
    simp only [gate,Expr.refs,List.mem_singleton] at h
    subst r
    have hb := backward_bound (output k (reverseIndex k i))
    rw [nodeFin_normalize]
    omega

theorem printed_refs_before (k : ℕ) (j : Fin (total k)) (a : ℕ)
    (h : a ∈ (instruction k j).refs) : a < width k+j.val := by
  rw [instruction,Expr.refs_map,List.mem_map] at h
  obtain ⟨r,hr,rfl⟩ := h
  simpa using gate_refs_before ((nodeFin k).symm j) r hr

@[simp] theorem records_length (k : ℕ) : (records k).length = total k := by simp [records]

theorem gate_count (k : ℕ) : (records k).length = 3*k*2^k+2*2^k := by
  rw [records_length]
  have hc := count_exact k
  unfold total
  rw [width_eq] at *
  omega


/-- Rebase an input port and skip the distinguished literal-zero slot before
all generated registers. The map depends only on integer indices. -/
def wireAddress {N : ℕ} (n : ℕ) (f : Fin N → Fin (n+1)) (a : ℕ) : ℕ :=
  if h : a < N then (f ⟨a,h⟩).val else n+1+(a-N)

theorem wireAddress_lt {N : ℕ} (n t : ℕ) (f : Fin N → Fin (n+1)) (a : ℕ)
    (h : a < N+t) : wireAddress n f a < n+1+t := by
  unfold wireAddress
  split
  · rename_i ha
    have := (f ⟨a,ha⟩).isLt; omega
  · omega

def typedIndex {N : ℕ} (n t : ℕ) (f : Fin N → Fin (n+1)) (a : ℕ)
    (h : a < N+t) : Fin (n+1+t) := ⟨wireAddress n f a,wireAddress_lt n t f a h⟩

theorem typedIndex_castSucc {N : ℕ} (n t : ℕ) (f : Fin N → Fin (n+1)) (a : ℕ)
    (h : a < N+t) (h' : a < N+(t+1)) :
    typedIndex n (t+1) f a h' = (typedIndex n t f a h).castSucc := rfl

theorem typedIndex_last {N : ℕ} (n t : ℕ) (f : Fin N → Fin (n+1)) :
    typedIndex n (t+1) f (N+t) (by omega) = Fin.last (n+1+t) := by
  apply Fin.ext
  simp [typedIndex,wireAddress,show ¬N+t<N by omega]

theorem typedIndex_initial {N : ℕ} (n : ℕ) (f : Fin N → Fin (n+1)) (i : Fin N) :
    typedIndex n 0 f i.val (by omega) = f i := by
  apply Fin.ext
  simp [typedIndex,wireAddress,i.isLt]

def loweredGate (k n : ℕ) (f : Fin (width k) → Fin (n+1)) (j : Fin (total k)) :
    UniformReplayPrint.Gate (width k+width k) (n+1+j.val) :=
  ((instruction k j).map (wireAddress n f)).lower (by
    intro a ha
    rw [Expr.refs_map,List.mem_map] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    exact wireAddress_lt n j.val f a (printed_refs_before k j a ha))

/-- Typed prior-register references for the exact printed record prefix. -/
def programPrefix (k n : ℕ) (f : Fin (width k) → Fin (n+1)) :
    (t : ℕ) → t ≤ total k → UniformReplayPrint.Program (width k+width k) n t
  | 0, _ => .nil
  | t+1,h => .step (programPrefix k n f t (by omega)) (loweredGate k n f ⟨t,by omega⟩)

def program (k n : ℕ) (f : Fin (width k) → Fin (n+1)) :
    UniformReplayPrint.Program (width k+width k) n (total k) :=
  programPrefix k n f (total k) (le_refl _)

def outputIndex (k n : ℕ) (i : Fin (width k)) :
    Fin (n+1+total k) :=
  ⟨n+1+(nodeFin k (.normalize i)).val,by have := (nodeFin k (.normalize i)).isLt; omega⟩

def padInputs (k n : ℕ) (i : Fin (width k)) : Fin (n+1) :=
  if h : i.val < n then ⟨i.val,by omega⟩ else Fin.last n

def cyclicProgram (k : ℕ) : UniformReplayPrint.Program (width k+width k) (width k) (total k) :=
  program k (width k) (fun i => i.castSucc)

def paddedProgram (k n : ℕ) : UniformReplayPrint.Program (width k+width k) n (total k) :=
  program k n (padInputs k n)

theorem Expr.depth_map {r : ℕ} {α β : Type} (f : α → β) (g : Expr r α) (d : β → ℕ) :
    (g.map f).depth d = g.depth (d ∘ f) := by cases g <;> rfl

theorem prepareOp_depth {r : ℕ} {α : Type} (coeff : ℕ → UniformReplayPrint.Coefficient r)
    (g : Op α) (d : α → ℕ) : (prepareOp coeff g).depth d = g.depth d := by cases g <;> rfl

theorem Op.depth_shift {α : Type} (g : Op α) (d : α → ℕ) (a : ℕ) :
    g.depth (fun r => a+d r) = a+g.depth d := by
  cases g <;> simp [Op.depth,Nat.add_max_add_left,Nat.add_assoc]

/-- Exact longest-path labels for the full logical convolution graph.
Padding and deletion of phantom-zero reads preserve its upper bound. -/
def depth {k : ℕ} : Ref k → ℕ
  | .inl _ => 0
  | .inr (.forward j) => UniformRadixTwoDAG.depth (.inr j)
  | .inr (.diagonal _) => 2*k+1
  | .inr (.backward j) => (2*k+1)+UniformRadixTwoDAG.depth (.inr j)
  | .inr (.normalize _) => 4*k+2

theorem depth_forward {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    depth (forwardRef r) = UniformRadixTwoDAG.depth r := by
  cases r with
  | inl i => exact (depth_input k i).symm
  | inr j => rfl

theorem depth_backward {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    depth (backwardRef r) = (2*k+1)+UniformRadixTwoDAG.depth r := by
  cases r with
  | inl i => simp [backwardRef,depth,depth_input]
  | inr j => rfl

theorem depth_gate {k : ℕ} (j : Node k) : depth (.inr j) = (gate j).depth depth := by
  cases j with
  | forward j =>
    rw [gate,Expr.depth_map,prepareOp_depth]
    have hd : (@depth k ∘ @forwardRef k) = @UniformRadixTwoDAG.depth k := by
      funext r; exact depth_forward r
    rw [hd]
    exact UniformRadixTwoDAG.depth_gate j
  | diagonal i =>
    change 2*k+1 = depth (forwardRef (output k i))+1
    rw [depth_forward (output k i),output_depth]
  | backward j =>
    rw [gate,Expr.depth_map,prepareOp_depth]
    have hd : (@depth k ∘ @backwardRef k) = fun r => (2*k+1)+UniformRadixTwoDAG.depth r := by
      funext r; exact depth_backward r
    rw [hd,Op.depth_shift,← UniformRadixTwoDAG.depth_gate]
    rfl
  | normalize i =>
    change 4*k+2 = depth (backwardRef (output k (reverseIndex k i)))+1
    rw [depth_backward (output k (reverseIndex k i)),output_depth]
    omega

theorem depth_bound {k : ℕ} (r : Ref k) : depth r ≤ 4*k+2 := by
  cases r with
  | inl i => exact Nat.zero_le _
  | inr j => cases j with
    | forward j => have hd := UniformRadixTwoDAG.depth_bound k (.inr j); change UniformRadixTwoDAG.depth (.inr j) ≤ 4*k+2; omega
    | diagonal i => change 2*k+1≤4*k+2; omega
    | backward j => have hd := UniformRadixTwoDAG.depth_bound k (.inr j); change (2*k+1)+_≤_; omega
    | normalize i => exact le_refl _

theorem depth_exact (k : ℕ) : (∀ r : Ref k, depth r ≤ 4*k+2) ∧ ∃ r : Ref k, depth r=4*k+2 :=
  ⟨depth_bound,⟨.inr (.normalize ⟨0,width_pos k⟩),rfl⟩⟩

theorem forwardRef_injective (k : ℕ) : Function.Injective (@forwardRef k) := by
  intro r s h
  cases r <;> cases s <;> simp_all [forwardRef]

theorem backwardRef_injective (k : ℕ) : Function.Injective (@backwardRef k) := by
  intro r s h
  cases r <;> cases s <;> simp_all [backwardRef]

@[simp] theorem forwardRef_eq {k : ℕ} (r s : UniformRadixTwoDAG.Ref k) :
    forwardRef r=forwardRef s ↔ r=s := (forwardRef_injective k).eq_iff
@[simp] theorem backwardRef_eq {k : ℕ} (r s : UniformRadixTwoDAG.Ref k) :
    backwardRef r=backwardRef s ↔ r=s := (backwardRef_injective k).eq_iff
@[simp] theorem forwardRef_ne_backwardRef {k : ℕ} (r s : UniformRadixTwoDAG.Ref k) :
    forwardRef r≠backwardRef s := by cases r <;> cases s <;> simp [forwardRef,backwardRef]
@[simp] theorem backwardRef_ne_forwardRef {k : ℕ} (r s : UniformRadixTwoDAG.Ref k) :
    backwardRef r≠forwardRef s := (forwardRef_ne_backwardRef s r).symm
@[simp] theorem forwardRef_ne_normalize {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    forwardRef r≠.inr (.normalize i) := by cases r <;> simp [forwardRef]
@[simp] theorem backwardRef_ne_normalize {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    backwardRef r≠.inr (.normalize i) := by cases r <;> simp [backwardRef]

/-- Terminal ports are consumed by the next actual diagonal/normalization gate,
replacing (rather than adding to) their original FFT output use. -/
def frontSuccessors {k : ℕ} (r : UniformRadixTwoDAG.Ref k) : List (Node k) :=
  match UniformRadixTwoDAG.outputIndex k r with
  | some i => [.diagonal i]
  | none => (UniformRadixTwoDAG.successors k r).map Node.forward

def backSuccessors {k : ℕ} (r : UniformRadixTwoDAG.Ref k) : List (Node k) :=
  match UniformRadixTwoDAG.outputIndex k r with
  | some i => [.normalize (reverseIndex k i)]
  | none => (UniformRadixTwoDAG.successors k r).map Node.backward

def successors {k : ℕ} : Ref k → List (Node k)
  | .inl i => frontSuccessors (.inl i)
  | .inr (.forward j) => frontSuccessors (.inr j)
  | .inr (.diagonal i) => backSuccessors (.inl i)
  | .inr (.backward j) => backSuccessors (.inr j)
  | .inr (.normalize _) => []

theorem successors_forward {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    successors (forwardRef r) = frontSuccessors r := by cases r <;> rfl

theorem successors_backward {k : ℕ} (r : UniformRadixTwoDAG.Ref k) :
    successors (backwardRef r) = backSuccessors r := by cases r <;> rfl

theorem front_forward_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (j : UniformRadixTwoDAG.Node k) :
    .forward j ∈ frontSuccessors r ↔ j ∈ UniformRadixTwoDAG.successors k r := by
  cases h : UniformRadixTwoDAG.outputIndex k r with
  | none => simp [frontSuccessors,h,List.mem_map]
  | some i =>
    have hr := (UniformRadixTwoDAG.outputIndex_some k r i).mp h
    rw [hr,UniformRadixTwoDAG.successors_terminal]
    simp [frontSuccessors,← hr,h]

theorem front_diagonal_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    .diagonal i ∈ frontSuccessors r ↔ r=output k i := by
  cases h : UniformRadixTwoDAG.outputIndex k r with
  | none =>
    have hn : r≠output k i := by
      intro hr
      have hs := (UniformRadixTwoDAG.outputIndex_some k r i).mpr hr
      rw [h] at hs
      cases hs
    simp [frontSuccessors,h,List.mem_map,hn]
  | some j =>
    rw [← UniformRadixTwoDAG.outputIndex_some k r i,h]
    simp [frontSuccessors,h,eq_comm]

theorem front_backward_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (j : UniformRadixTwoDAG.Node k) :
    .backward j ∉ frontSuccessors r := by
  cases h : UniformRadixTwoDAG.outputIndex k r <;> simp [frontSuccessors,h,List.mem_map]

theorem front_normalize_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    .normalize i ∉ frontSuccessors r := by
  cases h : UniformRadixTwoDAG.outputIndex k r <;> simp [frontSuccessors,h,List.mem_map]

theorem back_backward_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (j : UniformRadixTwoDAG.Node k) :
    .backward j ∈ backSuccessors r ↔ j ∈ UniformRadixTwoDAG.successors k r := by
  cases h : UniformRadixTwoDAG.outputIndex k r with
  | none => simp [backSuccessors,h,List.mem_map]
  | some i =>
    have hr := (UniformRadixTwoDAG.outputIndex_some k r i).mp h
    rw [hr,UniformRadixTwoDAG.successors_terminal]
    simp [backSuccessors,← hr,h]

theorem reverseIndex_eq {k : ℕ} (i j : Fin (width k)) : reverseIndex k i=j ↔ i=reverseIndex k j := by
  constructor
  · intro h
    calc i = reverseIndex k (reverseIndex k i) := (reverseIndex_involution k i).symm
      _ = reverseIndex k j := congrArg (reverseIndex k) h
  · intro h
    rw [h,reverseIndex_involution]

theorem back_normalize_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    .normalize i ∈ backSuccessors r ↔ r=output k (reverseIndex k i) := by
  cases h : UniformRadixTwoDAG.outputIndex k r with
  | none =>
    have hn : r≠output k (reverseIndex k i) := by
      intro hr
      have hs := (UniformRadixTwoDAG.outputIndex_some k r (reverseIndex k i)).mpr hr
      rw [h] at hs
      cases hs
    simp [backSuccessors,h,List.mem_map,hn]
  | some j =>
    rw [← UniformRadixTwoDAG.outputIndex_some k r (reverseIndex k i),h]
    simp only [backSuccessors,h,List.mem_singleton,Node.normalize.injEq,Option.some.injEq]
    exact (eq_comm : i=reverseIndex k j ↔ reverseIndex k j=i).trans (reverseIndex_eq j i)

theorem back_forward_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (j : UniformRadixTwoDAG.Node k) :
    .forward j ∉ backSuccessors r := by
  cases h : UniformRadixTwoDAG.outputIndex k r <;> simp [backSuccessors,h,List.mem_map]

theorem back_diagonal_mem {k : ℕ} (r : UniformRadixTwoDAG.Ref k) (i : Fin (width k)) :
    .diagonal i ∉ backSuccessors r := by
  cases h : UniformRadixTwoDAG.outputIndex k r <;> simp [backSuccessors,h,List.mem_map]

theorem Expr.mem_refs_map {r : ℕ} {α β : Type} (f : α → β) (hf : Function.Injective f)
    (g : Expr r α) (a : α) : f a ∈ (g.map f).refs ↔ a ∈ g.refs := by
  rw [refs_map,List.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    exact (hf he) ▸ hb
  · intro h
    exact ⟨a,h,rfl⟩

theorem ref_cases {k : ℕ} (r : Ref k) :
    (∃ s, r=forwardRef s) ∨ (∃ s, r=backwardRef s) ∨ ∃ i, r=.inr (.normalize i) := by
  cases r with
  | inl i => exact .inl ⟨.inl i,rfl⟩
  | inr j => cases j with
    | forward j => exact .inl ⟨.inr j,rfl⟩
    | diagonal i => exact .inr (.inl ⟨.inl i,rfl⟩)
    | backward j => exact .inr (.inl ⟨.inr j,rfl⟩)
    | normalize i => exact .inr (.inr ⟨i,rfl⟩)

/-- Exact adjacency of the same literal gate expressions consumed by the typed
compiler, rather than a sampled or merely upper-bounding successor list. -/
theorem successors_spec {k : ℕ} (r : Ref k) (j : Node k) :
    j ∈ successors r ↔ r ∈ (gate j).refs := by
  rcases ref_cases r with ⟨r,rfl⟩|⟨r,rfl⟩|⟨i,rfl⟩
  · rw [successors_forward]
    cases j with
    | forward j =>
      rw [front_forward_mem,UniformRadixTwoDAG.successors_spec,gate,
        Expr.mem_refs_map forwardRef (forwardRef_injective k),prepareOp_refs]
    | diagonal i => simp [front_diagonal_mem,gate,Expr.refs]
    | backward j =>
      simp only [front_backward_mem,gate,Expr.refs_map,prepareOp_refs,List.mem_map]
      simp
    | normalize i => simp [front_normalize_mem,gate,Expr.refs]
  · rw [successors_backward]
    cases j with
    | forward j =>
      simp only [back_forward_mem,gate,Expr.refs_map,prepareOp_refs,List.mem_map]
      simp
    | diagonal i => simp [back_diagonal_mem,gate,Expr.refs]
    | backward j =>
      rw [back_backward_mem,UniformRadixTwoDAG.successors_spec,gate,
        Expr.mem_refs_map backwardRef (backwardRef_injective k),prepareOp_refs]
    | normalize i => simp [back_normalize_mem,gate,Expr.refs]
  · cases j with
    | forward j =>
      simp only [successors,List.not_mem_nil,gate,Expr.refs_map,prepareOp_refs,List.mem_map]
      simp
    | diagonal j => simp [successors,gate,Expr.refs,(forwardRef_ne_normalize _ _).symm]
    | backward j =>
      simp only [successors,List.not_mem_nil,gate,Expr.refs_map,prepareOp_refs,List.mem_map]
      simp
    | normalize j => simp [successors,gate,Expr.refs,(backwardRef_ne_normalize _ _).symm]

theorem successors_bound {k : ℕ} (r : Ref k) : (successors r).length ≤ 2 := by
  rcases ref_cases r with ⟨r,rfl⟩|⟨r,rfl⟩|⟨i,rfl⟩
  · rw [successors_forward]
    cases h : UniformRadixTwoDAG.outputIndex k r with
    | none => simpa [frontSuccessors,h] using UniformRadixTwoDAG.successors_bound k r
    | some i => simp [frontSuccessors,h]
  · rw [successors_backward]
    cases h : UniformRadixTwoDAG.outputIndex k r with
    | none => simpa [backSuccessors,h] using UniformRadixTwoDAG.successors_bound k r
    | some i => simp [backSuccessors,h]
  · simp [successors]

theorem successors_nodup {k : ℕ} (r : Ref k) : (successors r).Nodup := by
  rcases ref_cases r with ⟨r,rfl⟩|⟨r,rfl⟩|⟨i,rfl⟩
  · rw [successors_forward]
    cases h : UniformRadixTwoDAG.outputIndex k r with
    | none =>
      simpa [frontSuccessors,h] using (UniformRadixTwoDAG.successors_nodup k r).map (fun _ _ h => Node.forward.inj h)
    | some i => simp [frontSuccessors,h]
  · rw [successors_backward]
    cases h : UniformRadixTwoDAG.outputIndex k r with
    | none =>
      simpa [backSuccessors,h] using (UniformRadixTwoDAG.successors_nodup k r).map (fun _ _ h => Node.backward.inj h)
    | some i => simp [backSuccessors,h]
  · simp [successors]

theorem gate_refs_nodup {k : ℕ} (j : Node k) : (gate j).refs.Nodup := by
  cases j with
  | forward j =>
    rw [gate,Expr.refs_map,prepareOp_refs]
    exact (UniformRadixTwoDAG.gate_refs_nodup j).map (forwardRef_injective k)
  | diagonal i => simp [gate,Expr.refs]
  | backward j =>
    rw [gate,Expr.refs_map,prepareOp_refs]
    exact (UniformRadixTwoDAG.gate_refs_nodup j).map (backwardRef_injective k)
  | normalize i => simp [gate,Expr.refs]

def outputUses {k : ℕ} : Ref k → ℕ
  | .inr (.normalize _) => 1
  | _ => 0

def fanout {k : ℕ} (r : Ref k) : ℕ := (successors r).length+outputUses r

/-- Every actual input/node port has at most two indexed gate/output uses.
Prepared coefficient-bank reuse is separate from this data-port degree. -/
theorem fanout_bound {k : ℕ} (r : Ref k) : fanout r ≤ 2 := by
  rcases ref_cases r with ⟨r,rfl⟩|⟨r,rfl⟩|⟨i,rfl⟩
  · have hb := successors_bound (forwardRef r)
    cases r <;> simpa [fanout,forwardRef,outputUses] using hb
  · have hb := successors_bound (backwardRef r)
    cases r <;> simpa [fanout,backwardRef,outputUses] using hb
  · simp [fanout,successors,outputUses]

def physicalEmbedding (k n : ℕ) (hn : n ≤ width k) : Fin n ⊕ Node k → Ref k
  | .inl i => .inl ⟨i.val,i.isLt.trans_le hn⟩
  | .inr j => .inr j

/-- Physical replay coordinates contain actual inputs and gates, and no zero
register. Padding input ports outside n disappear in sourceMap below. -/
def physicalSuccessors (k n : ℕ) (hn : n ≤ width k) (p : Fin n ⊕ Node k) : List (Node k) :=
  successors (physicalEmbedding k n hn p)

def physicalOutputUses (k m : ℕ) : Node k → ℕ
  | .normalize i => if i.val < m then 1 else 0
  | _ => 0

def physicalFanout (k n m : ℕ) (hn : n ≤ width k) (p : Fin n ⊕ Node k) : ℕ :=
  (physicalSuccessors k n hn p).length+
    (match p with | .inl _ => 0 | .inr j => physicalOutputUses k m j)

theorem physicalSuccessors_spec (k n : ℕ) (hn : n ≤ width k) (p : Fin n ⊕ Node k) (j : Node k) :
    j ∈ physicalSuccessors k n hn p ↔ physicalEmbedding k n hn p ∈ (gate j).refs :=
  successors_spec _ _

theorem physicalFanout_bound (k n m : ℕ) (hn : n ≤ width k) (p : Fin n ⊕ Node k) :
    physicalFanout k n m hn p ≤ 2 := by
  have hb := fanout_bound (physicalEmbedding k n hn p)
  cases p with
  | inl i => simpa [physicalFanout,physicalSuccessors,physicalEmbedding,fanout,outputUses] using hb
  | inr j => cases j with
    | forward j => simpa [physicalFanout,physicalSuccessors,physicalEmbedding,physicalOutputUses,fanout,outputUses] using hb
    | diagonal i => simpa [physicalFanout,physicalSuccessors,physicalEmbedding,physicalOutputUses,fanout,outputUses] using hb
    | backward j => simpa [physicalFanout,physicalSuccessors,physicalEmbedding,physicalOutputUses,fanout,outputUses] using hb
    | normalize i => simp [physicalFanout,physicalSuccessors,physicalEmbedding,physicalOutputUses,successors]; split_ifs <;> omega

/-- The exact input/gate reference map used by dirty sweep, using all already
printed gate coordinates. Its result type contains no phantom zero. -/
def sourceMap (k n t : ℕ) (ht : t ≤ total k) : Fin (n+1+t) → Option (Fin n ⊕ Node k) :=
  referenceMap true Sum.inl (fun j : Fin t => Sum.inr ((nodeFin k).symm ⟨j.val,by have := j.isLt; omega⟩))

theorem sourceMap_padding (k n t : ℕ) (ht : t ≤ total k) (i : Fin (width k)) :
    sourceMap k n t ht (typedIndex n t (padInputs k n) i.val (by have := i.isLt; omega)) =
      if h : i.val<n then some (.inl ⟨i.val,h⟩) else none := by
  have he : typedIndex n t (padInputs k n) i.val (by have := i.isLt; omega) =
      Fin.castAdd t (padInputs k n i) := by
    apply Fin.ext
    simp [typedIndex,wireAddress,i.isLt]
  rw [he,sourceMap,referenceMap,Fin.addCases_left]
  by_cases hi : i.val<n
  · rw [padInputs,dite_eq_left hi]
    change (Fin.snoc (fun j : Fin n => some (.inl j : Fin n ⊕ Node k))
      (none : Option (Fin n ⊕ Node k)) : Fin (n+1) → Option (Fin n ⊕ Node k))
      (⟨i.val,hi⟩ : Fin n).castSucc = _
    rw [Fin.snoc_castSucc]
    simp [hi]
  · rw [padInputs,dite_eq_right hi,Fin.snoc_last]
    simp [hi]

theorem sourceMap_node (k n t : ℕ) (ht : t ≤ total k) (j : Node k) (hj : (nodeFin k j).val<t) :
    sourceMap k n t ht (typedIndex n t (padInputs k n) (address (.inr j))
      (by change width k+(nodeFin k j).val<width k+t; omega)) = some (.inr j) := by
  have he : typedIndex n t (padInputs k n) (address (.inr j))
      (by change width k+(nodeFin k j).val<width k+t; omega) =
      Fin.natAdd (n+1) (⟨(nodeFin k j).val,hj⟩ : Fin t) := by
    apply Fin.ext
    simp [typedIndex,wireAddress,address]
  rw [he,sourceMap,referenceMap,Fin.addCases_right]
  change some (Sum.inr ((nodeFin k).symm (nodeFin k j)) : Fin n ⊕ Node k) = _
  rw [Equiv.symm_apply_apply]

/-- A material printer bridge: all padding reads of the distinguished zero are
literally deleted, not wired to an actual high-fanout borrowed register. -/
theorem padding_zero_removed (k n t : ℕ) (ht : t ≤ total k) (i : Fin (width k)) (hi : n ≤ i.val) :
    sourceMap k n t ht (typedIndex n t (padInputs k n) i.val (by have := i.isLt; omega)) = none := by
  rw [sourceMap_padding,dite_eq_right (by omega : ¬i.val<n)]

theorem reference_empty_of_none {ι : Type} {r : ℕ} (dst : ι) (ref : Option ι)
    (c : UniformReplayPrint.Coefficient r) (h : ∀ p, ref=some p → dst≠p)
    (hz : ref=none) : UniformReplayPrint.reference dst ref c h = [] := by
  subst ref
  rfl

theorem padding_zero_reference_empty (k n t : ℕ) (ht : t ≤ total k) (i : Fin (width k))
    (hi : n ≤ i.val) (dst : Fin n ⊕ Node k) (c : UniformReplayPrint.Coefficient (width k+width k))
    (h : ∀ p, sourceMap k n t ht (typedIndex n t (padInputs k n) i.val
      (by have := i.isLt; omega)) = some p → dst≠p) :
    UniformReplayPrint.reference dst
      (sourceMap k n t ht (typedIndex n t (padInputs k n) i.val (by have := i.isLt; omega))) c h = [] := by
  exact reference_empty_of_none dst _ c h (padding_zero_removed k n t ht i hi)

theorem Expr.depth_refs {r : ℕ} {α : Type} (g : Expr r α) (d : α → ℕ) (a : α)
    (h : a ∈ g.refs) : d a < g.depth d := by
  cases g with
  | add b c =>
    simp only [refs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact (Nat.le_max_left _ _).trans_lt (Nat.lt_succ_self _)
    · exact (Nat.le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  | sub b c =>
    simp only [refs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact (Nat.le_max_left _ _).trans_lt (Nat.lt_succ_self _)
    · exact (Nat.le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  | scale c b =>
    simp only [refs,List.mem_singleton] at h
    subst a
    exact Nat.lt_succ_self _

theorem gate_levels {k : ℕ} (j : Node k) (r : Ref k) (h : r ∈ (gate j).refs) :
    depth r < depth (.inr j) := by
  rw [depth_gate]
  exact Expr.depth_refs (gate j) depth r h

theorem typed_address_power_bound (k n : ℕ) (hn : n ≤ width k) (i : Fin (n+1+total k)) :
    i.val < 2^(2*k+4) := by
  have hr := register_bound k
  have hw := width_pos k
  have hsize : n+1+total k ≤ 16*(width k)^2 := by
    unfold total
    nlinarith
  have he : 16*(width k)^2 = 2^(2*k+4) := by
    rw [width_eq,pow_add,show 2*k=k*2 by omega,pow_mul]
    norm_num
    ring
  exact i.isLt.trans_le (hsize.trans_eq he)

def fftProgram (k n : ℕ) (f : Fin (width k) → Fin (n+1)) :
    UniformReplayPrint.Program (width k+width k) n (count k) :=
  programPrefix k n f (count k) (by unfold total; omega)

def fftOutputIndex (k n : ℕ) (f : Fin (width k) → Fin (n+1)) (i : Fin (width k)) :
    Fin (n+1+count k) := typedIndex n (count k) f (UniformRadixTwoDAG.refNat (output k i))
      (refNat_bound (output k i))

theorem Expr.map_map {r : ℕ} {α β γ : Type} (f : α → β) (h : β → γ) (g : Expr r α) :
    (g.map f).map h = g.map (h ∘ f) := by cases g <;> rfl

theorem prepareOp_map {r : ℕ} {α β : Type} (coeff : ℕ → UniformReplayPrint.Coefficient r)
    (f : α → β) (g : Op α) : prepareOp coeff (g.map f) = (prepareOp coeff g).map f := by
  cases g <;> rfl

/-- The first literal convolution record block is exactly the frozen FFT
printer, with only the scalar slots lowered to prepared coefficient refs. -/
theorem first_fft_instruction (k : ℕ) (j : Fin (count k)) :
    instruction k ⟨j.val,by have := j.isLt; unfold total; omega⟩ =
      prepareOp (powerCoefficient k) (UniformRadixTwoDAG.instruction k j) := by
  have hi : (nodeFin k).symm ⟨j.val,by have := j.isLt; unfold total; omega⟩ =
      .forward ((UniformRadixTwoDAG.nodeFin k).symm j) := by
    apply (nodeFin k).injective
    apply Fin.ext
    simp
  rw [instruction,hi,gate,Expr.map_map]
  have hf : (@address k ∘ @forwardRef k) = @UniformRadixTwoDAG.refNat k := by
    funext r; exact address_forward r
  rw [hf,← prepareOp_map]
  rfl

/-- A complete prepared-reference replay printer for a padded/truncated kernel
convolution. Its zero input port is deleted by the reference bridge above. -/
def convolutionReplay (k n m : ℕ) (hm : m ≤ width k) :
    List (UniformReplayPrint.ShearCode ((Fin n ⊕ Fin (total k)) ⊕ Fin m) (width k+width k)) :=
  UniformReplayPrint.replayCode (paddedProgram k n)
    (fun i : Fin m => outputIndex k n ⟨i.val,i.isLt.trans_le hm⟩)

theorem convolutionReplay_length (k n m : ℕ) (hm : m ≤ width k) :
    (convolutionReplay k n m hm).length ≤ 8*(3*k*2^k+2*2^k)+2*m := by
  have h := UniformReplayPrint.replayCode_length (paddedProgram k n)
    (fun i : Fin m => outputIndex k n ⟨i.val,i.isLt.trans_le hm⟩)
  have ht : total k=3*k*2^k+2*2^k := (records_length k).symm.trans (gate_count k)
  simpa [convolutionReplay,ht] using h

noncomputable section

noncomputable def Expr.eval {r : ℕ} {α : Type} (bank : Fin r → ℂ) (v : α → ℂ) : Expr r α → ℂ
  | .add a b => v a+v b
  | .sub a b => v a-v b
  | .scale c a => c.eval bank*v a

theorem Expr.eval_map {r : ℕ} {α β : Type} (bank : Fin r → ℂ) (v : β → ℂ)
    (f : α → β) (g : Expr r α) : (g.map f).eval bank v = g.eval bank (v ∘ f) := by
  cases g <;> rfl

theorem Expr.eval_congr {r : ℕ} {α : Type} (bank : Fin r → ℂ) (v w : α → ℂ)
    (g : Expr r α) (h : ∀ a ∈ g.refs, v a=w a) : g.eval bank v=g.eval bank w := by
  cases g with
  | add a b => exact congrArg₂ (·+·) (h a (by simp [refs])) (h b (by simp [refs]))
  | sub a b => exact congrArg₂ (·-·) (h a (by simp [refs])) (h b (by simp [refs]))
  | scale c a => exact congrArg (c.eval bank*·) (h a (by simp [refs]))

/-- This bank is a semantic specification of the separately charged preparation:
root powers and the Fourier spectrum of the fixed kernel. It is not a free
instruction or a second root request in the printed program. -/
def coefficientBank (k : ℕ) (kernel : Fin (width k) → ℂ) : Fin (width k+width k) → ℂ :=
  Fin.addCases (fun i => zeta (width k)^i.val) ((fourierMatrix (width k)).mulVec kernel)

theorem powerCoefficient_eval (k : ℕ) (kernel : Fin (width k) → ℂ) (c : ℕ)
    (h : c < width k) : (powerCoefficient k c).eval (coefficientBank k kernel) = zeta (width k)^c := by
  rw [powerCoefficient,dite_eq_left h]
  simp only [UniformReplayPrint.Coefficient.eval,Bool.false_eq_true,ite_false,coefficientBank,Fin.addCases_left]

theorem prepareOp_eval {r : ℕ} {α : Type} (coeff : ℕ → UniformReplayPrint.Coefficient r)
    (g : Op α) (omega : ℂ) (bank : Fin r → ℂ) (v : α → ℂ)
    (h : ∀ c ∈ g.scalars, (coeff c).eval bank=omega^c) :
    (prepareOp coeff g).eval bank v = g.eval omega v := by
  cases g with
  | add a b => rfl
  | sub a b => rfl
  | scale c a => exact congrArg (·*v a) (h c (by simp [Op.scalars]))

def diagonalValues (k : ℕ) (kernel x : Fin (width k) → ℂ) : Fin (width k) → ℂ :=
  fun i => (fourierMatrix (width k)).mulVec kernel i * UniformRadixTwoDAG.eval k (zeta (width k)) x i

def values (k : ℕ) (kernel x : Fin (width k) → ℂ) : Ref k → ℂ
  | .inl i => x i
  | .inr (.forward j) => UniformRadixTwoDAG.values k (zeta (width k)) x (.inr j)
  | .inr (.diagonal i) => diagonalValues k kernel x i
  | .inr (.backward j) =>
      UniformRadixTwoDAG.values k (zeta (width k)) (diagonalValues k kernel x) (.inr j)
  | .inr (.normalize i) => (width k : ℂ)⁻¹ *
      UniformRadixTwoDAG.eval k (zeta (width k)) (diagonalValues k kernel x) (reverseIndex k i)

theorem values_forward (k : ℕ) (kernel x : Fin (width k) → ℂ) (r : UniformRadixTwoDAG.Ref k) :
    values k kernel x (forwardRef r) = UniformRadixTwoDAG.values k (zeta (width k)) x r := by
  cases r with
  | inl i => exact (UniformRadixTwoDAG.values_input k _ x i).symm
  | inr j => rfl

theorem values_backward (k : ℕ) (kernel x : Fin (width k) → ℂ) (r : UniformRadixTwoDAG.Ref k) :
    values k kernel x (backwardRef r) =
      UniformRadixTwoDAG.values k (zeta (width k)) (diagonalValues k kernel x) r := by
  cases r with
  | inl i => exact (UniformRadixTwoDAG.values_input k (zeta (width k)) (diagonalValues k kernel x) i).symm
  | inr j => rfl

theorem values_gate (k : ℕ) (kernel x : Fin (width k) → ℂ) (j : Node k) :
    values k kernel x (.inr j) = (gate j).eval (coefficientBank k kernel) (values k kernel x) := by
  cases j with
  | forward j =>
    rw [gate,Expr.eval_map]
    have hv : (values k kernel x ∘ forwardRef) = UniformRadixTwoDAG.values k (zeta (width k)) x := by
      funext r; exact values_forward k kernel x r
    rw [hv,prepareOp_eval]
    · exact UniformRadixTwoDAG.values_gate k _ x j
    · intro c hc
      exact powerCoefficient_eval k kernel c (gate_scalar_bound j c hc)
  | diagonal i =>
    rw [gate,Expr.eval,values_forward]
    simp only [UniformReplayPrint.Coefficient.eval,Bool.false_eq_true,ite_false,coefficientBank,Fin.addCases_right]
    rfl
  | backward j =>
    rw [gate,Expr.eval_map]
    have hv : (values k kernel x ∘ backwardRef) =
        UniformRadixTwoDAG.values k (zeta (width k)) (diagonalValues k kernel x) := by
      funext r; exact values_backward k kernel x r
    rw [hv,prepareOp_eval]
    · exact UniformRadixTwoDAG.values_gate k _ _ j
    · intro c hc
      exact powerCoefficient_eval k kernel c (gate_scalar_bound j c hc)
  | normalize i =>
    rw [gate,Expr.eval,values_backward]
    simp [UniformReplayPrint.Coefficient.eval,values,UniformRadixTwoDAG.eval]

def natValues (k : ℕ) (kernel x : Fin (width k) → ℂ) (a : ℕ) : ℂ :=
  if h : a < width k then x ⟨a,h⟩
  else if h : a-width k < total k then values k kernel x (.inr ((nodeFin k).symm ⟨a-width k,h⟩))
  else 0

theorem natValues_ref (k : ℕ) (kernel x : Fin (width k) → ℂ) (r : Ref k) :
    natValues k kernel x (address r) = values k kernel x r := by
  cases r with
  | inl i => simp [natValues,address,i.isLt,values]
  | inr j =>
    have hn : ¬width k+(nodeFin k j).val < width k := by omega
    simp [natValues,address,hn,(nodeFin k j).isLt]

theorem printed_gate (k : ℕ) (kernel x : Fin (width k) → ℂ) (j : Fin (total k)) :
    natValues k kernel x (width k+j.val) =
      (instruction k j).eval (coefficientBank k kernel) (natValues k kernel x) := by
  have hv := natValues_ref k kernel x (.inr ((nodeFin k).symm j))
  simp only [address,Equiv.apply_symm_apply] at hv
  rw [hv,instruction,Expr.eval_map]
  have he : (natValues k kernel x ∘ address) = values k kernel x := by
    funext r; exact natValues_ref k kernel x r
  rw [he]
  exact values_gate k kernel x _


def readTyped {N : ℕ} (n t : ℕ) (f : Fin N → Fin (n+1))
    (v : Fin (n+1+t) → ℂ) (a : ℕ) : ℂ :=
  if h : a < N+t then v (typedIndex n t f a h) else 0

theorem Expr.lower_eval {r n : ℕ} (g : Expr r ℕ) (h : ∀ a ∈ g.refs, a < n)
    (bank : Fin r → ℂ) (v : Fin n → ℂ) :
    ((g.lower h).eval bank).eval v =
      g.eval bank (fun a => if ha : a < n then v ⟨a,ha⟩ else 0) := by
  cases g with
  | add a b =>
    have ha := h a (by simp [refs])
    have hb := h b (by simp [refs])
    simp [lower,UniformReplayPrint.Gate.eval,OAI.ExactFourier.Gate.eval,eval,ha,hb]
  | sub a b =>
    have ha := h a (by simp [refs])
    have hb := h b (by simp [refs])
    simp [lower,UniformReplayPrint.Gate.eval,OAI.ExactFourier.Gate.eval,eval,ha,hb]
  | scale c a =>
    have ha := h a (by simp [refs])
    simp [lower,UniformReplayPrint.Gate.eval,OAI.ExactFourier.Gate.eval,eval,ha]

theorem loweredGate_eval (k n : ℕ) (f : Fin (width k) → Fin (n+1)) (j : Fin (total k))
    (bank : Fin (width k+width k) → ℂ) (v : Fin (n+1+j.val) → ℂ) :
    ((loweredGate k n f j).eval bank).eval v =
      (instruction k j).eval bank (readTyped n j.val f v) := by
  rw [loweredGate,Expr.lower_eval,Expr.eval_map]
  apply Expr.eval_congr
  intro a ha
  have hb := printed_refs_before k j a ha
  have ht := wireAddress_lt n j.val f a hb
  simp only [Function.comp_apply,dite_eq_left ht,readTyped,dite_eq_left hb]
  rfl

def inputVector (k n : ℕ) (f : Fin (width k) → Fin (n+1)) (x : Fin n → ℂ) :
    Fin (width k) → ℂ := fun i => (Fin.snoc x (0 : ℂ) : Fin (n+1) → ℂ) (f i)

theorem programPrefix_eval (k n : ℕ) (f : Fin (width k) → Fin (n+1))
    (kernel : Fin (width k) → ℂ) (x : Fin n → ℂ) (t : ℕ) (ht : t ≤ total k)
    (a : ℕ) (ha : a < width k+t) :
    ((programPrefix k n f t ht).eval (coefficientBank k kernel)).eval x
        (typedIndex n t f a ha) = natValues k kernel (inputVector k n f x) a := by
  induction t generalizing a with
  | zero =>
    have hb : a < width k := by omega
    rw [typedIndex_initial n f ⟨a,hb⟩]
    simp only [programPrefix,UniformReplayPrint.Program.eval,OAI.ExactFourier.Program.eval,
      natValues,dite_eq_left hb,inputVector]
  | succ t ih =>
    let j : Fin (total k) := ⟨t,by omega⟩
    have he : ((loweredGate k n f j).eval (coefficientBank k kernel)).eval
        (((programPrefix k n f t (by omega)).eval (coefficientBank k kernel)).eval x) =
        (instruction k j).eval (coefficientBank k kernel) (natValues k kernel (inputVector k n f x)) := by
      rw [loweredGate_eval k n f j (coefficientBank k kernel)
        (((programPrefix k n f t (by omega)).eval (coefficientBank k kernel)).eval x)]
      apply Expr.eval_congr
      intro b hb
      have hbefore := printed_refs_before k j b hb
      rw [readTyped,dite_eq_left hbefore]
      exact ih (by omega) b hbefore
    by_cases heq : a = width k+t
    · subst a
      rw [typedIndex_last]
      simp only [programPrefix,UniformReplayPrint.Program.eval,OAI.ExactFourier.Program.eval]
      exact (@Fin.snoc_last (n+1+t) (fun _ => ℂ) _ _).trans
        (he.trans (printed_gate k kernel (inputVector k n f x) j).symm)
    · have hbefore : a < width k+t := by omega
      rw [typedIndex_castSucc n t f a hbefore]
      simp only [programPrefix,UniformReplayPrint.Program.eval,OAI.ExactFourier.Program.eval,Fin.snoc_castSucc]
      exact ih (by omega) a hbefore

theorem outputIndex_typed (k n : ℕ) (f : Fin (width k) → Fin (n+1)) (i : Fin (width k)) :
    outputIndex k n i = typedIndex n (total k) f (address (.inr (.normalize i)))
      (by change width k+(nodeFin k (.normalize i)).val < width k+total k
          have := (nodeFin k (.normalize i)).isLt; omega) := by
  apply Fin.ext
  simp [outputIndex,typedIndex,address,wireAddress]

/-- Exact action of the actual typed program, valid for arbitrary input wiring. -/
theorem program_eval (k n : ℕ) (f : Fin (width k) → Fin (n+1))
    (kernel : Fin (width k) → ℂ) (x : Fin n → ℂ) (i : Fin (width k)) :
    ((program k n f).eval (coefficientBank k kernel)).eval x (outputIndex k n i) =
      values k kernel (inputVector k n f x) (.inr (.normalize i)) := by
  rw [outputIndex_typed k n f i]
  exact (programPrefix_eval k n f kernel x (total k) (le_refl _) _ _).trans
    (natValues_ref k kernel (inputVector k n f x) (.inr (.normalize i)))


theorem reverseIndex_zMod (k : ℕ) (i : Fin (width k)) :
    FourierCRT.finZMod (width k) (reverseIndex k i) = -FourierCRT.finZMod (width k) i := by
  change (((width k-i.val)%width k : ℕ) : ZMod (width k)) = -(i.val : ZMod (width k))
  rw [ZMod.natCast_mod,Nat.cast_sub (Nat.le_of_lt i.isLt),ZMod.natCast_self,zero_sub]

theorem fft_specified (k : ℕ) (x : Fin (width k) → ℂ) :
    UniformRadixTwoDAG.eval k (zeta (width k)) x = (fourierMatrix (width k)).mulVec x := by
  have hroot : IsPrimitiveRoot (zeta (width k)) (width k) :=
    Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt (width_pos k))
  exact (eval_fft k _ hroot x).trans (by rfl)

theorem diagonal_toZMod (k : ℕ) (kernel x : Fin (width k) → ℂ) :
    UniformCyclic.toZMod (diagonalValues k kernel x) = fun q =>
      UniformCyclic.positiveDFT (UniformCyclic.toZMod x) q *
        UniformCyclic.positiveDFT (UniformCyclic.toZMod kernel) q := by
  funext q
  let i := (FourierCRT.finZMod (width k)).symm q
  have hi : FourierCRT.finZMod (width k) i = q := Equiv.apply_symm_apply _ q
  change (fourierMatrix (width k)).mulVec kernel i * UniformRadixTwoDAG.eval k (zeta (width k)) x i = _
  rw [fft_specified,← UniformCyclic.positiveDFT_fin kernel i,← UniformCyclic.positiveDFT_fin x i,hi,mul_comm]

/-- Positive FFT, fixed-kernel diagonal, positive FFT, reversal and rational
normalization implement the exact normalized inverse and cyclic convolution. -/
theorem normalized_values (k : ℕ) (kernel x : Fin (width k) → ℂ) (i : Fin (width k)) :
    values k kernel x (.inr (.normalize i)) =
      UniformCyclic.convolution (UniformCyclic.toZMod x) (UniformCyclic.toZMod kernel)
        (FourierCRT.finZMod (width k) i) := by
  change (width k : ℂ)⁻¹ * UniformRadixTwoDAG.eval k (zeta (width k)) (diagonalValues k kernel x)
    (reverseIndex k i) = _
  rw [fft_specified,← UniformCyclic.positiveDFT_fin (diagonalValues k kernel x) (reverseIndex k i),
    reverseIndex_zMod,← UniformCyclic.inversePositiveDFT_apply,diagonal_toZMod,
    UniformCyclic.convolution_via_fourier]

theorem cyclic_inputVector (k : ℕ) (x : Fin (width k) → ℂ) :
    inputVector k (width k) (fun i => i.castSucc) x = x := by
  funext i
  exact @Fin.snoc_castSucc (width k) (fun _ => ℂ) 0 x i

/-- The actual typed cyclic program, with no action or interpreted-DAG premise. -/
theorem cyclic_program_eval (k : ℕ) (kernel x : Fin (width k) → ℂ) (i : Fin (width k)) :
    ((cyclicProgram k).eval (coefficientBank k kernel)).eval x (outputIndex k (width k) i) =
      UniformCyclic.convolution (UniformCyclic.toZMod x) (UniformCyclic.toZMod kernel)
        (FourierCRT.finZMod (width k) i) := by
  rw [cyclicProgram,program_eval,cyclic_inputVector,normalized_values]

theorem padded_inputVector (k n : ℕ) (x : Fin n → ℂ) :
    inputVector k n (padInputs k n) x = UniformCyclic.fromZMod (UniformCyclic.pad x : ZMod (width k) → ℂ) := by
  funext i
  change (Fin.snoc x 0 : Fin (n+1) → ℂ) (padInputs k n i) = _
  by_cases hi : i.val<n
  · rw [padInputs,dite_eq_left hi]
    change (Fin.snoc x 0 : Fin (n+1) → ℂ) (⟨i.val,hi⟩ : Fin n).castSucc = _
    rw [Fin.snoc_castSucc]
    simp [UniformCyclic.fromZMod,UniformCyclic.pad,FourierCRT.finZMod,
      ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt,hi]
  · rw [padInputs,dite_eq_right hi,Fin.snoc_last]
    simp [UniformCyclic.fromZMod,UniformCyclic.pad,FourierCRT.finZMod,
      ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt,hi]

theorem toZMod_fromZMod (k : ℕ) (f : ZMod (width k) → ℂ) :
    UniformCyclic.toZMod (UniformCyclic.fromZMod f) = f := by
  funext q
  simp [UniformCyclic.toZMod,UniformCyclic.fromZMod]

/-- Padding and truncation are literal integer input/output reference maps.
They incur no uncharged arithmetic gate, and no scalar branch selects wiring. -/
theorem padded_program_eval (k n m : ℕ) (hn : n ≤ width k) (hm : m ≤ width k)
    (kernel : Fin (width k) → ℂ) (x : Fin n → ℂ) (i : Fin m) :
    ((paddedProgram k n).eval (coefficientBank k kernel)).eval x
      (outputIndex k n ⟨i.val,by have := i.isLt; omega⟩) =
      ∑ j : Fin n, x j * UniformCyclic.toZMod kernel ((i.val : ZMod (width k)) - j.val) := by
  rw [paddedProgram,program_eval,padded_inputVector,normalized_values,toZMod_fromZMod,
    UniformCyclic.convolution_pad hn]
  rfl


theorem padded_kernel_difference (k n t m : ℕ) (hsize : n+t ≤ width k) (hm : m ≤ width k)
    (kernel : Fin t → ℂ) (j : Fin n) (i : Fin m) :
    (UniformCyclic.pad kernel : ZMod (width k) → ℂ)
        ((i.val : ZMod (width k)) - j.val) =
      if _hji : j.val ≤ i.val then
        if hd : i.val-j.val < t then kernel ⟨i.val-j.val,hd⟩ else 0
      else 0 := by
  have hi : i.val < width k := i.isLt.trans_le hm
  have hj := j.isLt
  by_cases hji : j.val ≤ i.val
  · have hd : i.val-j.val < width k := by omega
    rw [← Nat.cast_sub hji]
    simp only [UniformCyclic.pad,ZMod.val_natCast,Nat.mod_eq_of_lt hd,dite_eq_left hji]
  · have hgap : j.val-i.val ≤ width k := by omega
    have hc : (((width k-(j.val-i.val) : ℕ)) : ZMod (width k)) =
        (i.val : ZMod (width k)) - j.val := by
      rw [Nat.cast_sub hgap,Nat.cast_sub (by omega : i.val ≤ j.val),ZMod.natCast_self]
      ring
    have hd : width k-(j.val-i.val) < width k := by omega
    have hnot : ¬width k-(j.val-i.val)<t := by omega
    rw [← hc]
    simp [UniformCyclic.pad,ZMod.val_natCast,Nat.mod_eq_of_lt hd,hnot,hji]

/-- Ordinary no-wrap linear convolution with a fixed finite kernel, truncated
at any m≤N. The prepared bank is the actual spectrum of its zero extension. -/
theorem linear_program_eval (k n t m : ℕ) (hsize : n+t ≤ width k) (hm : m ≤ width k)
    (kernel : Fin t → ℂ) (x : Fin n → ℂ) (i : Fin m) :
    ((paddedProgram k n).eval
        (coefficientBank k (inputVector k t (padInputs k t) kernel))).eval x
      (outputIndex k n ⟨i.val,by have := i.isLt; omega⟩) =
      ∑ j : Fin n, if _hji : j.val ≤ i.val then
        if hd : i.val-j.val < t then kernel ⟨i.val-j.val,hd⟩ * x j else 0
      else 0 := by
  rw [padded_program_eval k n m (by omega) hm,padded_inputVector,toZMod_fromZMod]
  apply Finset.sum_congr rfl
  intro j _
  rw [padded_kernel_difference k n t m hsize hm kernel j i]
  split_ifs <;> simp [mul_comm]


theorem fft_program_eval (k n : ℕ) (f : Fin (width k) → Fin (n+1))
    (kernel : Fin (width k) → ℂ) (x : Fin n → ℂ) (i : Fin (width k)) :
    ((fftProgram k n f).eval (coefficientBank k kernel)).eval x (fftOutputIndex k n f i) =
      (fourierMatrix (width k)).mulVec (inputVector k n f x) i := by
  have hp := programPrefix_eval k n f kernel x (count k) (by unfold total; omega)
    (UniformRadixTwoDAG.refNat (output k i)) (refNat_bound (output k i))
  have hv := natValues_ref k kernel (inputVector k n f x) (forwardRef (output k i))
  rw [address_forward,values_forward] at hv
  have he : UniformRadixTwoDAG.values k (zeta (width k)) (inputVector k n f x) (output k i) =
      (fourierMatrix (width k)).mulVec (inputVector k n f x) i :=
    congrFun (fft_specified k (inputVector k n f x)) i
  exact hp.trans (hv.trans he)

/-- Concrete dirty replay restores every borrowed gate register and adds the
exact ordinary linear convolution to arbitrary output accumulators. -/
theorem convolutionReplay_spec (k n t m : ℕ) (hsize : n+t ≤ width k) (hm : m ≤ width k)
    (kernel : Fin t → ℂ) (x : Fin n → ℂ) (y : Fin m → ℂ) (z : Fin (total k) → ℂ) :
    runShears ((convolutionReplay k n m hm).map
      (UniformReplayPrint.ShearCode.eval
        (coefficientBank k (inputVector k t (padInputs k t) kernel))))
      (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z) (fun i => y i+
        ∑ j : Fin n, if _hji : j.val ≤ i.val then
          if hd : i.val-j.val<t then kernel ⟨i.val-j.val,hd⟩*x j else 0
        else 0) := by
  rw [convolutionReplay,UniformReplayPrint.replayCode_spec]
  congr 1
  funext i
  exact congrArg (y i+·) (linear_program_eval k n t m hsize hm kernel x i)

end
end ExactFourierCircuits.UniformConvolutionDAG
