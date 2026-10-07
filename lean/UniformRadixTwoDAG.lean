import UniformNewton
import OAI.Computability.FourierCircuit.FFTCircuit

/-! A computable printed radix-two topology. Scale instructions contain prepared
power-table references, never complex literals. Node equations determine its
semantics uniquely; their natural addresses are strictly topological. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRadixTwoDAG
open OAI.ExactFourier

@[reducible] def width : ℕ → ℕ
  | 0 => 1
  | k+1 => width k + width k

theorem width_eq (k : ℕ) : width k = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [width, ih, pow_succ]; omega

theorem width_pos (k : ℕ) : 0 < width k := by
  rw [width_eq]
  positivity

inductive Node : ℕ → Type where
  | even {k : ℕ} (child : Node k) : Node (k+1)
  | odd {k : ℕ} (child : Node k) : Node (k+1)
  | scale {k : ℕ} (index : Fin (width k)) : Node (k+1)
  | add {k : ℕ} (index : Fin (width k)) : Node (k+1)
  | sub {k : ℕ} (index : Fin (width k)) : Node (k+1)

abbrev Ref (k : ℕ) := Fin (width k) ⊕ Node k

def evenRef {k : ℕ} : Ref k → Ref (k+1)
  | .inl i => .inl (RadixTwo.evenIndex (width k) i)
  | .inr j => .inr (.even j)

def oddRef {k : ℕ} : Ref k → Ref (k+1)
  | .inl i => .inl (RadixTwo.oddIndex (width k) i)
  | .inr j => .inr (.odd j)

def output : (k : ℕ) → Fin (width k) → Ref k
  | 0, i => .inl i
  | _+1, i => Fin.addCases (fun j => .inr (.add j)) (fun j => .inr (.sub j)) i

inductive Op (α : Type) where
  | add (left right : α)
  | sub (left right : α)
  | scale (scalar : ℕ) (source : α)
  deriving Repr

namespace Op

def refs {α : Type} : Op α → List α
  | .add a b => [a,b]
  | .sub a b => [a,b]
  | .scale _ a => [a]

def map {α β : Type} (f : α → β) : Op α → Op β
  | .add a b => .add (f a) (f b)
  | .sub a b => .sub (f a) (f b)
  | .scale c a => .scale c (f a)

def double {α : Type} : Op α → Op α
  | .add a b => .add a b
  | .sub a b => .sub a b
  | .scale c a => .scale (2*c) a

noncomputable def eval {α : Type} (omega : ℂ) (v : α → ℂ) : Op α → ℂ
  | .add a b => v a + v b
  | .sub a b => v a - v b
  | .scale c a => omega^c * v a

theorem eval_double_map {α β : Type} (omega : ℂ) (v : β → ℂ) (f : α → β)
    (g : Op α) : (g.double.map f).eval omega v = g.eval (omega^2) (v ∘ f) := by
  cases g <;> simp only [double,map,eval,Function.comp_apply]
  rw [pow_mul]

end Op

theorem Op.refs_map {α β : Type} (f : α → β) (g : Op α) :
    (g.map f).refs = g.refs.map f := by cases g <;> rfl

theorem Op.refs_double {α : Type} (g : Op α) : g.double.refs = g.refs := by
  cases g <;> rfl


def gate : {k : ℕ} → Node k → Op (Ref k)
  | _, .even j => (gate j).double.map evenRef
  | _, .odd j => (gate j).double.map oddRef
  | k+1, .scale i => .scale i.val (oddRef (output k i))
  | k+1, .add i => .add (evenRef (output k i)) (.inr (.scale i))
  | k+1, .sub i => .sub (evenRef (output k i)) (.inr (.scale i))

noncomputable def values : (k : ℕ) → ℂ → (Fin (width k) → ℂ) → Ref k → ℂ
  | _, _, x, .inl i => x i
  | k+1, omega, x, .inr (.even j) =>
      values k (omega^2) (x ∘ RadixTwo.evenIndex (width k)) (.inr j)
  | k+1, omega, x, .inr (.odd j) =>
      values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) (.inr j)
  | k+1, omega, x, .inr (.scale i) =>
      omega^i.val * values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) (output k i)
  | k+1, omega, x, .inr (.add i) =>
      values k (omega^2) (x ∘ RadixTwo.evenIndex (width k)) (output k i) +
        omega^i.val * values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) (output k i)
  | k+1, omega, x, .inr (.sub i) =>
      values k (omega^2) (x ∘ RadixTwo.evenIndex (width k)) (output k i) -
        omega^i.val * values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) (output k i)

@[simp] theorem values_input (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (i : Fin (width k)) : values k omega x (.inl i) = x i := by
  cases k <;> rfl

theorem values_even (k : ℕ) (omega : ℂ) (x : Fin (width (k+1)) → ℂ) (r : Ref k) :
    values (k+1) omega x (evenRef r) =
      values k (omega^2) (x ∘ RadixTwo.evenIndex (width k)) r := by
  cases r with
  | inl i =>
      simp only [evenRef, values_input, Function.comp_apply]
      exact values_input (k+1) omega x _
  | inr j => rfl

theorem values_odd (k : ℕ) (omega : ℂ) (x : Fin (width (k+1)) → ℂ) (r : Ref k) :
    values (k+1) omega x (oddRef r) =
      values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) r := by
  cases r with
  | inl i =>
      simp only [oddRef, values_input, Function.comp_apply]
      exact values_input (k+1) omega x _
  | inr j => rfl

theorem values_gate (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (j : Node k) :
    values k omega x (.inr j) = (gate j).eval omega (values k omega x) := by
  induction j generalizing omega with
  | even j ih =>
      simp only [gate, Op.eval_double_map, values]
      rw [show (values _ omega x ∘ evenRef) =
        values _ (omega^2) (x ∘ RadixTwo.evenIndex _) by funext r; exact values_even _ _ _ r]
      exact ih _ _
  | odd j ih =>
      simp only [gate, Op.eval_double_map, values]
      rw [show (values _ omega x ∘ oddRef) =
        values _ (omega^2) (x ∘ RadixTwo.oddIndex _) by funext r; exact values_odd _ _ _ r]
      exact ih _ _
  | scale i => simp only [values,gate,Op.eval,values_odd]
  | add i => simp only [values,gate,Op.eval,values_even]
  | sub i => simp only [values,gate,Op.eval,values_even]

noncomputable def eval (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    Fin (width k) → ℂ := fun i => values k omega x (output k i)

theorem eval_fft (k : ℕ) (omega : ℂ) (hroot : IsPrimitiveRoot omega (width k))
    (x : Fin (width k) → ℂ) : eval k omega x = RadixTwo.eval (width k) omega x := by
  induction k generalizing omega with
  | zero =>
      funext i
      have hi : i=0 := Fin.eq_zero i
      simp [eval,output,values,RadixTwo.eval,RadixTwo.evalAt,hi,width]
  | succ k ih =>
      have hs : IsPrimitiveRoot (omega^2) (width k) :=
        IsPrimitiveRoot.pow (width_pos (k+1)) hroot (by simp [width]; omega)
      have hh : omega^(width k) = -1 :=
        (IsPrimitiveRoot.pow (width_pos (k+1)) hroot (by simp [width]; omega)).eq_neg_one_of_two_right
      rw [RadixTwo.eval_split _ _ hh]
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [eval,output,Fin.addCases_left,Fin.addCases_right,values]
      · rw [← ih (omega^2) hs (x ∘ RadixTwo.evenIndex _),
          ← ih (omega^2) hs (x ∘ RadixTwo.oddIndex _)]
        rfl
      · rw [← ih (omega^2) hs (x ∘ RadixTwo.evenIndex _),
          ← ih (omega^2) hs (x ∘ RadixTwo.oddIndex _)]
        rfl

/-- Any interpretation of the literal input/gate equations has these values. -/
theorem values_unique (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (v : Ref k → ℂ) (hin : ∀ i, v (.inl i) = x i)
    (hg : ∀ j, v (.inr j) = (gate j).eval omega v) : v = values k omega x := by
  induction k generalizing omega with
  | zero =>
      funext r
      cases r with
      | inl i => exact hin i
      | inr j => nomatch j
  | succ k ih =>
      have he : v ∘ evenRef =
          values k (omega^2) (x ∘ RadixTwo.evenIndex (width k)) := by
        apply ih
        · intro i; exact hin (RadixTwo.evenIndex _ i)
        · intro j
          simpa only [Function.comp_apply, evenRef, gate, Op.eval_double_map] using hg (.even j)
      have ho : v ∘ oddRef =
          values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) := by
        apply ih
        · intro i; exact hin (RadixTwo.oddIndex _ i)
        · intro j
          simpa only [Function.comp_apply, oddRef, gate, Op.eval_double_map] using hg (.odd j)
      have hscale (i : Fin (width k)) : v (.inr (.scale i)) =
          omega^i.val * values k (omega^2) (x ∘ RadixTwo.oddIndex (width k)) (output k i) := by
        rw [hg]
        simpa only [gate,Op.eval,Function.comp_apply] using
          congrArg (fun z => omega^i.val*z) (congrFun ho (output k i))
      funext r
      cases r with
      | inl i => exact hin i
      | inr j =>
          cases j with
          | even j => exact congrFun he (.inr j)
          | odd j => exact congrFun ho (.inr j)
          | scale i => exact hscale i
          | add i =>
              rw [hg]
              simp only [gate,Op.eval,hscale,values]
              exact congrArg (fun z => z + _) (congrFun he (output k i))
          | sub i =>
              rw [hg]
              simp only [gate,Op.eval,hscale,values]
              exact congrArg (fun z => z - _) (congrFun he (output k i))

def depth : {k : ℕ} → Ref k → ℕ
  | _, .inl _ => 0
  | _, .inr (.even j) => depth (.inr j)
  | _, .inr (.odd j) => depth (.inr j)
  | k+1, .inr (.scale _) => 2*k+1
  | k+1, .inr (.add _) => 2*k+2
  | k+1, .inr (.sub _) => 2*k+2

@[simp] theorem depth_input (k : ℕ) (i : Fin (width k)) : depth (.inl i : Ref k) = 0 := by
  cases k <;> rfl

theorem depth_even {k : ℕ} (r : Ref k) : depth (evenRef r) = depth r := by
  cases r with
  | inl i =>
      simp only [evenRef,depth_input]
      exact depth_input (k+1) _
  | inr j => rfl

theorem depth_odd {k : ℕ} (r : Ref k) : depth (oddRef r) = depth r := by
  cases r with
  | inl i =>
      simp only [oddRef,depth_input]
      exact depth_input (k+1) _
  | inr j => rfl

theorem output_depth (k : ℕ) (i : Fin (width k)) : depth (output k i) = 2*k := by
  cases k with
  | zero => rfl
  | succ k =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [output,Fin.addCases_left,Fin.addCases_right,depth] <;> omega

def Op.depth {α : Type} (d : α → ℕ) : Op α → ℕ
  | .add a b => max (d a) (d b) + 1
  | .sub a b => max (d a) (d b) + 1
  | .scale _ a => d a + 1

theorem Op.depth_double_map {α β : Type} (d : β → ℕ) (f : α → β) (g : Op α) :
    (g.double.map f).depth d = g.depth (d ∘ f) := by cases g <;> rfl

/-- These labels equal the actual longest input-to-node path lengths. -/
theorem depth_gate {k : ℕ} (j : Node k) : depth (.inr j) = (gate j).depth depth := by
  induction j with
  | even j ih =>
      simp only [gate,Op.depth_double_map]
      rw [show (depth ∘ evenRef) = depth by funext r; exact depth_even r]
      exact ih
  | odd j ih =>
      simp only [gate,Op.depth_double_map]
      rw [show (depth ∘ oddRef) = depth by funext r; exact depth_odd r]
      exact ih
  | scale i => simp only [gate,Op.depth,depth,depth_odd,output_depth]
  | add i =>
      simp only [gate,Op.depth,depth,depth_even,output_depth]
      rw [Nat.max_eq_right (by omega)]
  | sub i =>
      simp only [gate,Op.depth,depth,depth_even,output_depth]
      rw [Nat.max_eq_right (by omega)]

theorem depth_bound (k : ℕ) (r : Ref k) : depth r ≤ 2*k := by
  induction k with
  | zero => cases r with
    | inl i => exact le_refl 0
    | inr j => nomatch j
  | succ k ih =>
      cases r with
      | inl i => change 0 ≤ 2*(k+1); omega
      | inr j =>
          cases j with
          | even j => exact (ih (.inr j)).trans (by omega)
          | odd j => exact (ih (.inr j)).trans (by omega)
          | scale i => simp only [depth]; omega
          | add i => simp only [depth]; omega
          | sub i => simp only [depth]; omega

theorem depth_exact (k : ℕ) : (∀ r : Ref k, depth r ≤ 2*k) ∧
    ∃ r : Ref k, depth r = 2*k :=
  ⟨depth_bound k, ⟨output k ⟨0,width_pos k⟩, output_depth _ _⟩⟩

def Op.scalars {α : Type} : Op α → List ℕ
  | .add _ _ => []
  | .sub _ _ => []
  | .scale c _ => [c]

theorem Op.scalars_map {α β : Type} (f : α → β) (g : Op α) :
    (g.map f).scalars = g.scalars := by cases g <;> rfl

theorem Op.scalars_double {α : Type} (g : Op α) :
    g.double.scalars = g.scalars.map (2*·) := by cases g <;> rfl

theorem gate_scalar_bound {k : ℕ} (j : Node k) (c : ℕ) (h : c ∈ (gate j).scalars) :
    c < width k := by
  induction j generalizing c with
  | even j ih =>
      simp only [gate,Op.scalars_map,Op.scalars_double,List.mem_map] at h
      obtain ⟨a,ha,rfl⟩ := h
      have := ih a ha
      simp only [width]
      omega
  | odd j ih =>
      simp only [gate,Op.scalars_map,Op.scalars_double,List.mem_map] at h
      obtain ⟨a,ha,rfl⟩ := h
      have := ih a ha
      simp only [width]
      omega
  | scale i =>
      simp only [gate,Op.scalars,List.mem_singleton] at h
      subst c
      have := i.isLt
      simp only [width]
      omega
  | add i => simp only [gate,Op.scalars,List.not_mem_nil] at h
  | sub i => simp only [gate,Op.scalars,List.not_mem_nil] at h


/-- Recognize exactly the unique ordered output ports. -/
def outputIndex : (k : ℕ) → Ref k → Option (Fin (width k))
  | 0, .inl i => some i
  | k+1, .inr (.add i) => some (Fin.castAdd (width k) i)
  | k+1, .inr (.sub i) => some (Fin.natAdd (width k) i)
  | _, _ => none

theorem outputIndex_some (k : ℕ) (r : Ref k) (i : Fin (width k)) :
    outputIndex k r = some i ↔ r = output k i := by
  cases k with
  | zero =>
      cases r with
      | inl j => simp [outputIndex,output]
      | inr j => nomatch j
  | succ k =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        cases r with
        | inl j => simp only [outputIndex,output,Fin.addCases_left,Fin.addCases_right]; simp
        | inr j =>
            cases j <;> simp only [outputIndex,output,Fin.addCases_left,Fin.addCases_right]
            all_goals simp [Fin.ext_iff]
            all_goals omega

theorem output_injective (k : ℕ) : Function.Injective (output k) := by
  intro i j hij
  have hi := (outputIndex_some k (output k i) i).mpr rfl
  have hj := (outputIndex_some k (output k j) j).mpr rfl
  rw [hij,hj] at hi
  exact (Option.some.inj hi).symm

theorem evenRef_injective (k : ℕ) : Function.Injective (@evenRef k) := by
  intro r s h
  cases r with
  | inl i => cases s with
    | inl j =>
        apply congrArg Sum.inl
        apply Fin.ext
        have hv := congrArg Fin.val (Sum.inl.inj h)
        simp only [RadixTwo.evenIndex] at hv
        omega
    | inr j => cases h
  | inr i => cases s with
    | inl j => cases h
    | inr j => exact congrArg Sum.inr (Node.even.inj (Sum.inr.inj h))

theorem oddRef_injective (k : ℕ) : Function.Injective (@oddRef k) := by
  intro r s h
  cases r with
  | inl i => cases s with
    | inl j =>
        apply congrArg Sum.inl
        apply Fin.ext
        have hv := congrArg Fin.val (Sum.inl.inj h)
        simp only [RadixTwo.oddIndex] at hv
        omega
    | inr j => cases h
  | inr i => cases s with
    | inl j => cases h
    | inr j => exact congrArg Sum.inr (Node.odd.inj (Sum.inr.inj h))

@[simp] theorem evenRef_eq {k : ℕ} (r s : Ref k) : evenRef r = evenRef s ↔ r=s :=
  (evenRef_injective k).eq_iff
@[simp] theorem oddRef_eq {k : ℕ} (r s : Ref k) : oddRef r = oddRef s ↔ r=s :=
  (oddRef_injective k).eq_iff

@[simp] theorem evenRef_ne_oddRef {k : ℕ} (r s : Ref k) : evenRef r ≠ oddRef s := by
  cases r with
  | inl i => cases s with
    | inl j =>
        intro h
        have hv := congrArg Fin.val (Sum.inl.inj h)
        simp only [RadixTwo.evenIndex,RadixTwo.oddIndex] at hv
        omega
    | inr j => intro h; cases h
  | inr i => cases s <;> intro h <;> cases h

@[simp] theorem oddRef_ne_evenRef {k : ℕ} (r s : Ref k) : oddRef r ≠ evenRef s :=
  (evenRef_ne_oddRef s r).symm

@[simp] theorem evenRef_ne_scale {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    evenRef r ≠ .inr (.scale i) := by cases r <;> intro h <;> cases h
@[simp] theorem oddRef_ne_scale {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    oddRef r ≠ .inr (.scale i) := by cases r <;> intro h <;> cases h
@[simp] theorem evenRef_ne_add {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    evenRef r ≠ .inr (.add i) := by cases r <;> intro h <;> cases h
@[simp] theorem oddRef_ne_add {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    oddRef r ≠ .inr (.add i) := by cases r <;> intro h <;> cases h
@[simp] theorem evenRef_ne_sub {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    evenRef r ≠ .inr (.sub i) := by cases r <;> intro h <;> cases h
@[simp] theorem oddRef_ne_sub {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    oddRef r ≠ .inr (.sub i) := by cases r <;> intro h <;> cases h

def through {k : ℕ} (tag : Node k → Node (k+1))
    (ports : Fin (width k) → List (Node (k+1))) (old : Ref k → List (Node k))
    (r : Ref k) : List (Node (k+1)) :=
  match outputIndex k r with
  | some i => ports i
  | none => (old r).map tag

def successors : (k : ℕ) → Ref k → List (Node k)
  | 0, _ => []
  | k+1, .inl i =>
      let jb := (RadixTwo.parityEquiv (width k)).symm i
      if jb.2.val = 0 then
        through Node.even (fun j => [.add j,.sub j]) (successors k) (.inl jb.1)
      else through Node.odd (fun j => [.scale j]) (successors k) (.inl jb.1)
  | k+1, .inr (.even j) =>
      through Node.even (fun i => [.add i,.sub i]) (successors k) (.inr j)
  | k+1, .inr (.odd j) =>
      through Node.odd (fun i => [.scale i]) (successors k) (.inr j)
  | _+1, .inr (.scale i) => [.add i,.sub i]
  | _+1, .inr (.add _) => []
  | _+1, .inr (.sub _) => []

theorem parity_even (k : ℕ) (i : Fin (width k)) :
    (RadixTwo.parityEquiv (width k)).symm (RadixTwo.evenIndex (width k) i) = (i,0) := by
  change (RadixTwo.parityEquiv (width k)).symm
    (RadixTwo.parityEquiv (width k) (i,0)) = _
  exact Equiv.symm_apply_apply _ _

theorem parity_odd (k : ℕ) (i : Fin (width k)) :
    (RadixTwo.parityEquiv (width k)).symm (RadixTwo.oddIndex (width k) i) = (i,1) := by
  change (RadixTwo.parityEquiv (width k)).symm
    (RadixTwo.parityEquiv (width k) (i,1)) = _
  exact Equiv.symm_apply_apply _ _

theorem successors_even {k : ℕ} (r : Ref k) :
    successors (k+1) (evenRef r) =
      through Node.even (fun i => [.add i,.sub i]) (successors k) r := by
  cases r with
  | inl i => simp only [evenRef,successors,parity_even,Fin.val_zero,ite_true]
  | inr j => rfl

theorem successors_odd {k : ℕ} (r : Ref k) :
    successors (k+1) (oddRef r) =
      through Node.odd (fun i => [.scale i]) (successors k) r := by
  cases r with
  | inl i => simp only [oddRef,successors,parity_odd,Fin.val_one,one_ne_zero,ite_false]
  | inr j => rfl

theorem successors_terminal (k : ℕ) (i : Fin (width k)) : successors k (output k i) = [] := by
  cases k with
  | zero => rfl
  | succ k =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [output,Fin.addCases_left,Fin.addCases_right] <;> rfl

theorem through_bound {k : ℕ} (tag : Node k → Node (k+1))
    (ports : Fin (width k) → List (Node (k+1))) (old : Ref k → List (Node k))
    (hp : ∀ i, (ports i).length ≤ 2) (ho : ∀ r, (old r).length ≤ 2) (r : Ref k) :
    (through tag ports old r).length ≤ 2 := by
  unfold through
  cases outputIndex k r with
  | none => simpa only [List.length_map] using ho r
  | some i => exact hp i

theorem successors_bound (k : ℕ) (r : Ref k) : (successors k r).length ≤ 2 := by
  induction k with
  | zero => exact Nat.zero_le 2
  | succ k ih =>
      cases r with
      | inl i =>
          simp only [successors]
          split_ifs <;> apply through_bound <;> try exact ih
          · intro i; exact le_refl 2
          · intro i; change 1 ≤ 2; decide
      | inr j => cases j with
          | even j => exact through_bound _ _ _ (fun _ => le_refl 2) ih _
          | odd j => exact through_bound _ _ _ (fun _ => by change 1 ≤ 2; decide) ih _
          | scale i => exact le_refl 2
          | add i => exact Nat.zero_le 2
          | sub i => exact Nat.zero_le 2


@[simp] theorem scale_ne_evenRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.scale i) : Ref (k+1)) ≠ evenRef r := (evenRef_ne_scale r i).symm
@[simp] theorem scale_ne_oddRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.scale i) : Ref (k+1)) ≠ oddRef r := (oddRef_ne_scale r i).symm
@[simp] theorem add_ne_evenRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.add i) : Ref (k+1)) ≠ evenRef r := (evenRef_ne_add r i).symm
@[simp] theorem add_ne_oddRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.add i) : Ref (k+1)) ≠ oddRef r := (oddRef_ne_add r i).symm
@[simp] theorem sub_ne_evenRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.sub i) : Ref (k+1)) ≠ evenRef r := (evenRef_ne_sub r i).symm
@[simp] theorem sub_ne_oddRef {k : ℕ} (i : Fin (width k)) (r : Ref k) :
    (.inr (.sub i) : Ref (k+1)) ≠ oddRef r := (oddRef_ne_sub r i).symm

theorem through_even_child {k : ℕ} (r : Ref k) (j : Node k) :
    .even j ∈ through Node.even (fun i => [.add i,.sub i]) (successors k) r ↔
      j ∈ successors k r := by
  unfold through
  cases h : outputIndex k r with
  | none => simp [List.mem_map]
  | some i =>
      have hr := (outputIndex_some k r i).mp h
      rw [hr,successors_terminal]
      simp

theorem through_odd_child {k : ℕ} (r : Ref k) (j : Node k) :
    .odd j ∈ through Node.odd (fun i => [.scale i]) (successors k) r ↔
      j ∈ successors k r := by
  unfold through
  cases h : outputIndex k r with
  | none => simp [List.mem_map]
  | some i =>
      have hr := (outputIndex_some k r i).mp h
      rw [hr,successors_terminal]
      simp

theorem through_even_add {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    .add i ∈ through Node.even (fun j => [.add j,.sub j]) (successors k) r ↔
      r = output k i := by
  rw [← outputIndex_some]
  unfold through
  cases outputIndex k r <;> simp [List.mem_map,eq_comm]

theorem through_even_sub {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    .sub i ∈ through Node.even (fun j => [.add j,.sub j]) (successors k) r ↔
      r = output k i := by
  rw [← outputIndex_some]
  unfold through
  cases outputIndex k r <;> simp [List.mem_map,eq_comm]

theorem through_odd_scale {k : ℕ} (r : Ref k) (i : Fin (width k)) :
    .scale i ∈ through Node.odd (fun j => [.scale j]) (successors k) r ↔
      r = output k i := by
  rw [← outputIndex_some]
  unfold through
  cases outputIndex k r <;> simp [List.mem_map,eq_comm]

theorem through_even_other {k : ℕ} (r : Ref k) :
    (∀ j, .odd j ∉ through Node.even (fun i => [.add i,.sub i]) (successors k) r) ∧
    (∀ i, .scale i ∉ through Node.even (fun i => [.add i,.sub i]) (successors k) r) := by
  unfold through
  cases outputIndex k r <;> simp [List.mem_map]

theorem through_odd_other {k : ℕ} (r : Ref k) :
    (∀ j, .even j ∉ through Node.odd (fun i => [.scale i]) (successors k) r) ∧
    (∀ i, .add i ∉ through Node.odd (fun i => [.scale i]) (successors k) r) ∧
    (∀ i, .sub i ∉ through Node.odd (fun i => [.scale i]) (successors k) r) := by
  unfold through
  cases outputIndex k r <;> simp [List.mem_map]

theorem ref_cases {k : ℕ} (r : Ref (k+1)) :
    (∃ q : Ref k, r=evenRef q) ∨ (∃ q : Ref k, r=oddRef q) ∨
    (∃ i, r=.inr (.scale i)) ∨ (∃ i, r=.inr (.add i)) ∨ (∃ i, r=.inr (.sub i)) := by
  cases r with
  | inl i =>
      have hb : i.val/2 < width k := by have := i.isLt; simp only [width] at this; omega
      let j : Fin (width k) := ⟨i.val/2,hb⟩
      by_cases h : i.val%2=0
      · left
        refine ⟨.inl j, ?_⟩
        apply congrArg Sum.inl
        apply Fin.ext
        simp only [RadixTwo.evenIndex]
        dsimp [j]
        omega
      · right; left
        refine ⟨.inl j, ?_⟩
        apply congrArg Sum.inl
        apply Fin.ext
        simp only [RadixTwo.oddIndex]
        dsimp [j]
        omega
  | inr j => cases j with
      | even j => exact Or.inl ⟨.inr j,rfl⟩
      | odd j => exact Or.inr (Or.inl ⟨.inr j,rfl⟩)
      | scale i => exact Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))
      | add i => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
      | sub i => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,rfl⟩)))

/-- The computed successor list contains precisely the actual consumer gates. -/
theorem successors_spec (k : ℕ) (r : Ref k) (j : Node k) :
    j ∈ successors k r ↔ r ∈ (gate j).refs := by
  induction k with
  | zero => nomatch j
  | succ k ih =>
      rcases ref_cases r with ⟨q,rfl⟩ | ⟨q,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩
      · rw [successors_even]
        cases j with
        | even j =>
            rw [through_even_child,ih]
            simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@evenRef_eq k]
        | odd j => simp [through_even_other,gate,Op.refs_map,Op.refs_double,List.mem_map,@oddRef_ne_evenRef k]
        | scale i => simp [through_even_other,gate,Op.refs,@evenRef_ne_oddRef k]
        | add i => rw [through_even_add]; simp [gate,Op.refs,@evenRef_eq k,@evenRef_ne_scale k]
        | sub i => rw [through_even_sub]; simp [gate,Op.refs,@evenRef_eq k,@evenRef_ne_scale k]
      · rw [successors_odd]
        cases j with
        | even j => simp [through_odd_other,gate,Op.refs_map,Op.refs_double,List.mem_map,@evenRef_ne_oddRef k]
        | odd j =>
            rw [through_odd_child,ih]
            simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@oddRef_eq k]
        | scale i => rw [through_odd_scale]; simp [gate,Op.refs,@oddRef_eq k]
        | add i => simp [through_odd_other,gate,Op.refs,@oddRef_ne_evenRef k,@oddRef_ne_scale k]
        | sub i => simp [through_odd_other,gate,Op.refs,@oddRef_ne_evenRef k,@oddRef_ne_scale k]
      · change j ∈ [.add i,.sub i] ↔ _
        cases j with
        | even j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@evenRef_ne_scale k]
        | odd j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@oddRef_ne_scale k]
        | scale j => simp [gate,Op.refs,@scale_ne_oddRef k]
        | add j => simp [gate,Op.refs,@evenRef_ne_scale k,eq_comm]
        | sub j => simp [gate,Op.refs,@evenRef_ne_scale k,eq_comm]
      · change j ∈ [] ↔ _
        cases j with
        | even j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@evenRef_ne_add k]
        | odd j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@oddRef_ne_add k]
        | scale j => simp [gate,Op.refs,@add_ne_oddRef k]
        | add j => simp [gate,Op.refs,@add_ne_evenRef k]
        | sub j => simp [gate,Op.refs,@add_ne_evenRef k]
      · change j ∈ [] ↔ _
        cases j with
        | even j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@evenRef_ne_sub k]
        | odd j => simp [gate,Op.refs_map,Op.refs_double,List.mem_map,@oddRef_ne_sub k]
        | scale j => simp [gate,Op.refs,@sub_ne_oddRef k]
        | add j => simp [gate,Op.refs,@sub_ne_evenRef k]
        | sub j => simp [gate,Op.refs,@sub_ne_evenRef k]

theorem through_nodup {k : ℕ} (tag : Node k → Node (k+1))
    (ports : Fin (width k) → List (Node (k+1))) (old : Ref k → List (Node k))
    (ht : Function.Injective tag) (hp : ∀ i, (ports i).Nodup) (ho : ∀ r, (old r).Nodup)
    (r : Ref k) : (through tag ports old r).Nodup := by
  unfold through
  cases outputIndex k r with
  | none => exact (ho r).map ht
  | some i => exact hp i

theorem successors_nodup (k : ℕ) (r : Ref k) : (successors k r).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
      cases r with
      | inl i =>
          simp only [successors]
          split_ifs
          · exact through_nodup _ _ _ (fun _ _ h => Node.even.inj h) (fun i => by simp) ih _
          · exact through_nodup _ _ _ (fun _ _ h => Node.odd.inj h) (fun i => by simp) ih _
      | inr j => cases j with
          | even j => exact through_nodup _ _ _ (fun _ _ h => Node.even.inj h) (fun i => by simp) ih _
          | odd j => exact through_nodup _ _ _ (fun _ _ h => Node.odd.inj h) (fun i => by simp) ih _
          | scale i => change [Node.add i,Node.sub i].Nodup; simp
          | add i => exact List.nodup_nil
          | sub i => exact List.nodup_nil

theorem gate_refs_nodup {k : ℕ} (j : Node k) : (gate j).refs.Nodup := by
  induction j with
  | even j ih => rw [gate,Op.refs_map,Op.refs_double]; exact ih.map (evenRef_injective _)
  | odd j ih => rw [gate,Op.refs_map,Op.refs_double]; exact ih.map (oddRef_injective _)
  | scale i => simp [gate,Op.refs]
  | @add k i => simp [gate,Op.refs,@evenRef_ne_scale k]
  | @sub k i => simp [gate,Op.refs,@evenRef_ne_scale k]

/-- Output ports are included, once each, in the bound. No input-copy gates are needed. -/
def fanout (k : ℕ) (r : Ref k) : ℕ :=
  (successors k r).length + if (outputIndex k r).isSome then 1 else 0

theorem fanout_bound (k : ℕ) (r : Ref k) : fanout k r ≤ 2 := by
  unfold fanout
  cases h : outputIndex k r with
  | none => simpa [h] using successors_bound k r
  | some i =>
      have hr := (outputIndex_some k r i).mp h
      rw [hr,successors_terminal]
      simp only [List.length_nil,Nat.zero_add]
      split_ifs <;> omega


@[reducible] def count : ℕ → ℕ
  | 0 => 0
  | k+1 => (count k + count k) + ((width k + width k) + width k)

theorem count_exact (k : ℕ) : 2*count k = 3*k*width k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [count,width]; nlinarith

def splitNodes (k : ℕ) : Node (k+1) ≃
    (Node k ⊕ Node k) ⊕ ((Fin (width k) ⊕ Fin (width k)) ⊕ Fin (width k)) where
  toFun
    | .even j => .inl (.inl j)
    | .odd j => .inl (.inr j)
    | .scale i => .inr (.inl (.inl i))
    | .add i => .inr (.inl (.inr i))
    | .sub i => .inr (.inr i)
  invFun
    | .inl (.inl j) => .even j
    | .inl (.inr j) => .odd j
    | .inr (.inl (.inl i)) => .scale i
    | .inr (.inl (.inr i)) => .add i
    | .inr (.inr i) => .sub i
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with (j|j)|((i|i)|i) <;> rfl

def emptyNode : Node 0 ≃ Fin 0 where
  toFun j := by cases j
  invFun := Fin.elim0
  left_inv j := by cases j
  right_inv j := Fin.elim0 j

def nodeFin : (k : ℕ) → Node k ≃ Fin (count k)
  | 0 => emptyNode
  | k+1 => (splitNodes k).trans
      ((Equiv.sumCongr (Equiv.sumCongr (nodeFin k) (nodeFin k))
        (Equiv.refl _)).trans
      ((Equiv.sumCongr finSumFinEquiv
        ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans
        finSumFinEquiv))

@[simp] theorem nodeFin_even {k : ℕ} (j : Node k) :
    (nodeFin (k+1) (.even j)).val = (nodeFin k j).val := rfl
@[simp] theorem nodeFin_odd {k : ℕ} (j : Node k) :
    (nodeFin (k+1) (.odd j)).val = count k + (nodeFin k j).val := rfl
@[simp] theorem nodeFin_scale {k : ℕ} (i : Fin (width k)) :
    (nodeFin (k+1) (.scale i)).val = (count k + count k) + i.val := rfl
@[simp] theorem nodeFin_add {k : ℕ} (i : Fin (width k)) :
    (nodeFin (k+1) (.add i)).val = (count k + count k) + (width k + i.val) := rfl
@[simp] theorem nodeFin_sub {k : ℕ} (i : Fin (width k)) :
    (nodeFin (k+1) (.sub i)).val = (count k + count k) + ((width k + width k) + i.val) := rfl

def refNat {k : ℕ} : Ref k → ℕ
  | .inl i => i.val
  | .inr j => width k + (nodeFin k j).val


theorem refNat_injective (k : ℕ) : Function.Injective (@refNat k) := by
  intro r s h
  cases r with
  | inl i => cases s with
    | inl j => exact congrArg Sum.inl (Fin.ext h)
    | inr j =>
        change i.val = width k + (nodeFin k j).val at h
        have := i.isLt
        omega
  | inr i => cases s with
    | inl j =>
        change width k + (nodeFin k i).val = j.val at h
        have := j.isLt
        omega
    | inr j =>
        apply congrArg Sum.inr
        apply (nodeFin k).injective
        apply Fin.ext
        change width k + (nodeFin k i).val = width k + (nodeFin k j).val at h
        omega


theorem refNat_bound {k : ℕ} (r : Ref k) : refNat r < width k + count k := by
  cases r with
  | inl i => exact i.isLt.trans_le (Nat.le_add_right _ _)
  | inr j => simp only [refNat]; exact Nat.add_lt_add_left (nodeFin k j).isLt _

theorem evenRef_before {k : ℕ} (r : Ref k) (j : Node k)
    (h : refNat r < width k + (nodeFin k j).val) :
    refNat (evenRef r) < width (k+1) + (nodeFin (k+1) (.even j)).val := by
  cases r with
  | inl i =>
      simp only [evenRef,refNat,RadixTwo.evenIndex,width]
      have := i.isLt
      omega
  | inr a =>
      change width (k+1) + (nodeFin k a).val < width (k+1) + (nodeFin k j).val
      change width k + (nodeFin k a).val < width k + (nodeFin k j).val at h
      omega

theorem oddRef_before {k : ℕ} (r : Ref k) (j : Node k)
    (h : refNat r < width k + (nodeFin k j).val) :
    refNat (oddRef r) < width (k+1) + (nodeFin (k+1) (.odd j)).val := by
  cases r with
  | inl i =>
      simp only [oddRef,refNat,RadixTwo.oddIndex,width]
      have := i.isLt
      omega
  | inr a =>
      change width (k+1) + (count k + (nodeFin k a).val) <
        width (k+1) + (count k + (nodeFin k j).val)
      change width k + (nodeFin k a).val < width k + (nodeFin k j).val at h
      omega

theorem evenRef_child_bound {k : ℕ} (r : Ref k) :
    refNat (evenRef r) < width (k+1) + (count k + count k) := by
  cases r with
  | inl i =>
      simp only [evenRef,refNat,RadixTwo.evenIndex,width]
      have := i.isLt
      omega
  | inr j =>
      change width (k+1) + (nodeFin k j).val < width (k+1) + (count k + count k)
      have := (nodeFin k j).isLt
      omega

theorem oddRef_child_bound {k : ℕ} (r : Ref k) :
    refNat (oddRef r) < width (k+1) + (count k + count k) := by
  cases r with
  | inl i =>
      simp only [oddRef,refNat,RadixTwo.oddIndex,width]
      have := i.isLt
      omega
  | inr j =>
      change width (k+1) + (count k + (nodeFin k j).val) <
        width (k+1) + (count k + count k)
      have := (nodeFin k j).isLt
      omega

/-- Every printed data operand strictly precedes its destination address. -/
theorem gate_refs_before {k : ℕ} (j : Node k) (r : Ref k) (h : r ∈ (gate j).refs) :
    refNat r < width k + (nodeFin k j).val := by
  induction j with
  | even j ih =>
      simp only [gate,Op.refs_map,Op.refs_double,List.mem_map] at h
      obtain ⟨r,hr,rfl⟩ := h
      exact evenRef_before r j (ih r hr)
  | odd j ih =>
      simp only [gate,Op.refs_map,Op.refs_double,List.mem_map] at h
      obtain ⟨r,hr,rfl⟩ := h
      exact oddRef_before r j (ih r hr)
  | @scale k i =>
      simp only [gate,Op.refs,List.mem_singleton] at h
      subst r
      exact (oddRef_child_bound (output k i)).trans_le (by change width (k+1)+(count k+count k) ≤ width (k+1)+((count k+count k)+i.val); omega)
  | @add k i =>
      simp only [gate,Op.refs,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact (evenRef_child_bound (output k i)).trans_le (by change width (k+1)+(count k+count k) ≤ width (k+1)+((count k+count k)+(width k+i.val)); omega)
      · change width (k+1)+((count k+count k)+i.val) <
          width (k+1)+((count k+count k)+(width k+i.val))
        have := width_pos k
        omega
  | @sub k i =>
      simp only [gate,Op.refs,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact (evenRef_child_bound (output k i)).trans_le (by change width (k+1)+(count k+count k) ≤ width (k+1)+((count k+count k)+((width k+width k)+i.val)); omega)
      · change width (k+1)+((count k+count k)+i.val) <
          width (k+1)+((count k+count k)+((width k+width k)+i.val))
        have := width_pos k
        omega

/-- Printed operations use only natural data addresses and prepared scalar slots. -/
def instruction (k : ℕ) (j : Fin (count k)) : Op ℕ :=
  (gate ((nodeFin k).symm j)).map refNat

def records (k : ℕ) : List (Op ℕ) :=
  (List.finRange (count k)).map (instruction k)

def outputs (k : ℕ) : List ℕ := (List.finRange (width k)).map (refNat ∘ output k)


theorem printed_refs_before (k : ℕ) (j : Fin (count k)) (r : ℕ)
    (h : r ∈ ((gate ((nodeFin k).symm j)).map refNat).refs) : r < width k + j.val := by
  rw [Op.refs_map,List.mem_map] at h
  obtain ⟨r,hr,rfl⟩ := h
  simpa only [Equiv.apply_symm_apply] using gate_refs_before ((nodeFin k).symm j) r hr

theorem records_length (k : ℕ) : (records k).length = count k := by simp [records]
theorem gate_count (k : ℕ) : (records k).length = 3*k*2^k/2 := by
  rw [records_length]
  have h := count_exact k
  rw [width_eq] at h
  omega

theorem outputs_length (k : ℕ) : (outputs k).length = width k := by simp [outputs]

/-- The coefficient bank is an actual shared root/rational arithmetic DAG. -/
def powers (k : ℕ) : UniformScalarPreparation.DAG 1 (width k) where
  length := UniformNewton.Preparation.productCount (width k)
  program := UniformNewton.Preparation.productProgram (width k)
  output j := UniformNewton.Preparation.productLift (Nat.le_of_lt j.isLt)
    (UniformNewton.Preparation.powerRef j.val)

theorem powers_admissible (k : ℕ) (omega : ℂ) :
    (powers k).Admissible (UniformNewton.Preparation.roots omega) :=
  UniformNewton.Preparation.productProgram_admissible omega _

theorem powers_run (k : ℕ) (omega : ℂ) (j : Fin (width k)) :
    (powers k).run (UniformNewton.Preparation.roots omega) (powers_admissible k omega) j =
      omega^j.val := by
  exact (UniformNewton.Preparation.productProgram_table omega (width k) j).1

theorem powers_length (k : ℕ) : (powers k).length = 5*width k+3 :=
  UniformNewton.Preparation.productCount_formula _

noncomputable def preparedBank (k : ℕ) (omega : ℂ) (c : ℕ) : ℂ :=
  if hc : c < width k then
    (powers k).run (UniformNewton.Preparation.roots omega) (powers_admissible k omega) ⟨c,hc⟩
  else 0

theorem preparedBank_eq (k : ℕ) (omega : ℂ) (c : ℕ) (h : c < width k) :
    preparedBank k omega c = omega^c := by
  rw [preparedBank,dite_eq_left h]
  exact powers_run _ _ _

noncomputable def Op.evalBank {α : Type} (bank : ℕ → ℂ) (v : α → ℂ) : Op α → ℂ
  | .add a b => v a+v b
  | .sub a b => v a-v b
  | .scale c a => bank c*v a

theorem Op.evalBank_map {α β : Type} (bank : ℕ → ℂ) (v : β → ℂ) (f : α → β)
    (g : Op α) : (g.map f).evalBank bank v = g.evalBank bank (v ∘ f) := by
  cases g <;> rfl

theorem Op.evalBank_eq {α : Type} (g : Op α) (omega : ℂ) (bank : ℕ → ℂ) (v : α → ℂ)
    (h : ∀ c ∈ g.scalars, bank c=omega^c) : g.evalBank bank v = g.eval omega v := by
  cases g with
  | add a b => rfl
  | sub a b => rfl
  | scale c a => rw [evalBank,eval,h c (by simp [scalars])]

theorem Op.evalBank_congr {α : Type} (g : Op α) (bank : ℕ → ℂ) (v w : α → ℂ)
    (h : ∀ r ∈ g.refs, v r=w r) : g.evalBank bank v = g.evalBank bank w := by
  cases g with
  | add a b => exact congrArg₂ (·+·) (h a (by simp [refs])) (h b (by simp [refs]))
  | sub a b => exact congrArg₂ (·-·) (h a (by simp [refs])) (h b (by simp [refs]))
  | scale c a => exact congrArg (bank c*·) (h a (by simp [refs]))

noncomputable def natValues (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (r : ℕ) : ℂ :=
  if h : r < width k then x ⟨r,h⟩
  else if h : r-width k < count k then
    values k omega x (.inr ((nodeFin k).symm ⟨r-width k,h⟩))
  else 0

theorem natValues_input (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (i : Fin (width k)) :
    natValues k omega x i.val = x i := by simp only [natValues,dite_eq_left i.isLt]

theorem natValues_node (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (j : Node k) :
    natValues k omega x (width k+(nodeFin k j).val) = values k omega x (.inr j) := by
  have hn : ¬width k+(nodeFin k j).val < width k := by omega
  rw [natValues,dite_eq_right hn,Nat.add_sub_cancel_left,dite_eq_left (nodeFin k j).isLt]
  change values k omega x (.inr ((nodeFin k).symm (nodeFin k j))) = _
  rw [Equiv.symm_apply_apply]

theorem natValues_ref (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (r : Ref k) :
    natValues k omega x (refNat r) = values k omega x r := by
  cases r with
  | inl i => exact (natValues_input k omega x i).trans (values_input k omega x i).symm
  | inr j => exact natValues_node k omega x j

/-- Actual printed instruction semantics with actually prepared scalars. -/
theorem printed_gate (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (j : Fin (count k)) :
    natValues k omega x (width k+j.val) =
      (instruction k j).evalBank (preparedBank k omega) (natValues k omega x) := by
  have h := natValues_node k omega x ((nodeFin k).symm j)
  simp only [Equiv.apply_symm_apply] at h
  rw [h,instruction,Op.evalBank_map]
  have hv : (natValues k omega x ∘ refNat) = values k omega x := by
    funext r
    exact natValues_ref k omega x r
  rw [hv,Op.evalBank_eq]
  · exact values_gate k omega x _
  · intro c hc
    exact preparedBank_eq k omega c (gate_scalar_bound _ c hc)

/-- Sequential execution reads only previously printed data registers. -/
noncomputable def runPrefix (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    (t : ℕ) → t ≤ count k → ℕ → ℂ
  | 0, _ => fun r => if h : r < width k then x ⟨r,h⟩ else 0
  | t+1, h =>
      let old := runPrefix k omega x t (by omega)
      Function.update old (width k+t)
        ((instruction k ⟨t,by omega⟩).evalBank (preparedBank k omega) old)

theorem runPrefix_correct (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (t : ℕ) (ht : t ≤ count k) (r : ℕ) (hr : r < width k+t) :
    runPrefix k omega x t ht r = natValues k omega x r := by
  induction t generalizing r with
  | zero => simp only [Nat.add_zero] at hr; simp only [runPrefix,natValues,dite_eq_left hr]
  | succ t ih =>
      let j : Fin (count k) := ⟨t,by omega⟩
      have he : (instruction k j).evalBank (preparedBank k omega)
          (runPrefix k omega x t (by omega)) =
          (instruction k j).evalBank (preparedBank k omega) (natValues k omega x) := by
        apply Op.evalBank_congr
        intro a ha
        exact ih (by omega) a (printed_refs_before k j a ha)
      by_cases heq : r=width k+t
      · subst r
        simp only [runPrefix,Function.update_self]
        exact he.trans (printed_gate k omega x j).symm
      · simp only [runPrefix,Function.update_of_ne heq]
        exact ih (by omega) r (by omega)

noncomputable def run (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    Fin (width k) → ℂ := fun i =>
  runPrefix k omega x (count k) (le_refl _) (refNat (output k i))

theorem run_fft (k : ℕ) (omega : ℂ) (hroot : IsPrimitiveRoot omega (width k))
    (x : Fin (width k) → ℂ) : run k omega x = RadixTwo.eval (width k) omega x := by
  have heq : run k omega x = eval k omega x := by
    funext i
    exact (runPrefix_correct k omega x (count k) (le_refl _) _
      (refNat_bound (output k i))).trans (natValues_ref k omega x (output k i))
  exact heq.trans (eval_fft k omega hroot x)


theorem run_specified (k : ℕ) (x : Fin (width k) → ℂ) :
    run k (zeta (width k)) x = (fourierMatrix (width k)).mulVec x := by
  have hroot : IsPrimitiveRoot (zeta (width k)) (width k) :=
    Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt (width_pos k))
  exact (run_fft k _ hroot x).trans (by rfl)

theorem instruction_scalar_bound (k : ℕ) (j : Fin (count k)) (c : ℕ)
    (hc : c ∈ (instruction k j).scalars) : c < width k := by
  rw [instruction,Op.scalars_map] at hc
  exact gate_scalar_bound _ c hc

theorem width_ge_height (k : ℕ) : k ≤ width k := by
  induction k with
  | zero => omega
  | succ k ih => have := width_pos k; simp only [width]; omega

theorem register_bound (k : ℕ) : width k+count k ≤ 4*(width k)^2 := by
  have hc := count_exact k
  have hk := width_ge_height k
  have hn := width_pos k
  nlinarith

/-- Every data address fits in at most 2k+2 bits. -/
theorem address_power_bound {k : ℕ} (r : Ref k) : refNat r < 2^(2*k+2) := by
  have h := (refNat_bound r).trans_le (register_bound k)
  rw [width_eq] at h
  have heq : 4*(2^k)^2 = 2^(2*k+2) := by
    rw [pow_add,show 2*k=k*2 by omega,pow_mul]
    norm_num
    ring
  exact h.trans_eq heq

/-- Preparation register counts are separate from charged data gates. -/
theorem preparation_register_bound (k : ℕ) : (powers k).length ≤ 2^(k+3) := by
  rw [powers_length,pow_add]
  have hn := width_pos k
  rw [← width_eq]
  norm_num
  omega


end ExactFourierCircuits.UniformRadixTwoDAG
