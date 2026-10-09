import OAI.Computability.FourierTransform.RAM
import UniformMachine

set_option autoImplicit false

/-! Concrete reverse-direction primitive lowering. This file does not claim a
compiler for arrays, pairs, control flow, or the whole upstream language. -/
namespace ExactFourierCircuits.ModelEquivalenceScalarLowering
open UniformMachine
namespace Source
abbrev Paint := OAI.PowerSaving.RAM.Paint
abbrev NOp := OAI.PowerSaving.RAM.NOp
abbrev Atom := OAI.PowerSaving.RAM.Atom
end Source
noncomputable section

/-- Static scalar registers must be prepared. A non-scalar register may also
contain an input-independent zero, so its dependence flag need not be true. -/
def Prepared : Source.Paint → Scalar → Prop
  | .scalar, a => a.dependent = false
  | _, _ => True

def Represents (paint : Source.Paint) (v : ℂ) (a : Scalar) : Prop :=
  a.value = v ∧ Prepared paint a

/-- The fixed primitive ABI writes result register 0 and scratch register 3.
All heap cells, output cells and root-request history are preserved. -/
structure Frame (s u : State) : Prop where
  natHeap : u.natHeap = s.natHeap
  scalarHeap : u.scalarHeap = s.scalarHeap
  outputs : u.outputs = s.outputs
  rootOrders : u.rootOrders = s.rootOrders
  natReg : ∀ i, i ≠ 0 → i ≠ 3 → u.natReg i = s.natReg i
  scalarReg : ∀ i, i ≠ 0 → i ≠ 3 → u.scalarReg i = s.scalarReg i

def reset (s : State) : State := { s with pc := 0 }

def Lowered (p : Program) (n B : ℕ) (x : Fin n → ℂ)
    (s : State) (ticks : ℕ) (u : State) : Prop :=
  BoundedExecution p n x B (reset s) ticks u ∧ Frame s u

theorem Frame.refl (s : State) : Frame s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (g : Frame u v) : Frame s v :=
  ⟨g.natHeap.trans h.natHeap,g.scalarHeap.trans h.scalarHeap,
   g.outputs.trans h.outputs,g.rootOrders.trans h.rootOrders,
   fun i h0 h3 => (g.natReg i h0 h3).trans (h.natReg i h0 h3),
   fun i h0 h3 => (g.scalarReg i h0 h3).trans (h.scalarReg i h0 h3)⟩

theorem Frame.reset (s : State) : Frame s (reset s) :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem Frame.writeNat (s : State) (d v : ℕ) (hd : d = 0 ∨ d = 3) :
    Frame s (writeNat s d v) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,fun _ _ _ => rfl⟩
  intro i h0 h3
  change Function.update s.natReg d v i = s.natReg i
  apply Function.update_of_ne
  intro hi
  rcases hd with h | h
  · exact h0 (hi.trans h)
  · exact h3 (hi.trans h)

theorem Frame.writeScalar (s : State) (d : ℕ) (v : Scalar) (hd : d = 0 ∨ d = 3) :
    Frame s (writeScalar s d v) := by
  refine ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl,?_⟩
  intro i h0 h3
  change Function.update s.scalarReg d v i = s.scalarReg i
  apply Function.update_of_ne
  intro hi
  rcases hd with h | h
  · exact h0 (hi.trans h)
  · exact h3 (hi.trans h)

theorem Frame.setPC (s : State) (pc : ℕ) : Frame s {s with pc := pc} :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem bound_setPC {s : State} {B pc : ℕ} (h : WordBound B s) (hp : pc ≤ B) :
    WordBound B {s with pc := pc} := ⟨hp,h.2⟩

theorem bound_writeNat {s : State} {B d v : ℕ} (h : WordBound B s)
    (hp : s.pc + 1 ≤ B) (hv : v ≤ B) : WordBound B (writeNat s d v) := by
  refine ⟨hp,?_,h.2.2⟩
  intro i
  by_cases hi : i = d
  · subst i; simpa [writeNat] using hv
  · simpa [writeNat,Function.update,hi] using h.2.1 i

theorem bound_writeScalar {s : State} {B d : ℕ} {v : Scalar} (h : WordBound B s)
    (hp : s.pc + 1 ≤ B) : WordBound B (writeScalar s d v) := ⟨hp,h.2⟩

def fieldProgram (op : FieldOp) : Program := [.fieldBinary op 0 1 2,.halt]
def scalarProgram (v : ℚ) : Program := [.scalarLiteral 0 v,.halt]
def literalProgram (v : ℕ) : Program := [.natLiteral 0 v,.halt]
def inverseProgram : Program := [.scalarLiteral 3 1,.fieldBinary .div 0 3 1,.halt]

theorem field_execution {n B : ℕ} {x : Fin n → ℂ} {s : State} {op : FieldOp}
    {v : Scalar} (bound : WordBound B s) (hb : 1 ≤ B)
    (eval : evalField op (s.scalarReg 1) (s.scalarReg 2) = some v) :
    Lowered (fieldProgram op) n B x s 2 (writeScalar (reset s) 0 v) := by
  refine ⟨.next (bound_setPC bound (by omega)) ?_ (.halt ?_ ?_),
    (Frame.reset s).trans (Frame.writeScalar _ 0 v (Or.inl rfl))⟩
  · simp [step,fieldProgram,reset,eval]
  · exact bound_writeScalar (bound_setPC bound (by omega)) hb
  · simp [step,fieldProgram,writeScalar,next,reset]

theorem scalar_execution {n B : ℕ} {x : Fin n → ℂ} {s : State} (v : ℚ)
    (bound : WordBound B s) (hb : 1 ≤ B) :
    Lowered (scalarProgram v) n B x s 2 (writeScalar (reset s) 0 ⟨v,false⟩) := by
  refine ⟨.next (bound_setPC bound (by omega)) ?_ (.halt ?_ ?_),
    (Frame.reset s).trans (Frame.writeScalar _ 0 _ (Or.inl rfl))⟩
  · simp [step,scalarProgram,reset]
  · exact bound_writeScalar (bound_setPC bound (by omega)) hb
  · simp [step,scalarProgram,writeScalar,next,reset]

theorem literal_execution {n B : ℕ} {x : Fin n → ℂ} {s : State} {v : ℕ}
    (bound : WordBound B s) (hb : 1 ≤ B) (hv : v ≤ B) :
    Lowered (literalProgram v) n B x s 2 (writeNat (reset s) 0 v) := by
  refine ⟨.next (bound_setPC bound (by omega)) ?_ (.halt ?_ ?_),
    (Frame.reset s).trans (Frame.writeNat _ 0 _ (Or.inl rfl))⟩
  · simp [step,literalProgram,reset]
  · exact bound_writeNat (bound_setPC bound (by omega)) hb hv
  · simp [step,literalProgram,writeNat,next,reset]

/-- A single literal macro implements upstream's scalar zero at every paint. -/
theorem zero_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State} (paint : Source.Paint)
    (bound : WordBound B s) (hb : 1 ≤ B) :
    ∃ u, Lowered (scalarProgram 0) n B x s 2 u ∧ Represents paint 0 (u.scalarReg 0) := by
  refine ⟨_,scalar_execution 0 bound hb,?_⟩
  cases paint <;> simp [Represents,Prepared,writeScalar]

theorem one_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (bound : WordBound B s) (hb : 1 ≤ B) :
    ∃ u, Lowered (scalarProgram 1) n B x s 2 u ∧ Represents .scalar 1 (u.scalarReg 0) := by
  refine ⟨_,scalar_execution 1 bound hb,?_⟩
  simp [Represents,Prepared,writeScalar]

theorem add_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (paint : Source.Paint) (a b : ℂ)
    (ha : Represents paint a (s.scalarReg 1)) (hb : Represents paint b (s.scalarReg 2))
    (bound : WordBound B s) (capacity : 1 ≤ B) :
    ∃ u, Lowered (fieldProgram .add) n B x s 2 u ∧
      Represents paint ((OAI.PowerSaving.RAM.Atom.add paint : Source.Atom false _ _).run (a,b)).val
        (u.scalarReg 0) := by
  refine ⟨_,field_execution bound capacity rfl,?_⟩
  cases paint <;> simp_all [Represents,Prepared,OAI.PowerSaving.RAM.Atom.run,
    OAI.PowerSaving.RAM.Bill.one,writeScalar]

theorem sub_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (paint : Source.Paint) (a b : ℂ)
    (ha : Represents paint a (s.scalarReg 1)) (hb : Represents paint b (s.scalarReg 2))
    (bound : WordBound B s) (capacity : 1 ≤ B) :
    ∃ u, Lowered (fieldProgram .sub) n B x s 2 u ∧
      Represents paint ((OAI.PowerSaving.RAM.Atom.sub paint : Source.Atom false _ _).run (a,b)).val
        (u.scalarReg 0) := by
  refine ⟨_,field_execution bound capacity rfl,?_⟩
  cases paint <;> simp_all [Represents,Prepared,OAI.PowerSaving.RAM.Atom.run,
    OAI.PowerSaving.RAM.Bill.one,writeScalar]

theorem scale_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (paint : Source.Paint) (a b : ℂ)
    (ha : Represents .scalar a (s.scalarReg 1)) (hb : Represents paint b (s.scalarReg 2))
    (bound : WordBound B s) (capacity : 1 ≤ B) :
    ∃ u, Lowered (fieldProgram .mul) n B x s 2 u ∧
      Represents paint ((OAI.PowerSaving.RAM.Atom.scale paint : Source.Atom false _ _).run (a,b)).val
        (u.scalarReg 0) := by
  have prepared : (s.scalarReg 1).dependent = false := ha.2
  have ev : evalField .mul (s.scalarReg 1) (s.scalarReg 2) =
      some ⟨(s.scalarReg 1).value*(s.scalarReg 2).value,(s.scalarReg 2).dependent⟩ := by
    simp [evalField,prepared]
  refine ⟨_,field_execution bound capacity ev,?_⟩
  cases paint <;> simp_all [Represents,Prepared,OAI.PowerSaving.RAM.Atom.run,
    OAI.PowerSaving.RAM.Bill.one,writeScalar]

theorem inverse_lowering {n B : ℕ} {x : Fin n → ℂ} {s : State} (a : ℂ)
    (ha : Represents .scalar a (s.scalarReg 1))
    (valid : ((OAI.PowerSaving.RAM.Atom.inv : Source.Atom false _ _).run a).valid)
    (bound : WordBound B s) (capacity : 2 ≤ B) :
    ∃ u, Lowered inverseProgram n B x s 3 u ∧
      Represents .scalar ((OAI.PowerSaving.RAM.Atom.inv : Source.Atom false _ _).run a).val
        (u.scalarReg 0) := by
  have nonzero : a ≠ 0 := valid
  have prepared : (s.scalarReg 1).dependent = false := ha.2
  let u := writeScalar (writeScalar (reset s) 3 ⟨1,false⟩) 0 ⟨a⁻¹,false⟩
  have b0 := bound_setPC bound (show 0 ≤ B by omega)
  have b1 := bound_writeScalar (d:=3) (v:=⟨1,false⟩) b0 (show (reset s).pc+1≤B by dsimp [reset]; omega)
  have b2 := bound_writeScalar (d:=0) (v:=⟨a⁻¹,false⟩) b1
    (show (writeScalar (reset s) 3 ⟨1,false⟩).pc+1≤B by dsimp [writeScalar,next,reset]; omega)
  refine ⟨u,⟨.next b0 ?_ (.next b1 ?_ (.halt b2 ?_)),
    ((Frame.reset s).trans (Frame.writeScalar _ 3 _ (Or.inr rfl))).trans
      (Frame.writeScalar _ 0 _ (Or.inl rfl))⟩,?_⟩
  · simp [step,inverseProgram,reset]
  · simp [step,inverseProgram,u,writeScalar,next,reset,evalField,ha.1,prepared,nonzero,one_div]
  · simp [step,inverseProgram,u,writeScalar,next,reset]
  · simp [u,Represents,Prepared,writeScalar,OAI.PowerSaving.RAM.Atom.run]

/-- Every upstream scalar arithmetic atom has work one. The macros above use
at most three concrete instructions, including their terminal halt. -/
theorem scalar_cost (paint : Source.Paint) (a b : ℂ) :
    ((OAI.PowerSaving.RAM.Atom.add paint : Source.Atom false _ _).run (a,b)).work = 1 ∧
    ((OAI.PowerSaving.RAM.Atom.sub paint : Source.Atom false _ _).run (a,b)).work = 1 ∧
    ((OAI.PowerSaving.RAM.Atom.scale paint : Source.Atom false _ _).run (a,b)).work = 1 ∧
    ((OAI.PowerSaving.RAM.Atom.inv : Source.Atom false _ _).run a).work = 1 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Precisely the scalar arithmetic fragment being compiled, in false mode.
The zero and one operations ignore a word input; their concrete macros also
implement the corresponding polymorphic atoms at any source input type. -/
inductive Primitive where
  | zero (paint : Source.Paint)
  | one
  | add (paint : Source.Paint)
  | sub (paint : Source.Paint)
  | scale (paint : Source.Paint)
  | inverse

namespace Primitive
open OAI.PowerSaving.RAM (Ty)

def input : Primitive → Ty
  | .zero _ | .one => .w
  | .add t | .sub t => .p (.c t) (.c t)
  | .scale t => .p (.c .scalar) (.c t)
  | .inverse => .c .scalar

def paint : Primitive → Source.Paint
  | .zero t | .add t | .sub t | .scale t => t
  | .one | .inverse => .scalar

def atom : (op : Primitive) → Source.Atom false op.input (.c op.paint)
  | .zero t => .cz t
  | .one => .cone
  | .add t => .add t
  | .sub t => .sub t
  | .scale t => .scale t
  | .inverse => .inv

def program : Primitive → Program
  | .zero _ => scalarProgram 0
  | .one => scalarProgram 1
  | .add _ => fieldProgram .add
  | .sub _ => fieldProgram .sub
  | .scale _ => fieldProgram .mul
  | .inverse => inverseProgram

def inputRep : (op : Primitive) → op.input.T → State → Prop
  | .zero _, _, _ => True
  | .one, _, _ => True
  | .add t, v, s => Represents t v.1 (s.scalarReg 1) ∧ Represents t v.2 (s.scalarReg 2)
  | .sub t, v, s => Represents t v.1 (s.scalarReg 1) ∧ Represents t v.2 (s.scalarReg 2)
  | .scale t, v, s => Represents .scalar v.1 (s.scalarReg 1) ∧ Represents t v.2 (s.scalarReg 2)
  | .inverse, v, s => Represents .scalar v (s.scalarReg 1)

theorem length_le (op : Primitive) : op.program.length ≤ 3 := by
  cases op <;> simp [program,fieldProgram,scalarProgram,inverseProgram]

/-- Actual bounded UniformMachine execution of every compiled scalar primitive,
with value/type simulation, storage frames and uniform constant work overhead.
The count includes halt; removing the terminal halt only reduces that cost. -/
theorem compile_correct (op : Primitive) {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (v : op.input.T) (input : op.inputRep v s) (valid : (op.atom.run v).valid)
    (bound : WordBound B s) (capacity : 2 ≤ B) :
    ∃ ticks u, Lowered op.program n B x s ticks u ∧
      Represents op.paint (op.atom.run v).val (u.scalarReg 0) ∧
      ticks ≤ 3 * (op.atom.run v).work := by
  cases op with
  | zero t =>
      obtain ⟨u,run,value⟩ := zero_lowering t bound (by omega)
      exact ⟨2,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run,OAI.PowerSaving.RAM.Bill.one]⟩
  | one =>
      obtain ⟨u,run,value⟩ := one_lowering bound (by omega)
      exact ⟨2,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run,OAI.PowerSaving.RAM.Bill.one]⟩
  | add t =>
      rcases v with ⟨a,b⟩
      obtain ⟨u,run,value⟩ := add_lowering t a b input.1 input.2 bound (by omega)
      exact ⟨2,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run,OAI.PowerSaving.RAM.Bill.one]⟩
  | sub t =>
      rcases v with ⟨a,b⟩
      obtain ⟨u,run,value⟩ := sub_lowering t a b input.1 input.2 bound (by omega)
      exact ⟨2,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run,OAI.PowerSaving.RAM.Bill.one]⟩
  | scale t =>
      rcases v with ⟨a,b⟩
      obtain ⟨u,run,value⟩ := scale_lowering t a b input.1 input.2 bound (by omega)
      exact ⟨2,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run,OAI.PowerSaving.RAM.Bill.one]⟩
  | inverse =>
      obtain ⟨u,run,value⟩ := inverse_lowering v input valid bound capacity
      exact ⟨3,u,run,value,by simp [atom,OAI.PowerSaving.RAM.Atom.run]⟩

end Primitive

/-- Reverse integer lowering retains upstream's total division/modulo semantics.
A genuine zero test avoids UniformMachine's partial integer instructions. -/
def natProgram : Source.NOp → Program
  | .add => [.natBinary .add 0 1 2,.halt]
  | .sub => [.natBinary .sub 0 1 2,.halt]
  | .mul => [.natBinary .mul 0 1 2,.halt]
  | .div => [.natLiteral 3 0,.branchLT 3 2 4 2,.natLiteral 0 0,.jump 5,
      .natBinary .div 0 1 2,.halt]
  | .mod => [.natLiteral 3 0,.branchLT 3 2 4 2,.natBinary .add 0 1 3,.jump 5,
      .natBinary .mod 0 1 2,.halt]
  | .lt => [.branchLT 1 2 3 1,.natLiteral 0 0,.jump 4,.natLiteral 0 1,.halt]

def quotientProgram (op : NatOp) (remainder : Bool) : Program :=
  [.natLiteral 3 0,.branchLT 3 2 4 2,
   if remainder then .natBinary .add 0 1 3 else .natLiteral 0 0,
   .jump 5,.natBinary op 0 1 2,.halt]

theorem nat_execution {n B : ℕ} {x : Fin n → ℂ} {s : State} {op : NatOp} {v : ℕ}
    (bound : WordBound B s) (capacity : 1 ≤ B) (hv : v ≤ B)
    (eval : evalNat op (s.natReg 1) (s.natReg 2) = some v) :
    Lowered [.natBinary op 0 1 2,.halt] n B x s 2 (writeNat (reset s) 0 v) := by
  refine ⟨.next (bound_setPC bound (by omega)) ?_ (.halt ?_ ?_),
    (Frame.reset s).trans (Frame.writeNat _ 0 v (Or.inl rfl))⟩
  · simp [step,reset,eval]
  · exact bound_writeNat (bound_setPC bound (by omega)) capacity hv
  · simp [step,writeNat,next,reset]

theorem quotient_execution {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (op : NatOp) (remainder : Bool) (v : ℕ)
    (bound : WordBound B s) (capacity : 5 ≤ B) (hv : v ≤ B)
    (positive : s.natReg 2 ≠ 0 → evalNat op (s.natReg 1) (s.natReg 2) = some v)
    (zero : s.natReg 2 = 0 → v = if remainder then s.natReg 1 else 0) :
    ∃ ticks u, Lowered (quotientProgram op remainder) n B x s ticks u ∧
      u.natReg 0 = v ∧ ticks ≤ 5 := by
  let s0 := reset s
  let s1 := writeNat s0 3 0
  have b0 : WordBound B s0 := bound_setPC bound (by omega)
  have b1 : WordBound B s1 := bound_writeNat b0
    (show s0.pc+1≤B by dsimp [s0,reset]; omega) (by omega)
  by_cases hzero : s.natReg 2 = 0
  · let s2 : State := {s1 with pc:=2}
    let s3 := writeNat s2 0 v
    let s4 : State := {s3 with pc:=5}
    have b2 : WordBound B s2 := bound_setPC b1 (by omega)
    have b3 : WordBound B s3 := bound_writeNat b2
      (show s2.pc+1≤B by dsimp [s2]; omega) hv
    have b4 : WordBound B s4 := bound_setPC b3 (by omega)
    refine ⟨5,s4,⟨.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.next b3 ?_ (.halt b4 ?_)))),
      ((((Frame.reset s).trans (Frame.writeNat _ 3 0 (Or.inr rfl))).trans
        (Frame.setPC _ 2)).trans (Frame.writeNat _ 0 v (Or.inl rfl))).trans
        (Frame.setPC _ 5)⟩,?_,by omega⟩
    · simp [step,quotientProgram,s0,s1,reset]
    · simp [step,quotientProgram,s0,s1,s2,writeNat,next,reset,hzero]
    · cases remainder <;> simp [step,quotientProgram,s2,s3,s1,s0,writeNat,next,reset,
        evalNat,zero hzero]
    · simp [step,quotientProgram,s3,s4,s2,writeNat,next]
    · simp [step,quotientProgram,s4]
    · simp [s4,s3,writeNat]
  · have hp : 0 < s.natReg 2 := Nat.pos_of_ne_zero hzero
    let s2 : State := {s1 with pc:=4}
    let s3 := writeNat s2 0 v
    have b2 : WordBound B s2 := bound_setPC b1 (by omega)
    have b3 : WordBound B s3 := bound_writeNat b2
      (show s2.pc+1≤B by dsimp [s2]; omega) hv
    refine ⟨4,s3,⟨.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.halt b3 ?_))),
      (((Frame.reset s).trans (Frame.writeNat _ 3 0 (Or.inr rfl))).trans
        (Frame.setPC _ 4)).trans (Frame.writeNat _ 0 v (Or.inl rfl))⟩,?_,by omega⟩
    · simp [step,quotientProgram,s0,s1,reset]
    · simp [step,quotientProgram,s0,s1,s2,writeNat,next,reset,hp]
    · simp [step,quotientProgram,s2,s3,s1,s0,writeNat,next,reset,positive hzero]
    · simp [step,quotientProgram,s3,s2,writeNat,next]
    · simp [s3,writeNat]

theorem less_execution {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (bound : WordBound B s) (capacity : 4 ≤ B) :
    ∃ ticks u, Lowered (natProgram .lt) n B x s ticks u ∧
      u.natReg 0 = (if s.natReg 1 < s.natReg 2 then 1 else 0) ∧ ticks ≤ 4 := by
  let s0 := reset s
  have b0 : WordBound B s0 := bound_setPC bound (by omega)
  by_cases h : s.natReg 1 < s.natReg 2
  · let s1 : State := {s0 with pc:=3}
    let s2 := writeNat s1 0 1
    have b1 : WordBound B s1 := bound_setPC b0 (by omega)
    have b2 : WordBound B s2 := bound_writeNat b1
      (show s1.pc+1≤B by dsimp [s1]; omega) (by omega)
    refine ⟨3,s2,⟨.next b0 ?_ (.next b1 ?_ (.halt b2 ?_)),
      ((Frame.reset s).trans (Frame.setPC _ 3)).trans (Frame.writeNat _ 0 1 (Or.inl rfl))⟩,?_,by omega⟩
    · simp [step,natProgram,s0,s1,reset,h]
    · simp [step,natProgram,s1,s2]
    · simp [step,natProgram,s2,s1,writeNat,next]
    · simp [s2,writeNat,h]
  · let s1 : State := {s0 with pc:=1}
    let s2 := writeNat s1 0 0
    let s3 : State := {s2 with pc:=4}
    have b1 : WordBound B s1 := bound_setPC b0 (by omega)
    have b2 : WordBound B s2 := bound_writeNat b1
      (show s1.pc+1≤B by dsimp [s1]; omega) (by omega)
    have b3 : WordBound B s3 := bound_setPC b2 (by omega)
    refine ⟨4,s3,⟨.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.halt b3 ?_))),
      (((Frame.reset s).trans (Frame.setPC _ 1)).trans
        (Frame.writeNat _ 0 0 (Or.inl rfl))).trans (Frame.setPC _ 4)⟩,?_,by omega⟩
    · simp [step,natProgram,s0,s1,reset,h]
    · simp [step,natProgram,s1,s2]
    · simp [step,natProgram,s2,s3,s1,writeNat,next]
    · simp [step,natProgram,s3]
    · simp [s3,s2,writeNat,h]

theorem nat_cost (op : Source.NOp) (a b : ℕ) : (op.run (a,b)).work = 1 := by
  cases op <;> rfl

theorem nat_peak (op : Source.NOp) (a b : ℕ) : (op.run (a,b)).peak = (op.run (a,b)).val := by
  cases op <;> rfl

/-- All six upstream total integer operations lower to real bounded executions.
This includes division by zero (result zero), modulo zero (result numerator),
and comparison; no successful-domain restriction is imposed on the input. -/
theorem nat_compile_correct (op : Source.NOp) {n B : ℕ} {x : Fin n → ℂ} {s : State}
    (bound : WordBound B s) (capacity : 5 ≤ B)
    (peak : (op.run (s.natReg 1,s.natReg 2)).peak ≤ B) :
    ∃ ticks u, Lowered (natProgram op) n B x s ticks u ∧
      u.natReg 0 = (op.run (s.natReg 1,s.natReg 2)).val ∧
      ticks ≤ 5 * (op.run (s.natReg 1,s.natReg 2)).work := by
  have hv := (nat_peak op (s.natReg 1) (s.natReg 2)) ▸ peak
  cases op with
  | add =>
      refine ⟨2,_,nat_execution bound (by omega) hv rfl,?_,?_⟩
      · simp [writeNat,OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
      · simp [OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
  | sub =>
      refine ⟨2,_,nat_execution bound (by omega) hv rfl,?_,?_⟩
      · simp [writeNat,OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
      · simp [OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
  | mul =>
      refine ⟨2,_,nat_execution bound (by omega) hv rfl,?_,?_⟩
      · simp [writeNat,OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
      · simp [OAI.PowerSaving.RAM.NOp.run,OAI.PowerSaving.RAM.Bill.word]
  | div =>
      obtain ⟨ticks,u,run,value,cheap⟩ := quotient_execution .div false
        (s.natReg 1/s.natReg 2) bound capacity hv
        (fun h => by simp [evalNat,h]) (fun h => by simp [h])
      exact ⟨ticks,u,run,value,by simpa [nat_cost] using cheap⟩
  | mod =>
      obtain ⟨ticks,u,run,value,cheap⟩ := quotient_execution .mod true
        (s.natReg 1%s.natReg 2) bound capacity hv
        (fun h => by simp [evalNat,h]) (fun h => by simp [h])
      exact ⟨ticks,u,run,value,by simpa [nat_cost] using cheap⟩
  | lt =>
      obtain ⟨ticks,u,run,value,cheap⟩ := less_execution bound (by omega)
      exact ⟨ticks,u,run,value,by simpa [nat_cost] using cheap.trans (by omega : 4 ≤ 5)⟩

end
end ExactFourierCircuits.ModelEquivalenceScalarLowering
