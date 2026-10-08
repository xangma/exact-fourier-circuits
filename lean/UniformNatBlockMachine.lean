import UniformNatCopyMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformNatBlockMachine
open UniformMachine
noncomputable section

/-- A proof assembler for the existing Nat alphabet; no new RAM instruction. -/
inductive Op where
 | literal (dst value : ℕ)
 | binary (op : NatOp) (dst left right : ℕ)
 | load (dst address : ℕ)
 | store (address src : ℕ)
 deriving DecidableEq

def Op.code : Op→Instruction
 | .literal d v => .natLiteral d v
 | .binary o d l r => .natBinary o d l r
 | .load d a => .loadNat d a
 | .store a r => .storeNat a r

def Op.apply : Op→State→State
 | .literal d v,s => writeNat s d v
 | .binary o d l r,s => writeNat s d ((evalNat o (s.natReg l) (s.natReg r)).getD 0)
 | .load d a,s => writeNat s d ((s.natHeap (s.natReg a)).getD 0)
 | .store a r,s => {next s with natHeap:=Function.update s.natHeap (s.natReg a) (some (s.natReg r))}

def Op.readable : Op→State→Prop
 | .binary o _ l r,s => (evalNat o (s.natReg l) (s.natReg r)).isSome=true
 | .load _ a,s => (s.natHeap (s.natReg a)).isSome=true
 | _,_ => True

def Op.peak : Op→State→ℕ
 | .literal _ v,_ => v
 | .binary o _ l r,s => (evalNat o (s.natReg l) (s.natReg r)).getD 0
 | .load _ a,s => max (s.natReg a) ((s.natHeap (s.natReg a)).getD 0)
 | .store a r,s => max (s.natReg a) (s.natReg r)

def applyBlock : List Op→State→State
 | [],s => s
 | o::b,s => applyBlock b (o.apply s)
def readable : List Op→State→Prop
 | [],_ => True
 | o::b,s => o.readable s ∧ readable b (o.apply s)
def peak : List Op→State→ℕ
 | [],_ => 0
 | o::b,s => max (o.peak s) (peak b (o.apply s))
def BlockAt (b : List Op) (p : Program) (base : ℕ) : Prop :=
 ∀i,(hi:i<b.length)→p[base+i]?=some (b[i]'hi).code

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl

theorem Op.step (o : Op) (p : Program) (n : ℕ) (x : Fin n→ℂ) (s : State)
 (hc : p[s.pc]?=some o.code) (hr : o.readable s) : step p n x s=.running (o.apply s) := by
 cases o with
 | literal d v => simp [UniformMachine.step,hc,Op.code,Op.apply]
 | binary op d l r =>
   cases h:evalNat op (s.natReg l) (s.natReg r) with
   | none => simp [Op.readable,h] at hr
   | some v => simp [UniformMachine.step,hc,Op.code,Op.apply,h]
 | load d a =>
   cases h:s.natHeap (s.natReg a) with
   | none => simp [Op.readable,h] at hr
   | some v => simp [UniformMachine.step,hc,Op.code,Op.apply,h]
 | store a r => simp [UniformMachine.step,hc,Op.code,Op.apply]

theorem Op.bound (o : Op) (B : ℕ) (s : State) (hs : WordBound B s)
 (hp : s.pc+1≤B) (hv : o.peak s≤B) : WordBound B (o.apply s) := by
 cases o with
 | literal d v => exact writeNat_bound B s d v hs hp hv
 | binary op d l r => exact writeNat_bound B s d _ hs hp hv
 | load d a => exact writeNat_bound B s d _ hs hp ((le_max_right _ _).trans hv)
 | store a r =>
   exact UniformNatCopyMachine.store_bound B s (s.natReg a) (s.natReg r) hs hp
    ((le_max_left _ _).trans hv) ((le_max_right _ _).trans hv)

theorem block_runs (b : List Op) (p : Program) (base n B : ℕ) (x : Fin n→ℂ)
 (s : State) (code : BlockAt b p base) (pc : s.pc=base) (bound : WordBound B s)
 (extent : base+b.length≤B) (reads : readable b s) (values : peak b s≤B) :
 BoundedRuns p n x B s b.length (applyBlock b s) := by
 induction b generalizing base s with
 | nil => exact .refl bound
 | cons o b ih =>
   have opBound:=o.bound B s bound (by simp only [List.length_cons] at extent;omega)
    ((le_max_left _ _).trans values)
   have tailCode : BlockAt b p (base+1) := by
    intro i hi
    have h:=code (i+1) (by simpa using hi)
    change p[base+(i+1)]?=some (b[i]'hi).code at h
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
   have tail:=ih (base+1) (o.apply s) tailCode (by rw [Op.apply_pc,pc]) opBound
     (by simp only [List.length_cons] at extent;omega) reads.2 ((le_max_right _ _).trans values)
   have head:=code 0 (by simp)
   change p[base]?=some o.code at head
   exact .next bound (o.step p n x s (by simpa [pc] using head) reads.1) tail

end
end ExactFourierCircuits.UniformNatBlockMachine
