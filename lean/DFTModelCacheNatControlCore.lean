import ModelEquivalenceNat
import ModelEquivalenceInterpreter

set_option autoImplicit false

/-! A local, dense natural-state compiler. Dense updates are charged in full.
This is a preparation component, not a constant-overhead machine compiler. -/
namespace ExactFourierCircuits.DFTModelCacheNatControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Cell := p w w
abbrev Local := p w (p (a w) (a Cell))
abbrev LocalValue := ℕ × (Tape ℕ × Tape (ℕ × ℕ))

def pc : Prog false Local w := .atom .fst
def registers : Prog false Local (a w) := .comp (.atom .snd) (.atom .fst)
def heap : Prog false Local (a Cell) := .comp (.atom .snd) (.atom .snd)
def literal (v : ℕ) : Prog false Local w := .atom (.lit v)
def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def nextPC : Prog false Local w := nat .add pc (literal 1)
def read (i : ℕ) : Prog false Local w :=
  .comp (.fork registers (literal i)) (.atom .look)
def heapCell (address : ℕ) : Prog false Local Cell :=
  .comp (.fork heap (read address)) (.atom .look)
def heapPresence (address : ℕ) : Prog false Local w :=
  .comp (heapCell address) (.atom .fst)
def heapValue (address : ℕ) : Prog false Local w :=
  .comp (heapCell address) (.atom .snd)

def write (dst : ℕ) (value : Prog false Local w) : Prog false Local Local :=
  .fork nextPC (.fork
    (.comp (.fork (.fork registers (literal dst)) value)
      (ModelEquivalenceInterpreter.update w)) heap)
def jump (target : Prog false Local w) : Prog false Local Local :=
  .fork target (.atom .snd)
def binary (op : UniformMachine.NatOp) (dst left right : ℕ) : Prog false Local Local :=
  write dst (.comp (.fork (read left) (read right)) (ModelEquivalenceNat.natCode op))

/-- A missing source cell is rejected through validity, using the same prepared
inverse-of-zero guard as the existing natural division compiler. -/
def invalid : Prog false Local Local :=
  .comp (.fork (.atom .id)
    (.comp (.atom (.cz .scalar)) (.atom .inv))) (.atom .fst)
def load (dst address : ℕ) : Prog false Local Local :=
  .ifz (heapPresence address) invalid (write dst (heapValue address))
def store (address src : ℕ) : Prog false Local Local :=
  .fork nextPC (.fork registers
    (.comp (.fork (.fork heap (read address)) (.fork (literal 1) (read src)))
      (ModelEquivalenceInterpreter.update Cell)))
def branch (left right yes no : ℕ) : Prog false Local Local :=
  jump (.comp (.fork (read left) (read right)) (ModelEquivalenceNat.branchCode yes no))

inductive Instruction where
  | literal (dst value : ℕ)
  | binary (op : UniformMachine.NatOp) (dst left right : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | branch (left right yes no : ℕ)
  | jump (target : ℕ)
  | halt

def Instruction.native : Instruction → UniformMachine.Instruction
  | .literal d v => .natLiteral d v
  | .binary op d l r => .natBinary op d l r
  | .load d addr => .loadNat d addr
  | .store addr src => .storeNat addr src
  | .branch l r y n => .branchLT l r y n
  | .jump t => .jump t
  | .halt => .halt

def instruction : Instruction → Prog false Local Local
  | .literal d v => write d (literal v)
  | .binary op d l r => binary op d l r
  | .load d addr => load d addr
  | .store addr src => store addr src
  | .branch l r y n => branch l r y n
  | .jump t => jump (literal t)
  | .halt => .atom .id

def reg (v : LocalValue) (i : ℕ) := v.2.1.look i 0
def cell (v : LocalValue) (i : ℕ) := v.2.2.look i (0,0)
def put (v : LocalValue) (d x : ℕ) : LocalValue :=
  (v.1+1,(v.2.1.set d x,v.2.2))
def setPC (v : LocalValue) (t : ℕ) : LocalValue := (t,v.2)
def putHeap (v : LocalValue) (a x : ℕ) : LocalValue :=
  (v.1+1,(v.2.1,v.2.2.set a (1,x)))
def result (i : Instruction) (v : LocalValue) : LocalValue :=
  match i with
  | .literal d x => put v d x
  | .binary op d l r => put v d ((ModelEquivalenceNat.toUpstream op).run (reg v l,reg v r)).val
  | .load d addr => if (cell v (reg v addr)).1=0 then v else put v d (cell v (reg v addr)).2
  | .store addr src => putHeap v (reg v addr) (reg v src)
  | .branch l r y n => setPC v (if reg v l<reg v r then y else n)
  | .jump t => setPC v t
  | .halt => v

def Domain (i : Instruction) (v : LocalValue) : Prop :=
  match i with
  | .binary op _ l r => ModelEquivalenceNat.ValidOperands op (reg v l) (reg v r)
  | .load _ addr => (cell v (reg v addr)).1≠0
  | _ => True

theorem read_run (i : ℕ) (v : LocalValue) :
    run (read i) v=⟨reg v i,7,i,True⟩ := by
  simp [read,registers,literal,reg,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem heapPresence_run (address : ℕ) (v : LocalValue) :
    run (heapPresence address) v=⟨(cell v (reg v address)).1,15,address,True⟩ := by
  simp [heapPresence,heapCell,heap,read,registers,literal,cell,reg,
    run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,Cell]

theorem heapValue_run (address : ℕ) (v : LocalValue) :
    run (heapValue address) v=⟨(cell v (reg v address)).2,15,address,True⟩ := by
  simp [heapValue,heapCell,heap,read,registers,literal,cell,reg,
    run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,Cell]

theorem write_value (d : ℕ) (f : Prog false Local w) (v : LocalValue) :
    (run (write d f) v).val=put v d (run f v).val := by
  change (v.1+1,((run (ModelEquivalenceInterpreter.update w)
    ((v.2.1,d),(run f v).val)).val,v.2.2))=_
  rw [ModelEquivalenceInterpreter.update_value]
  rfl

theorem write_valid (d : ℕ) (f : Prog false Local w) (v : LocalValue) :
    (run (write d f) v).valid ↔ (run f v).valid := by
  have hu:=ModelEquivalenceInterpreter.update_valid w v.2.1 d (run f v).val
  simpa only [write,nextPC,nat,pc,literal,heap,registers,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,and_true,true_and] using
    (show (run f v).valid ∧ (run (ModelEquivalenceInterpreter.update w)
      ((v.2.1,d),(run f v).val)).valid ↔ (run f v).valid by simp only [hu,and_true])

theorem instruction_value (i : Instruction) (v : LocalValue) :
    (run (instruction i) v).val=result i v := by
  cases i with
  | literal d x => simpa only [instruction,result,literal,run,Code.run,Atom.run,Bill.word] using write_value d (literal x) v
  | binary op d l r =>
    rw [instruction,binary,write_value]
    change put v d (run (ModelEquivalenceNat.natCode op) (reg v l,reg v r)).val=_
    rw [ModelEquivalenceNat.natCode_value]
    rfl
  | load d a =>
    by_cases h:(cell v (reg v a)).1=0
    · simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,h,ite_true]
      simp only [invalid,result,h,ite_true,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    · change (run (load d a) v).val=_
      have hv:(run (heapPresence a) v).val=(cell v (reg v a)).1:=rfl
      simp only [load,run,Code.run,Bill.pass,Bill.pay,hv,h,ite_false]
      change (run (write d (heapValue a)) v).val=_
      rw [write_value]
      simp only [result,h,ite_false]
      rfl
  | store a s =>
    change (v.1+1,(v.2.1,(run (ModelEquivalenceInterpreter.update Cell)
      ((v.2.2,reg v a),(1,reg v s))).val))=_
    rw [ModelEquivalenceInterpreter.update_value]
    rfl
  | branch l r y n =>
    change ((run (ModelEquivalenceNat.branchCode y n) (reg v l,reg v r)).val,v.2)=_
    rw [ModelEquivalenceNat.branchCode_run]
    rfl
  | jump t | halt => rfl

theorem instruction_valid (i : Instruction) (v : LocalValue) :
    (run (instruction i) v).valid ↔ Domain i v := by
  cases i with
  | literal d x =>
    rw [instruction,write_valid]
    trivial
  | binary op d l r =>
    rw [instruction,binary,write_valid]
    simp only [run,Code.run,Bill.pass,Bill.pay]
    have h:=ModelEquivalenceNat.natCode_valid_iff op (reg v l) (reg v r)
    simp only [read_run,run] at *
    simpa [Domain,Bill.one] using h
  | load d a =>
    by_cases h:(cell v (reg v a)).1=0
    · simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,h,ite_true]
      simp [invalid,Domain,h,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    · have hv:(run (heapPresence a) v).val=(cell v (reg v a)).1:=rfl
      simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,hv,h,ite_false]
      have hw: (run (write d (heapValue a)) v).valid := (write_valid d (heapValue a) v).2 (by
        simp [heapValue,heapCell,heap,read,registers,literal,run,Code.run,Atom.run,
          Bill.one,Bill.word,Bill.pass,Bill.pay])
      simp [hw,Domain,h,heapPresence,heapCell,heap,read,registers,literal,Code.run,
        Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  | store a s =>
    have hu:=ModelEquivalenceInterpreter.update_valid Cell v.2.2 (reg v a) (1,reg v s)
    simpa [instruction,store,Domain,nextPC,nat,pc,registers,heap,read,literal,reg,
      run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank] using hu
  | branch l r y n =>
    change (run (branch l r y n) v).valid ↔ True
    have h:=ModelEquivalenceNat.branchCode_run (reg v l) (reg v r) y n
    simp only [branch,jump,run,Code.run,Bill.pass,Bill.pay,read_run]
    simp only [Atom.run,Bill.one,and_true,true_and]
    change (run (ModelEquivalenceNat.branchCode y n) (reg v l,reg v r)).valid ↔ True
    rw [h]
  | jump t =>
    change (True ∧ True ∧ True) ↔ True
    simp
  | halt => rfl

end
end ExactFourierCircuits.DFTModelCacheNatControl
