import UniformGlobalDiagonalPhasePreparation
import UniformGlobalTensorDiagonalLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
/-- Physical two-cell(radix,pool) directory; prefix placement is computed by
this literal loop. No prepared tensor rows or permutation bank is an input. -/
def boot:List Op:=[.literal 4590 0,.literal 4591 1,.literal 4592 2,.literal 4593 0,.literal 4595 0]
def setup:List Op:=[.mul 4594 4593 4592,.add 4594 4581 4594,.getNat 4380 4594,
 .add 4594 4594 4591,.getNat 4381 4594,.add 4382 4582 4590,
 .add 4383 4584 4595,.add 4384 4585 4595,.add 4385 4583 4590,.add 4386 4593 4590]
def finish:List Op:=[.add 4595 4595 4380,.add 4593 4593 4591]
def program:Program:=boot.map Op.code++[.branchLT 4593 4580 6 48]++setup.map Op.code++
 UniformGlobalDiagonalPhasePreparation.program.map (relocate 16 45)++finish.map Op.code++[.jump 5,.halt]
lemma program_length:program.length=49:=by
 simp only[program,List.length_append,List.length_map,UniformGlobalDiagonalPhasePreparation.program_length,
  List.length_cons,List.length_nil];rfl
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i < 5 at hi;interval_cases i <;>rfl
lemma setup_code:BlockAt setup program 6:=by
 intro i hi;change i < 10 at hi;interval_cases i <;>rfl
lemma row_code:CodeAt UniformGlobalDiagonalPhasePreparation.program program 16 45:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 4593 4580 6 48]++setup.map Op.code)
  (finish.map Op.code++[.jump 5,.halt]) _ 16 45 rfl
lemma finish_code:BlockAt finish program 45:=by
 intro i hi;change i < 2 at hi;interval_cases i <;>rfl
lemma branch_at:program[5]?=some (.branchLT 4593 4580 6 48):=rfl
lemma jump_at:program[47]?=some (.jump 5):=rfl
lemma halt_at:program[48]?=some .halt:=rfl
noncomputable section
structure Entry where
 radix:ℕ
 positive:0 < radix
 pool:ℕ
 value:Fin 9→Fin radix→ℂ

def amount (as:List Entry):ℕ:=(as.map Entry.radix).sum
def axis (lane:Fin 9) (P C o:ℕ) (a:Entry):Axis where
 radix:=a.radix
 positive:=a.positive
 permutation:=Equiv.refl _
 coefficient:=a.value lane
 permutationBase:=P+o
 coefficientBase:=C+o
def axes (lane:Fin 9) (P C:ℕ):ℕ→List Entry→List Axis
 | _,[]=>[]
 | o,a::as=>axis lane P C o a::axes lane P C (o+a.radix) as
lemma axes_length (lane:Fin 9) (P C o:ℕ) (as:List Entry):
 (axes lane P C o as).length=as.length:=by
 induction as generalizing o with
 | nil=>rfl
 | cons a as ih=>simp only[axes,List.length_cons,ih]
lemma axes_radices (lane:Fin 9) (P C o:ℕ) (as:List Entry):
 radices (axes lane P C o as)=as.map Entry.radix:=by
 induction as generalizing o with
 | nil=>rfl
 | cons a as ih=>
   change a.radix::radices (axes lane P C (o+a.radix) as)=_
   rw[ih];rfl
structure Layout where
 B:ℕ
 ell:ℕ
 directory:ℕ
 rows:ℕ
 permutation:ℕ
 coefficient:ℕ
 total:ℕ
 code:49 ≤ B
 directoryBelow:directory+2*ell ≤ rows
 rowsBelow:rows+3*ell ≤ permutation
 permutationBound:permutation+total ≤ B
 coefficientBound:coefficient+total ≤ B

structure Header (L:Layout) (lane:Fin 9) (s:State):Prop where
 count:s.natReg 4580=L.ell
 directory:s.natReg 4581=L.directory
 lane:s.natReg 4582=lane.val
 rows:s.natReg 4583=L.rows
 permutation:s.natReg 4584=L.permutation
 coefficient:s.natReg 4585=L.coefficient
structure Cursor (L:Layout) (lane:Fin 9) (i o:ℕ) (s:State):Prop extends Header L lane s where
 index:s.natReg 4593=i
 offset:s.natReg 4595=o
 zero:s.natReg 4590=0
 one:s.natReg 4591=1
 two:s.natReg 4592=2
lemma Cursor.withPC {L:Layout} {lane:Fin 9} {i o pc:ℕ} {s:State} (h:Cursor L lane i o s):
 Cursor L lane i o (setPC s pc):=
 ⟨⟨h.count,h.directory,h.lane,h.rows,h.permutation,h.coefficient⟩,h.index,h.offset,h.zero,h.one,h.two⟩

def Cell (D i:ℕ) (a:Entry) (s:State):Prop:=
 s.natHeap (D+2*i)=some a.radix ∧s.natHeap (D+2*i+1)=some a.pool
def Directory (D:ℕ):List Entry→ℕ→State→Prop
 | [],_,_=>True
 | a::as,i,s=>Cell D i a s ∧Directory D as (i+1) s
def Pools (as:List Entry) (s:State):Prop:=
 ∀a∈as,∀lane:Fin 9,∀j:Fin a.radix,s.scalarHeap (a.pool+lane.val*a.radix+j.val)=some (prepared (a.value lane j))
def Produced (L:Layout) (lane:Fin 9) (as:List Entry) (i o:ℕ) (s:State):Prop:=
 Rows (axes lane L.permutation L.coefficient o as) i L.rows s ∧
 (∀a∈axes lane L.permutation L.coefficient o as,∀j:Fin a.radix,
  s.natHeap (a.permutationBase+j.val)=some (a.permutation j).val) ∧
 (∀a∈axes lane L.permutation L.coefficient o as,∀j:Fin a.radix,
  s.scalarHeap (a.coefficientBase+j.val)=some (prepared (a.coefficient j)))
def Frame (s u:State):Prop:=u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 ∀q,(q < 170 ∨181 ≤ q)→(q < 4380 ∨4388 ≤ q)→(q < 4590 ∨4596 ≤ q)→u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,fun _ _ _ _=>rfl⟩
lemma Frame.trans {s t u:State} (h:Frame s t) (k:Frame t u):Frame s u:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,
 fun q h0 h1 h2=>(k.2.2 q h0 h1 h2).trans (h.2.2 q h0 h1 h2)⟩
lemma setup_frame (s:State):Frame s (applyBlock setup s):=by
 refine ⟨rfl,rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega)[setup,applyBlock,Op.apply,writeNat,next]
lemma setup_header {L:Layout} {lane:Fin 9} {i o:ℕ} {a:Entry} {s:State}
 (h:Cursor L lane i o s) (cell:Cell L.directory i a s):
 UniformGlobalDiagonalPhasePreparation.Args a.radix a.pool (L.permutation+o)
  (L.coefficient+o) L.rows i lane (applyBlock setup s):=by
 have cp:=cell.2
 simp only[Nat.add_assoc] at cp
 constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.directory,h.index,h.offset,h.two,h.one,h.zero,
  h.lane,h.permutation,h.coefficient,h.rows,cell.1,cp,Nat.mul_comm i 2,Nat.add_assoc]
lemma setup_cursor {L:Layout} {lane:Fin 9} {i o:ℕ} {s:State} (h:Cursor L lane i o s):
 Cursor L lane i o (applyBlock setup s):=by
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.count,h.directory,h.lane,h.rows,
    h.permutation,h.coefficient]
 all_goals simp[setup,applyBlock,Op.apply,writeNat,next,h.index,h.offset,h.zero,h.one,h.two]
lemma setup_safe {L:Layout} {lane:Fin 9} {i o:ℕ} {a:Entry} {s:State}
 (h:Cursor L lane i o s) (cell:Cell L.directory i a s)
 (hi:i < L.ell) (off:o+a.radix ≤ L.total) (pool:a.pool+9*a.radix ≤ L.coefficient):
 readable setup s ∧peak setup s ≤ L.B:=by
 have e0:=L.directoryBelow;have e1:=L.rowsBelow;have e2:=L.permutationBound;have e3:=L.coefficientBound
 have e4:=L.code
 have lv:lane.val ≤ 8:=by have:=lane.isLt;omega
 have cp:=cell.2
 simp only[Nat.add_assoc] at cp
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.directory,h.index,h.offset,h.two,h.one,h.zero,
  h.lane,h.permutation,h.coefficient,h.rows,cell.1,cp,Nat.mul_comm i 2,Nat.add_assoc]
 omega

lemma row_keeps_nat (q:ℕ) (h0:q < 170 ∨181 ≤ q) (h1:q≠4387):
 ∀ins∈UniformGlobalDiagonalPhasePreparation.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 have tiny:∀a∈([170,171,172,173,174,175,176,177,178,179,180,4387]:List ℕ),q≠a:=by
  intro a ha;simp only[List.mem_cons,List.not_mem_nil,or_false] at ha;rcases ha with h|h|h|h|h|h|h|h|h|h|h|h <;>omega
 have head:∀ins∈UniformGlobalDiagonalPhasePreparation.setup.map Op.code,UniformNewtonTableMachine.KeepsNat q ins:=by
  simp[UniformGlobalDiagonalPhasePreparation.setup,Op.code,UniformNewtonTableMachine.KeepsNat,ne_comm,tiny]
 have base:∀ins∈UniformTensorDiagonalBankMachine.program,UniformNewtonTableMachine.KeepsNat q ins:=by
  simp[UniformTensorDiagonalBankMachine.program,UniformTensorDiagonalBankMachine.setup,
   UniformTensorDiagonalBankMachine.body,Op.code,UniformNewtonTableMachine.KeepsNat,ne_comm,tiny]
 have last:∀ins∈[Instruction.halt],UniformNewtonTableMachine.KeepsNat q ins:=by
  simp[UniformNewtonTableMachine.KeepsNat]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q head (UniformReciprocalMachine.keeps_relocate q 8 28 base)) last
lemma row_nat {B n t q:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformGlobalDiagonalPhasePreparation.program n x B s t u)
 (h0:q < 170 ∨181 ≤ q) (hq:q≠4387):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (row_keeps_nat q h0 hq)
lemma row_cursor {L:Layout} {lane:Fin 9} {i o B n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:Cursor L lane i o s) (run:BoundedExecution UniformGlobalDiagonalPhasePreparation.program n x B s t u):
 Cursor L lane i o u:=by
 constructor
 · constructor
   · exact (row_nat run (by omega) (by omega)).trans h.count
   · exact (row_nat run (by omega) (by omega)).trans h.directory
   · exact (row_nat run (by omega) (by omega)).trans h.lane
   · exact (row_nat run (by omega) (by omega)).trans h.rows
   · exact (row_nat run (by omega) (by omega)).trans h.permutation
   · exact (row_nat run (by omega) (by omega)).trans h.coefficient
 · exact (row_nat run (by omega) (by omega)).trans h.index
 · exact (row_nat run (by omega) (by omega)).trans h.offset
 · exact (row_nat run (by omega) (by omega)).trans h.zero
 · exact (row_nat run (by omega) (by omega)).trans h.one
 · exact (row_nat run (by omega) (by omega)).trans h.two
lemma finish_frame (s:State):Frame s (applyBlock finish s):=by
 refine ⟨rfl,rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega)[finish,applyBlock,Op.apply,writeNat,next]
lemma finish_cursor {L:Layout} {lane:Fin 9} {i o:ℕ} {a:Entry} {s:State}
 (h:Cursor L lane i o s) (hr:s.natReg 4380=a.radix):
 Cursor L lane (i+1) (o+a.radix) (applyBlock finish s):=by
 constructor
 · constructor <;>simp[finish,applyBlock,Op.apply,writeNat,next,h.count,h.directory,h.lane,h.rows,
   h.permutation,h.coefficient]
 all_goals simp[finish,applyBlock,Op.apply,writeNat,next,h.index,h.offset,h.zero,h.one,h.two,hr]

def RowData (L:Layout) (lane:Fin 9) (a:Entry) (i o:ℕ) (s u:State):Prop:=
 (∀j:Fin a.radix,u.natHeap (L.permutation+o+j.val)=some j.val) ∧
 (∀j:Fin a.radix,u.scalarHeap (L.coefficient+o+j.val)=some (prepared (a.value lane j))) ∧
 u.natHeap (L.rows+i*3)=some a.radix ∧
 u.natHeap (L.rows+i*3+1)=some (L.permutation+o) ∧
 u.natHeap (L.rows+i*3+2)=some (L.coefficient+o) ∧
 (∀q,(q < L.rows+i*3 ∨L.rows+i*3+3 ≤ q)→(q < L.permutation+o ∨L.permutation+o+a.radix ≤ q)→
  u.natHeap q=s.natHeap q) ∧
 (∀q,q < L.coefficient+o ∨L.coefficient+o+a.radix ≤ q→u.scalarHeap q=s.scalarHeap q)
lemma setup_heaps (s:State):(applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap:=by constructor <;>rfl
end
end ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
