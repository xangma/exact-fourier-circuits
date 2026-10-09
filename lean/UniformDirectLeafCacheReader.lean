import UniformDirectLeafCacheChronology
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheReader
open UniformMachine UniformTensorMonomialMachine
open UniformTransposeDescriptorMachine (Record)

/-- Only ordinary source/destination bank headers enter. Radix and coefficient
addresses are read from the real retained directory and printed descriptor. -/
structure Config where
 record : ℕ
 originalDirectory : ℕ
 conjugateDirectory : ℕ
 pool : ℕ
 rows : ℕ
 permutation : ℕ
 widths : ℕ
 markers : ℕ
 axis : ℕ
 entry : ℕ
 time : ℕ

structure Args (c : Config) (s : State) : Prop where
 record : s.natReg 6600=c.record
 originalDirectory : s.natReg 6601=c.originalDirectory
 conjugateDirectory : s.natReg 6602=c.conjugateDirectory
 pool : s.natReg 6603=c.pool
 rows : s.natReg 6604=c.rows
 permutation : s.natReg 6605=c.permutation
 widths : s.natReg 6606=c.widths
 markers : s.natReg 6607=c.markers
 axis : s.natReg 6608=c.axis
 entry : s.natReg 6609=c.entry
 time : s.natReg 6610=c.time
structure Source (c : Config) (r A C : ℕ) (q : Record) (s : State) : Prop where
 record : UniformDirectLeafCacheSource.At c.record q s
 original : s.natHeap c.originalDirectory=some A
 radix : s.natHeap (c.originalDirectory+1)=some r
 conjugate : s.natHeap c.conjugateDirectory=some C

def read : List Op := [.literal 6648 1,.getNat 6640 6600,
 .add 6650 6600 6648,.getNat 6641 6650,.add 6650 6650 6648,.getNat 6642 6650,
 .add 6650 6650 6648,.getNat 6643 6650,.getNat 6644 6601,
 .add 6650 6601 6648,.getNat 6645 6650,.getNat 6646 6602,
 .literal 6647 0,.literal 6649 3,.mul 6650 6645 6649,.add 6651 6644 6650,
 .sub 6651 6643 6651,.add 6652 6646 6650,.add 6652 6652 6651]
lemma read_length : read.length=19 := rfl

structure Read (r A C : ℕ) (q : Record) (s : State) : Prop where
 kind : s.natReg 6640=q.kind
 dest : s.natReg 6641=q.dest
 source : s.natReg 6642=q.source
 coefficient : s.natReg 6643=q.coefficient
 original : s.natReg 6644=A
 radix : s.natReg 6645=r
 conjugate : s.natReg 6646=C
 zero : s.natReg 6647=0
 one : s.natReg 6648=1
 three : s.natReg 6649=3
 index : s.natReg 6651=q.coefficient-(A+3*r)
 conjugateCoefficient : s.natReg 6652=C+3*r+(q.coefficient-(A+3*r))

lemma read_nat (s : State) (j : ℕ) (outside : j<6640 ∨ 6653≤j) :
 (applyBlock read s).natReg j=s.natReg j := by
 simp (disch:=omega) [read,applyBlock,Op.apply,writeNat,next]
lemma read_args {c : Config} {s : State} (h : Args c s) : Args c (applyBlock read s) := by
 exact ⟨(read_nat s _ (Or.inl (by omega))).trans h.record,
  (read_nat s _ (Or.inl (by omega))).trans h.originalDirectory,
  (read_nat s _ (Or.inl (by omega))).trans h.conjugateDirectory,
  (read_nat s _ (Or.inl (by omega))).trans h.pool,
  (read_nat s _ (Or.inl (by omega))).trans h.rows,
  (read_nat s _ (Or.inl (by omega))).trans h.permutation,
  (read_nat s _ (Or.inl (by omega))).trans h.widths,
  (read_nat s _ (Or.inl (by omega))).trans h.markers,
  (read_nat s _ (Or.inl (by omega))).trans h.axis,
  (read_nat s _ (Or.inl (by omega))).trans h.entry,
  (read_nat s _ (Or.inl (by omega))).trans h.time⟩
lemma read_values {c : Config} {r A C : ℕ} {q : Record} {s : State}
 (h : Args c s) (src : Source c r A C q s) : Read r A C q (applyBlock read s) := by
 have h0 : s.natHeap c.record=some q.kind := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (0:Fin 4)
 have h1 : s.natHeap (c.record+1)=some q.dest := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (1:Fin 4)
 have h2 : s.natHeap (c.record+2)=some q.source := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (2:Fin 4)
 have h3 : s.natHeap (c.record+3)=some q.coefficient := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (3:Fin 4)
 constructor <;>simp [read,applyBlock,Op.apply,writeNat,next,h.record,h.originalDirectory,
  h.conjugateDirectory,src.original,src.radix,src.conjugate,h0,h1,h2,h3,Nat.mul_comm,Nat.add_assoc]

lemma read_heaps (s : State) : (applyBlock read s).natHeap=s.natHeap ∧
 (applyBlock read s).scalarHeap=s.scalarHeap ∧(applyBlock read s).scalarReg=s.scalarReg ∧
 (applyBlock read s).outputs=s.outputs ∧(applyBlock read s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma read_safe {c : Config} {r A C B : ℕ} {q : Record} {s : State}
 (h : Args c s) (src : Source c r A C q s) (wb:WordBound B s)
 (code:19≤B) (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (_conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q) :
 readable read s ∧ peak read s≤B := by
 have h0 : s.natHeap c.record=some q.kind := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (0:Fin 4)
 have h1 : s.natHeap (c.record+1)=some q.dest := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (1:Fin 4)
 have h2 : s.natHeap (c.record+2)=some q.source := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (2:Fin 4)
 have h3 : s.natHeap (c.record+3)=some q.coefficient := by
  simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (3:Fin 4)
 rcases range with ⟨hd,he,hlo,hhi⟩
 have kindBound: q.kind≤B := (wb.2.2.1 c.record q.kind h0).2
 constructor
 · simp [read,readable,Op.readable,Op.apply,writeNat,next,h.record,h.originalDirectory,
    h.conjugateDirectory,src.original,src.radix,src.conjugate,h0,h1,h2,h3,Nat.add_assoc]
 · simp [read,peak,Op.peak,Op.apply,writeNat,next,h.record,h.originalDirectory,
    h.conjugateDirectory,src.original,src.radix,src.conjugate,h0,h1,h2,h3,Nat.add_assoc]
   omega

/-- The actual fixed nineteen instructions decode the descriptor and retained
bank directory, including its genuine conjugate coefficient address. -/
lemma read_execution {c : Config} {r A C B n : ℕ} {q : Record} (p : Program) (pc : ℕ)
 (x : Fin n→ℂ) (s : State) (codeAt : BlockAt read p pc) (h : Args c s)
 (src : Source c r A C q s) (hp:s.pc=pc) (wb:WordBound B s)
 (code:pc+19≤B) (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q) :
 BoundedRuns p n x B s 19 (applyBlock read s) := by
 have safe:=read_safe h src wb (by omega) descriptor directory conjugateDirectory original conjugate range
 exact block_runs read p pc n B x s codeAt hp wb (by rw [read_length];exact code) safe.1 safe.2
end ExactFourierCircuits.UniformDirectLeafCacheReader
