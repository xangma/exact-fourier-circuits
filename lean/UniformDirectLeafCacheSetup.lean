import UniformDirectLeafCacheProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheSetup
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheProgram
open UniformTransposeDescriptorMachine (Record)
noncomputable section

structure Core (c : Config) (r : ℕ) (s : State) : Prop where
 time : s.natReg 5840=c.time
 radix : s.natReg 5841=r
 pool : s.natReg 5842=c.pool
 permutation : s.natReg 5843=c.permutation
 widths : s.natReg 5844=c.widths
 markers : s.natReg 5845=c.markers
 axis : s.natReg 5846=c.axis
 rows : s.natReg 5847=c.rows
 directory : s.natReg 5848=c.entry
structure Installed (c : Config) (r A C : ℕ) (q : Record) (s : State) : Prop where
 args : Args c s
 read : Read r A C q s
 scales : UniformZeroFreePairShearMachine.Args 0 0 q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) s
 pool : s.natReg 4330=c.pool
 radix : s.natReg 4331=r
 rows : s.natReg 2140=c.rows
 index : s.natReg 2141=0
 dest : s.natHeap c.rows=some q.dest
 source : s.natHeap (c.rows+1)=some q.source
 coefficient : s.natHeap (c.rows+2)=some q.coefficient
 core : Core c r s

lemma Args.setPC {c : Config} {s : State} (h : Args c s) (pc : ℕ) : Args c (setPC s pc) :=
 ⟨h.record,h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,h.permutation,h.widths,h.markers,h.axis,h.entry,h.time⟩

lemma Read.setPC {r A C : ℕ} {q : Record} {s : State} (h : Read r A C q s) (pc : ℕ) : Read r A C q (setPC s pc) :=
 ⟨h.kind,h.dest,h.source,h.coefficient,h.original,h.radix,h.conjugate,h.zero,h.one,h.three,h.index,h.conjugateCoefficient⟩

lemma Core.setPC {c : Config} {r : ℕ} {s : State} (h : Core c r s) (pc : ℕ) : Core c r (setPC s pc) :=
 ⟨h.time,h.radix,h.pool,h.permutation,h.widths,h.markers,h.axis,h.rows,h.directory⟩

lemma install_nat (s : State) (j : ℕ)
 (outside : j≠1620∧j≠1621∧j≠1622∧j≠1623∧j≠4330∧j≠4331∧j≠2140∧j≠2141∧
  j≠6650∧(j<5840∨5849≤j)) : (applyBlock install s).natReg j=s.natReg j := by
 rcases outside with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
 simp (disch:=omega) [install,applyBlock,Op.apply,writeNat,next]
lemma install_args {c : Config} {s : State} (h : Args c s) : Args c (applyBlock install s) := by
 exact ⟨(install_nat s _ (by omega)).trans h.record,
  (install_nat s _ (by omega)).trans h.originalDirectory,
  (install_nat s _ (by omega)).trans h.conjugateDirectory,
  (install_nat s _ (by omega)).trans h.pool,
  (install_nat s _ (by omega)).trans h.rows,
  (install_nat s _ (by omega)).trans h.permutation,
  (install_nat s _ (by omega)).trans h.widths,
  (install_nat s _ (by omega)).trans h.markers,
  (install_nat s _ (by omega)).trans h.axis,
  (install_nat s _ (by omega)).trans h.entry,
  (install_nat s _ (by omega)).trans h.time⟩
lemma install_read {r A C : ℕ} {q : Record} {s : State} (h : Read r A C q s) :
 Read r A C q (applyBlock install s) := by
 exact ⟨(install_nat s _ (by omega)).trans h.kind,
  (install_nat s _ (by omega)).trans h.dest,
  (install_nat s _ (by omega)).trans h.source,
  (install_nat s _ (by omega)).trans h.coefficient,
  (install_nat s _ (by omega)).trans h.original,
  (install_nat s _ (by omega)).trans h.radix,
  (install_nat s _ (by omega)).trans h.conjugate,
  (install_nat s _ (by omega)).trans h.zero,
  (install_nat s _ (by omega)).trans h.one,
  (install_nat s _ (by omega)).trans h.three,
  (install_nat s _ (by omega)).trans h.index,
  (install_nat s _ (by omega)).trans h.conjugateCoefficient⟩
lemma install_heap {c : Config} {r A C : ℕ} {q : Record} {s : State}
 (a : Args c s) (h : Read r A C q s) :
 (applyBlock install s).natHeap=Function.update
  (Function.update (Function.update s.natHeap c.rows (some q.dest))
    (c.rows+1) (some q.source)) (c.rows+2) (some q.coefficient) := by
 simp [install,applyBlock,Op.apply,writeNat,next,a.rows,h.zero,h.one,h.dest,h.source,h.coefficient]
lemma install_values {c : Config} {r A C : ℕ} {q : Record} {s : State}
 (a : Args c s) (h : Read r A C q s) : Installed c r A C q (applyBlock install s) := by
 refine ⟨install_args a,install_read h,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor <;>simp [install,applyBlock,Op.apply,writeNat,next,h.zero,h.coefficient,h.conjugateCoefficient]
 · simp [install,applyBlock,Op.apply,writeNat,next,h.zero,a.pool]
 · simp [install,applyBlock,Op.apply,writeNat,next,h.zero,h.radix]
 · simp [install,applyBlock,Op.apply,writeNat,next,h.zero,a.rows]
 · simp [install,applyBlock,Op.apply,writeNat,next,h.zero]
 · rw [install_heap a h];simp
 · rw [install_heap a h];simp
 · rw [install_heap a h];simp
 · constructor <;>simp [install,applyBlock,Op.apply,writeNat,next,h.zero,h.radix,
    a.time,a.pool,a.permutation,a.widths,a.markers,a.axis,a.rows,a.entry]
lemma install_heaps (s : State) : (applyBlock install s).scalarHeap=s.scalarHeap ∧
 (applyBlock install s).scalarReg=s.scalarReg ∧(applyBlock install s).outputs=s.outputs ∧
 (applyBlock install s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩
lemma install_other {c : Config} {r A C : ℕ} {q : Record} {s : State}
 (a : Args c s) (h : Read r A C q s) (j : ℕ) (outside:j<c.rows∨c.rows+3≤j) :
 (applyBlock install s).natHeap j=s.natHeap j := by
 rw [install_heap a h]
 simp only [Function.update]
 split_ifs <;>first |omega |rfl
lemma install_safe {c : Config} {r A C B : ℕ} {q : Record} {s : State}
 (a : Args c s) (h : Read r A C q s) (wb:WordBound B s) (rows:c.rows+3≤B) :
 readable install s ∧peak install s≤B := by
 have p:=wb.2.1 6603;have r':=wb.2.1 6645;have cf:=wb.2.1 6643
 have cc:=wb.2.1 6652;have d:=wb.2.1 6641;have e:=wb.2.1 6642
 have t:=wb.2.1 6610;have P:=wb.2.1 6605;have W:=wb.2.1 6606
 have U:=wb.2.1 6607;have A':=wb.2.1 6608;have D:=wb.2.1 6609
 simp only [a.pool,h.radix,h.coefficient,h.conjugateCoefficient,h.dest,h.source,a.time,
  a.permutation,a.widths,a.markers,a.axis,a.entry] at p r' cf cc d e t P W U A' D
 constructor
 · simp [install,readable,Op.readable]
 · simp [install,peak,Op.peak,Op.apply,writeNat,next,h.zero,h.one,a.rows,a.pool,h.radix,
    h.coefficient,h.conjugateCoefficient,h.dest,h.source,a.time,a.permutation,a.widths,a.markers,a.axis,a.entry]
   omega
end
end ExactFourierCircuits.UniformDirectLeafCacheSetup
