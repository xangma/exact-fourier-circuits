import UniformDirectLeafCacheSetup
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheBootstrap
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheSetup UniformDirectLeafCacheProgram
open UniformTransposeDescriptorMachine (Record)
noncomputable section

lemma installed_pool {c : Config} {r A C : ℕ} {q : Record} {s u : State}
 (h : Installed c r A C q s) (frame : UniformGlobalScalePoolMachine.Frame s u) :
 Installed c r A C q u := by
 have keep (j : ℕ) (h0:j≠4356) (h1:j≠4357) (h2:j≠4358) (h3:j≠4359) :=
  frame.natReg j h0 h1 h2 h3
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact ⟨(keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.record,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.originalDirectory,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.conjugateDirectory,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.pool,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.rows,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.permutation,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.widths,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.markers,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.axis,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.entry,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.args.time⟩
 · exact ⟨(keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.kind,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.dest,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.source,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.coefficient,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.original,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.radix,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.conjugate,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.zero,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.one,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.three,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.index,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.read.conjugateCoefficient⟩
 · exact ⟨(keep _ (by omega) (by omega) (by omega) (by omega)).trans h.scales.leftAddress,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.scales.rightAddress,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.scales.coefficient,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.scales.conjugateCoefficient⟩
 · exact (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.pool
 · exact (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.radix
 · exact (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.rows
 · exact (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.index
 · rw [frame.natHeap];exact h.dest
 · rw [frame.natHeap];exact h.source
 · rw [frame.natHeap];exact h.coefficient
 · exact ⟨(keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.time,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.radix,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.pool,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.permutation,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.widths,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.markers,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.axis,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.rows,
    (keep _ (by omega) (by omega) (by omega) (by omega)).trans h.core.directory⟩

/-- The charged42-instruction front end is a separate proof boundary,
so the pool loop never unfolds the nested nineteen/23-instruction state. -/
theorem front {c : Config} {r A C n B : ℕ} {q : Record}
 (x : Fin n→ℂ) (s : State) (args:Args c s) (src:Source c r A C q s)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q)
 (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (rows:c.rows+3≤B) (code:264≤B) (pc:s.pc=0) (wb:WordBound B s) : ∃u,
 BoundedRuns UniformDirectLeafCacheProgram.program n x B s 42 u ∧u.pc=42 ∧Installed c r A C q u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,(j<c.rows∨c.rows+3≤j)→u.natHeap j=s.natHeap j) := by
 have readRun:=read_execution UniformDirectLeafCacheProgram.program 0 x s read_code args src pc wb (by omega)
  descriptor directory conjugateDirectory original conjugate range
 let a:=applyBlock read s
 have ap:a.pc=19:=by rw[applyBlock_pc,pc,read_length]
 have ar:=read_args args
 have av:=read_values args src
 have safe:=install_safe ar av readRun.final_bound rows
 have installRun:=block_runs install UniformDirectLeafCacheProgram.program 19 n B x a install_code ap readRun.final_bound
  (by rw[install_length];omega) safe.1 safe.2
 let b:=applyBlock install a
 have bp:b.pc=42:=by rw[applyBlock_pc,ap,install_length]
 refine ⟨b,?_,bp,install_values ar av,rfl,rfl,rfl,rfl,?_⟩
 · convert readRun.trans installRun using 1
   rw[install_length]
 · intro j hj
   exact install_other ar av j hj

/-- Decode actual source records, print the live endpoint row, and initialize
all nine scalar lanes. No factor-table or ready-helper premise enters. -/
theorem execution {c : Config} {r A C n B : ℕ} {q : Record} (mu : ℂ)
 (x : Fin n→ℂ) (s : State) (args:Args c s) (src:Source c r A C q s)
 (values:UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) s)
 (constants:UniformHadamardPairMachine.Constants s)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q)
 (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (rows:c.rows+3≤B) (pool:c.pool+9*r≤B) (base:6≤c.pool)
 (coefficient:q.coefficient<c.pool)
 (conjugateCoefficient:C+3*r+(q.coefficient-(A+3*r))<c.pool)
 (code:264≤B) (pc:s.pc=0) (wb:WordBound B s) : ∃u,
 BoundedRuns UniformDirectLeafCacheProgram.program n x B s (45*r+49) u ∧u.pc=53 ∧Installed c r A C q u ∧
 UniformGlobalScalePoolMachine.Prefix c.pool (9*r) u ∧
 UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) u ∧UniformHadamardPairMachine.Constants u ∧
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) ∧
 (∀j,(j<c.rows∨c.rows+3≤j)→u.natHeap j=s.natHeap j) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 obtain ⟨b,frontRun,bp,ready,sh,sr,outs0,roots0,nh0⟩:=front x s args src range
  descriptor directory conjugateDirectory original conjugate rows code pc wb
 let start:=setPC b 0
 have swb:=changePC_bound B b 0 frontRun.final_bound (by omega)
 obtain ⟨u,run,up,ones,out,frame⟩:=UniformGlobalScalePoolMachine.execution c.pool r n B x start
  ready.pool ready.radix pool (by omega) rfl swb
 have place:=UniformBoundedAssembly.boundedExecution_placed pool_code
  (by rw[UniformGlobalScalePoolMachine.program_length];omega) (by omega) run
 rw[show placed 42 start=b by change {b with pc:=42}=b;rw[←bp]] at place
 let result:=setPC u 53
 have sameFrame:UniformGlobalScalePoolMachine.Frame b result:=
  ⟨frame.natHeap,frame.outputs,frame.roots,frame.scalarReg,frame.natReg⟩
 have installed:Installed c r A C q result:=installed_pool ready sameFrame
 have outside (j:ℕ) (hj:j<c.pool∨c.pool+9*r≤j):result.scalarHeap j=s.scalarHeap j:=(out j hj).trans (congrFun sh j)
 have sources:UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) result:=by
  constructor
  · rw[outside _ (Or.inl coefficient)];exact values.1
  · rw[outside _ (Or.inl conjugateCoefficient)];exact values.2
 have const:UniformHadamardPairMachine.Constants result:=by
  rcases constants with ⟨c1,c2,c3,c4,c5⟩
  exact ⟨(outside 1 (Or.inl (by omega))).trans c1,
   (outside 2 (Or.inl (by omega))).trans c2,
   (outside 3 (Or.inl (by omega))).trans c3,
   (outside 4 (Or.inl (by omega))).trans c4,
   (outside 5 (Or.inl (by omega))).trans c5⟩
 refine ⟨result,?_,rfl,installed,ones,sources,const,outside,?_,frame.outputs.trans outs0,frame.roots.trans roots0⟩
 · convert frontRun.trans place using 1 <;>first |omega |rfl
 · intro j hj
   change u.natHeap j=s.natHeap j
   rw[frame.natHeap]
   exact nh0 j hj
end
end ExactFourierCircuits.UniformDirectLeafCacheBootstrap
