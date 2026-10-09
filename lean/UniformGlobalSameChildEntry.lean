import UniformSameProgramSectorEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalSameChildEntry
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Same data/address budget for a non-halting placed segment. Only actual
instruction PCs and its final PC need relocation room. -/
lemma boundedRuns_placed {p q:Program} {base ret n B ticks:ℕ} {x:Fin n→ℂ}
 (code:CodeAt p q base ret) (fits:base+p.length≤B) {s u:State}
 (run:BoundedRuns p n x B s ticks u) (last:base+u.pc≤B):
 BoundedRuns q n x B (placed base s) ticks (placed base u):=by
 induction run with
 |refl wb=>exact .refl (UniformBoundedAssembly.placed_bound _ _ _ wb last)
 |next wb step _ ih=>
  have pc:=running_pc step
  exact .next (UniformBoundedAssembly.placed_bound _ _ _ wb (by omega))
   (running_placed code step) (ih last)

def programFor (W:ℕ):Program:=UniformGlobalMovementAssembly.assembly
 (UniformGlobalDiagonalChildPrefix.programFor W) UniformSameProgramSectorLoop.program []
lemma program_length (W:ℕ):(programFor W).length=UniformRecursiveSavingProgram.program.length+525:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly_length,
  UniformGlobalDiagonalChildPrefix.program_length,UniformSameProgramSectorLoop.program_length,List.length_nil];omega
lemma prefix_code (W:ℕ):CodeAt (UniformGlobalDiagonalChildPrefix.programFor W) (programFor W) 0 504:=by
 have h:=UniformGlobalMovementAssembly.first_code (UniformGlobalDiagonalChildPrefix.programFor W)
  UniformSameProgramSectorLoop.program []
 simpa only[programFor,UniformGlobalDiagonalChildPrefix.program_length] using h
lemma loop_code (W:ℕ):CodeAt UniformSameProgramSectorLoop.program (programFor W) 504
 (504+UniformSameProgramSectorLoop.program.length):=by
 have h:=UniformGlobalMovementAssembly.second_code (UniformGlobalDiagonalChildPrefix.programFor W)
  UniformSameProgramSectorLoop.program []
 simpa only[programFor,UniformGlobalDiagonalChildPrefix.program_length] using h

lemma envelope_arithmetic (a B:ℕ) (h:a+525≤B):a+20≤B ∧504+(a+20)≤B ∧521≤B:=by omega

/-- Actual continuous131→all-W153→202gather→generated row reads→7boot→
branch→9root loader, in one static program whose common recursive C begins
at PC521. No transform/child-action premise is used. The child itself is
not executed by this entry-prefix theorem. -/
theorem execution {W n ordinal frontier:ℕ} (c:UniformGlobalDiagonalChildPrefix.Context W)
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (ready:UniformGlobalDiagonalChildPrefix.Ready c ordinal frontier v s)
 (hi:ordinal<(UniformProducedSectorChildABI.states c.physical).length)
 (code:(programFor W).length≤c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u ticks,BoundedRuns (programFor W) n x c.metadata.B s ticks u ∧
 ticks≤UniformGlobalDiagonalChildPrefix.diagonalTicks c+UniformGlobalDiagonalChildPrefix.movementBound c+18 ∧
 u.pc=521 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((UniformProducedSectorChildABI.states c.physical)[0]'(by omega)).pairs
  (c.transpose.buffer+W*((UniformProducedSectorChildABI.states c.physical)[0]'(by omega)).start)
  ((UniformProducedSectorChildABI.states c.physical)[0]'(by omega)).width frontier u ∧
 u.natReg 4151=0 ∧u.natReg 4122=2^(u.natReg 4120) ∧
 UniformProducedSectorChildABI.GroupedSource W
  (c.transpose.buffer+W*((UniformProducedSectorChildABI.states c.physical)[0]'(by omega)).start)
  ((UniformProducedSectorChildABI.states c.physical)[0]'(by omega)).width
  (UniformAllSectorTransposeMachine.slice
   (UniformGlobalPackingChildPreparation.packedValues c.packing
    (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume)
    (UniformGlobalDiagonalChildPrefix.phaseValues c v))
   ((UniformProducedSectorChildABI.states c.physical)[0]'(by omega))) u ∧
 UniformAllSectorTransposeMachine.Table c.transpose u ∧
 UniformSameProgramSectorLoop.Cursor (UniformProducedSectorChildABI.states c.physical).length
  c.transpose.directory frontier 0 u ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 obtain ⟨t,ticks,run,cost,tp,_child,_pow,_grouped,filled,table,num,dir,fresh,_saved,outs,roots,_low⟩:=
  UniformGlobalDiagonalChildPrefix.execution_directory c v x s ready hi pc wb
 have first:=UniformBoundedAssembly.boundedExecution_placed (prefix_code W)
  (by rw[UniformGlobalDiagonalChildPrefix.program_length];have:=c.code;omega)
  (by have:=c.code;omega) run
 rw[show placed 0 s=s by cases s;simp[placed]] at first
 let entry:=setPC t 0
 have eb:WordBound c.transpose.B entry:=by
  rw[c.transposeB]
  exact changePC_bound _ _ _ run.final_bound (by omega)
 have envelope:UniformRecursiveSavingProgram.program.length+525≤c.metadata.B:=by
  simpa only[program_length] using code
 have arithmetic:=envelope_arithmetic UniformRecursiveSavingProgram.program.length c.metadata.B envelope
 have loopFit:UniformSameProgramSectorLoop.program.length≤c.transpose.B:=by
  simpa only[c.transposeB,UniformSameProgramSectorLoop.program_length] using arithmetic.1
 have present:0<(UniformProducedSectorChildABI.states c.physical).length:=by omega
 obtain ⟨z,second,zp,child,depth,pow,grouped,retained,cursor,_heap,_regs,zouts,zroots⟩:=
  UniformSameProgramSectorLoop.entry_execution c.physical c.transpose
   (UniformGlobalPackingChildPreparation.packedValues c.packing
    (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume)
    (UniformGlobalDiagonalChildPrefix.phaseValues c v))
   x entry num dir fresh table filled present loopFit rfl eb
 have second':BoundedRuns UniformSameProgramSectorLoop.program n x c.metadata.B entry 17 z:=by
  simpa only[c.transposeB] using second
 have last:504+z.pc≤c.metadata.B:=by simpa only[zp] using arithmetic.2.2
 have moved:=boundedRuns_placed (loop_code W)
  (by simpa only[UniformSameProgramSectorLoop.program_length] using arithmetic.2.1) second' last
 rw[show placed 504 entry=setPC t 504 by cases t;rfl] at moved
 refine ⟨placed 504 z,ticks+17,first.trans moved,?_,?_,
  ⟨child.exponent,child.base,child.width,child.frontier⟩,depth,pow,grouped,retained,?_,
  zouts.trans outs,zroots.trans roots⟩
 · omega
 · change 504+z.pc=521;rw[zp]
 · exact ⟨cursor.count,cursor.one,cursor.index,cursor.directory,cursor.fresh,cursor.zero,cursor.five⟩

/- Open: actual C execution and all remaining sectors, inverse scatter and
inverse packing, scalar source/header chronology for all28 matching phases,
cache/time/axis finite loops, CRT/output and complete common runtime. -/
end
end ExactFourierCircuits.UniformGlobalSameChildEntry
