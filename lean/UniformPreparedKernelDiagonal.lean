import UniformGlobalKernelDiagonalAssembly
import UniformGlobalKernelDiagonalExecution
import UniformActualSectorRootBody
import UniformPreparedKernelAnyExecution
import UniformDiagonalDependencyTags
import UniformKernelDiagonalBanks
import UniformKernelClockFrame
import UniformActualKernelCallerFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedKernelDiagonal
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformKernelDiagonalBanks
open UniformGlobalKernelDiagonalAssembly (programFor kernel_code header_code header_jump diagonal_code halt_at)
noncomputable section
attribute [local irreducible] Nat.add
attribute [local irreducible] UniformGlobalKernelDiagonalAssembly.programFor UniformInitializedKernelExecution.programFor

abbrev child:Program:=UniformRecursiveSavingProgram.program
abbrev W:ℕ:=UniformRecursiveSelfCallMachine.W
lemma placed_reset (s:State) (base:ℕ):placed base (setPC s 0)=setPC s base:=by
 cases s
 simp only[placed,setPC,Nat.add_zero]

lemma input_kept {W n B ticks:ℕ} {x:Fin n→ℂ} {s t:State} (d:Diagonal W)
 (run:BoundedExecution (UniformInitializedKernelExecution.programFor child W) n x B s ticks t)
 (input:UniformDiagonalHeaderInstallation.Input d.rows d.tensor s):
 UniformDiagonalHeaderInstallation.Input d.rows d.tensor t:=by
 have low (j:ℕ) (lo:100 ≤ j) (hi:j < 107):t.natReg j=s.natReg j:=
  UniformKernelClockFrame.actual_startup_bounded_frame run j lo hi
 have high (j:ℕ) (lo:6020 ≤ j) (hi:j < 6028):t.natReg j=s.natReg j:=
  UniformActualKernelCallerFrame.bounded_frame run j (Or.inl ⟨by omega,by omega⟩)
 constructor
 · rw[low 102 (by omega) (by omega)];exact input.rowsCount
 · rw[low 102 (by omega) (by omega)];exact input.tensorCount
 · rw[high 6020 (by omega) (by omega)];exact input.directory
 · rw[high 6021 (by omega) (by omega)];exact input.rows
 · rw[high 6022 (by omega) (by omega)];exact input.permutation
 · rw[high 6026 (by omega) (by omega),low 103 (by omega) (by omega)];exact input.coefficient
 · rw[low 103 (by omega) (by omega)];exact input.volume
 · rw[high 6026 (by omega) (by omega)];exact input.source
 · rw[high 6027 (by omega) (by omega)];exact input.destination
 · rw[high 6021 (by omega) (by omega)];exact input.tensorRows
 · rw[high 6024 (by omega) (by omega)];exact input.natStack
 · rw[high 6025 (by omega) (by omega)];exact input.scalarStack

lemma input_pc {W:ℕ} (d:Diagonal W) (t:State) (pc:ℕ)
 (h:UniformDiagonalHeaderInstallation.Input d.rows d.tensor t):
 UniformDiagonalHeaderInstallation.Input d.rows d.tensor (setPC t pc):=by
 cases h
 constructor <;>assumption

lemma ready_pc {W:ℕ} (d:Diagonal W) (lane:d.lane=0) (t h:State) (values:ℕ→ℕ→Scalar)
 (dh:UniformGlobalDiagonalRowsMachine.Header d.rows 0 h)
 (th:UniformGlobalTensorDiagonalMachine.Header d.tensor h)
 (directory:UniformGlobalDiagonalRowsMachine.Directory d.rows.directory d.entries 0 t)
 (pools:UniformGlobalDiagonalRowsMachine.Pools d.entries t)
 (source:UniformGlobalTensorDiagonalMachine.Source d.tensor values t)
 (nat:h.natHeap=t.natHeap) (scalar:h.scalarHeap=t.scalarHeap):
 UniformDiagonalReturnCore.Ready d values (setPC h 0):=by
 refine ⟨?_,?_,?_,?_,?_⟩
 · rw[lane]
   exact ⟨dh.count,dh.directory,dh.lane,dh.rows,dh.permutation,dh.coefficient⟩
 · exact directory_transfer d.rows.directory (d.rows.directory+2*d.entries.length) d.entries 0 t (setPC h 0)
    directory (by simp only[Nat.zero_add];exact le_rfl) (fun q _=>congrFun nat q)
 · exact pools_transfer d.rows.coefficient d.entries t (setPC h 0) pools d.poolsBelow (fun q _=>congrFun scalar q)
 · exact ⟨th.volume,th.source,th.destination,th.axes,th.rows,th.natStack,th.scalarStack⟩
 · intro r hr j hj
   exact (congrFun scalar _).trans (source r hr j hj)

/-- Additive all-active-W prepared-tag preservation for one actual literal tick consumer: initialized SAME-program sector loop,
charged diagonal headers, and actual147 diagonal return. The tag source is
extracted from the executed kernel output. The sole recursive prepared-tag
obligation is the explicit RootBody; no desired output or Ready is supplied. -/
theorem execution {F R n:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (diagonalInput:UniformDiagonalHeaderInstallation.Input d.rows d.tensor s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s)
 (directory:UniformGlobalDiagonalRowsMachine.Directory d.rows.directory d.entries 0 s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools d.entries s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (root:UniformPreparedSectorLoop.RootBody child W n g.inverse.layout.B F R UniformRecursiveChildInduction.cost x)
 (reserve:UniformRecursiveReserve.reserve≤R)
 (prepared:∀r,r<W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0 < W) (code:child.length+813 ≤ g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x g.metadata.B s ticks u ∧
 ticks ≤ UniformGlobalKernelDiagonalExecution.budget g d UniformRecursiveChildInduction.cost ∧u.pc=child.length+812 ∧
 (∀r,r < W→∀j:Fin d.packing.volume,
  (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.dependent=some false) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 obtain ⟨t,kt,kernel,cheap,tp,stored,outputs,roots,nat,scalar⟩:=
  UniformInitializedKernelRetention.execution child g UniformRecursiveChildInduction.cost v x s input banks source constants
   (UniformActualSectorRootBody.root_body n g.inverse.layout.B F R x reserve) positive (by omega) pc wb
 have kernelTags:=UniformPreparedKernelAnyExecution.execution child g UniformRecursiveChildInduction.cost v x s t
  input banks source constants root prepared positive (by omega) pc wb kernel
 have natKept:∀q,q < links.natEnd→t.natHeap q=s.natHeap q:=by
  intro q h
  exact nat q (h.trans_le links.natPacking) (h.trans_le links.natMetadata) (h.trans_le links.natFresh)
   (h.trans_le links.natStack) (h.trans_le links.natInverse)
 have scalarKept:∀q,q < links.scalarEnd→t.scalarHeap q=s.scalarHeap q:=by
  intro q h
  exact scalar q (h.trans_le links.scalarPacked) (h.trans_le links.scalarBuffer) (h.trans_le links.scalarFresh)
   (h.trans_le links.scalarNative) (h.trans_le links.scalarTemporary) (h.trans_le links.scalarFinal)
 have dirT:=directory_transfer d.rows.directory links.natEnd d.entries 0 s t directory
  (by simpa only[Nat.zero_add] using links.directory) natKept
 have poolsT:=pools_transfer links.scalarEnd d.entries s t pools links.pools scalarKept
 have numeric:=numeric_source g d links v t stored
 have inputT:=input_kept d kernel diagonalInput
 have placedKernel:=UniformBoundedAssembly.boundedExecution_placed (kernel_code child W)
  (by rw[UniformInitializedKernelExecution.program_length];omega) (by omega) kernel
 rw[show placed 0 s=s by cases s;simp only[placed,Nat.zero_add]] at placedKernel
 let middle:=setPC t (child.length+647)
 have middleBound:WordBound d.metadata.B middle:=by rw[links.bound];exact placedKernel.final_bound
 have inputM:UniformDiagonalHeaderInstallation.Input d.rows d.tensor middle:=input_pc d t _ inputT
 have tensorBound:WordBound d.tensor.B middle:=by rw[d.tensorB,d.sharedB];exact middleBound
 obtain ⟨header,dh,th,heap,scalars,scalarRegs,headOut,headRoots,_natRegs⟩:=
  UniformDiagonalHeaderInstallation.execution d.rows d.tensor (programFor child W) x middle inputM
   (header_code child W) rfl (by rw[d.tensorB,d.sharedB,links.bound];omega) tensorBound
 have headerRun:BoundedRuns (programFor child W) n x g.metadata.B middle 17
  (applyBlock (UniformDiagonalHeaderInstallation.block W) middle):=by
  simpa only[d.tensorB,d.sharedB,links.bound] using header
 let hstate:=applyBlock (UniformDiagonalHeaderInstallation.block W) middle
 have hp:hstate.pc=child.length+664:=by
  rw[applyBlock_pc,UniformDiagonalHeaderInstallation.block_length]
  change child.length+647+17=child.length+664
  omega
 let dent:=setPC hstate 0
 have db:WordBound d.metadata.B dent:=changePC_bound _ hstate 0 (by rw[links.bound];exact headerRun.final_bound) (by omega)
 let values:=UniformExecutedTaggedBank.values d.tensor.source d.tensor.volume t
 have ready:UniformDiagonalReturnCore.Ready d values dent:=
  ready_pc d links.lane t hstate values dh th dirT poolsT numeric.2 heap scalars
 obtain ⟨z,diagonal,zp,final,diagonalOut,diagonalRoots,_scalarFrame,_natFrame⟩:=
  UniformDiagonalReturnNumeric.execution d values x dent ready (by rw[links.bound];omega) rfl db
 have preparedValues:∀r,r<W→∀j,j<d.tensor.volume→(values r j).dependent=false:=by
  intro r hr j hj
  have volume:UniformSectorPackingMachine.physicalVolume g.physical=d.tensor.volume:=
   (g.physicalVolume.trans links.volume).trans d.volume
  have tag:=kernelTags r hr (finCongr volume.symm ⟨j,hj⟩)
  have h:(t.scalarHeap (d.tensor.source+r*d.tensor.volume+j)).map Scalar.dependent=some false:=by
   simpa only[links.source,volume,finCongr_apply,Fin.val_cast] using tag
  exact UniformPreparedKernelAnyExecution.projected_false h
 have tags:=UniformDiagonalDependencyTags.all_prepared d values x dent z ready
  (by rw[links.bound];omega) rfl db diagonal preparedValues
 have diagonalB:BoundedExecution (UniformGlobalDiagonalReturn.programFor W) n x g.metadata.B dent
  (UniformGlobalDiagonalChildPrefix.diagonalTicks d+7*(W*d.tensor.volume)+10) z:=by
  simpa only[links.bound] using diagonal
 have jump:BoundedRuns (programFor child W) n x g.metadata.B hstate 1 (setPC hstate (child.length+665)):=by
  exact .next headerRun.final_bound (by simp only[step,hp,header_jump];rfl)
   (.refl (changePC_bound _ hstate _ headerRun.final_bound (by omega)))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (diagonal_code child W)
  (by rw[UniformGlobalDiagonalReturn.program_length];omega) (by omega) diagonalB
 have entry:placed (child.length+665) dent=setPC hstate (child.length+665):=by
  exact placed_reset hstate (child.length+665)
 rw[entry] at moved
 let u:=setPC z (child.length+812)
 have stop:BoundedExecution (programFor child W) n x g.metadata.B u 1 u:=
  .halt moved.final_bound (by simp only[step,u,setPC,UniformGlobalKernelDiagonalAssembly.halt_at])
 refine ⟨u,kt+(17+(1+((UniformGlobalDiagonalChildPrefix.diagonalTicks d+7*(W*d.tensor.volume)+10)+1))),
  placedKernel.executes (headerRun.executes (jump.executes (moved.executes stop))),?_,rfl,?_,?_,?_⟩
 · unfold UniformGlobalKernelDiagonalExecution.budget
   omega
 · intro r hr j
   exact tags r hr j
 · exact diagonalOut.trans (headOut.trans outputs)
 · exact diagonalRoots.trans (headRoots.trans roots)
end
end ExactFourierCircuits.UniformPreparedKernelDiagonal
