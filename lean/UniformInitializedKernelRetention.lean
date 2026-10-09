import UniformInitializedKernelExecution
import UniformConditionalKernelNumericRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitializedKernelRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformConditionalKernelLayout (Context movementCost)
open UniformInitializedKernelExecution (programFor ready_pc sectors_positive header_code kernel_code)
noncomputable section
attribute [local irreducible] Nat.add
lemma code_space {a B:ℕ} (h:a+647 ≤ B):32+(a+614) ≤ B:=by omega
lemma return_space {a B:ℕ} (h:a+647 ≤ B):a+646 ≤ B:=by omega
lemma shift_bound {k t:ℕ} (h:t ≤ k+57):32+(t+1) ≤ k+90:=by omega
attribute [local irreducible] UniformInitializedKernelExecution.programFor UniformConditionalKernelLayout.programFor

/-- Abstract state boundary prevents normalization of actual initialization
instructions inside the independently verified placed kernel proof. -/
theorem after_header {W F R n:ℕ} (child:Program) (g:Context W F R) (cost:ℕ→ℕ)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s t:State)
 (headRun:BoundedRuns (programFor child W) n x g.metadata.B s 32 t)
 (ready:UniformConditionalKernelLayout.Ready g 0 v t) (tp:t.pc=32)
 (outputs:t.outputs=s.outputs) (roots:t.rootOrders=s.rootOrders)
 (heap:t.natHeap=s.natHeap) (scalar:t.scalarHeap=s.scalarHeap)
 (root:UniformConditionalSectorLoop.RootBody child W n g.inverse.layout.B F R cost x)
 (positive:0 < W) (code:child.length+647 ≤ g.metadata.B):
 ∃u ticks,BoundedExecution (programFor child W) n x g.metadata.B s ticks u ∧
 ticks ≤ movementCost g+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states g.physical)+
  213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90 ∧u.pc=child.length+646 ∧
 (∀r,r < W → ∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (u.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.value=
  some ((UniformSectorTensor.originalTensor (UniformSectorPackingMachine.physicalAxes g.physical)).mulVec
   (fun k=>(v r (finCongr g.physicalVolume k)).value) j)) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < g.packing.suffix → q < g.metadata.rows → q < F →
  q < g.inverse.layout.stack → q < g.inverse.layout.inverse → u.natHeap q=s.natHeap q) ∧
 (∀q,q < g.packing.destination → q < g.gather.buffer → q < F → q < g.scatter.native →
  q < g.inverse.layout.destination → q < g.inverse.destination → u.scalarHeap q=s.scalarHeap q):=by
 let entry:=setPC t 0
 have ep:entry.pc=0:=rfl
 have bound:WordBound g.metadata.B entry:=changePC_bound _ t 0 headRun.final_bound (by omega)
 have readyE:UniformConditionalKernelLayout.Ready g 0 v entry:=ready_pc g v t ready
 have hi:0 < (UniformProducedSectorChildABI.states g.physical).length:=sectors_positive _
 obtain ⟨z,ticks,kernelRun,cheap,zp,values,out,rootOrders,natZ,scalarZ⟩:=UniformConditionalKernelNumericRetention.execution
  child g cost v x entry readyE hi root positive (by omega) ep bound
 have space:32+(UniformConditionalKernelLayout.programFor child W).length ≤ g.metadata.B:=by
  rw[UniformConditionalKernelLayout.program_length]
  exact code_space code
 have moved:=UniformBoundedAssembly.boundedExecution_placed
  (p:=UniformConditionalKernelLayout.programFor child W) (q:=programFor child W)
  (base:=32) (returnPC:=child.length+646) (n:=n) (B:=g.metadata.B) (x:=x)
  (kernel_code child W) space (return_space code) kernelRun
 have placedEntry:placed 32 entry=t:=UniformMultiAxisSectorMetadataPreparation.placed_zero t 32 tp
 rw[placedEntry] at moved
 let u:=setPC z (child.length+646)
 have stop:BoundedExecution (programFor child W) n x g.metadata.B u 1 u:=.halt moved.final_bound
  (by simp[step,u,setPC,UniformInitializedKernelExecution.halt_at])
 refine ⟨u,32+(ticks+1),headRun.executes (moved.executes stop),?_,rfl,values,out.trans outputs,rootOrders.trans roots,?_,?_⟩
 · exact shift_bound cheap
 · intro q suffix metadata before stack inverse
   exact (natZ q suffix metadata before stack inverse).trans (congrFun heap q)
 · intro q packed buffer before native temporary destination
   exact (scalarZ q packed buffer before native temporary destination).trans (congrFun scalar q)

/-- Charged32 ABI initialization followed continuously by the literal
packing→gather→finite common child→scatter→inverse kernel. No Ready is
supplied. RootBody remains the explicit actual recursive proof obligation. -/
theorem execution {W F R n:ℕ} (child:Program) (g:Context W F R) (cost:ℕ→ℕ)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s) (constants:UniformBinaryCStageMachine.Constants s)
 (root:UniformConditionalSectorLoop.RootBody child W n g.inverse.layout.B F R cost x)
 (positive:0 < W) (code:child.length+647 ≤ g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x g.metadata.B s ticks u ∧
 ticks ≤ movementCost g+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states g.physical)+
  213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90 ∧u.pc=child.length+646 ∧
 (∀r,r < W → ∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (u.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.value=
  some ((UniformSectorTensor.originalTensor (UniformSectorPackingMachine.physicalAxes g.physical)).mulVec
   (fun k=>(v r (finCongr g.physicalVolume k)).value) j)) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < g.packing.suffix → q < g.metadata.rows → q < F →
  q < g.inverse.layout.stack → q < g.inverse.layout.inverse → u.natHeap q=s.natHeap q) ∧
 (∀q,q < g.packing.destination → q < g.gather.buffer → q < F → q < g.scatter.native →
  q < g.inverse.layout.destination → q < g.inverse.destination → u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨headRun,ready,heap,scalar,regs,outputs,roots,nat⟩:=UniformKernelHeaderInstallation.execution g
  (programFor child W) x v s input banks source constants (header_code child W) pc (by omega) wb
 have tp:(applyBlock UniformKernelHeaderInstallation.block s).pc=32:=by
  rw[applyBlock_pc,UniformKernelHeaderInstallation.block_length,pc,Nat.zero_add]
 exact after_header child g cost v x s (applyBlock UniformKernelHeaderInstallation.block s)
  headRun ready tp outputs roots heap scalar root positive code
end
end ExactFourierCircuits.UniformInitializedKernelRetention
