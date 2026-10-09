import UniformKernelHeaderInstallation
import UniformPreparedKernelTags
import UniformInitializedKernelExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitializedPreparedKernel
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformConditionalKernelLayout (Context movementCost)
noncomputable section

def programFor (child:Program) (W:ℕ):Program:=UniformKernelHeaderInstallation.block.map Op.code++
 (UniformConditionalKernelLayout.programFor child W).map (relocate 32 (child.length+646))++[.halt]
lemma program_same (child:Program) (W:ℕ):programFor child W=UniformInitializedKernelExecution.programFor child W:=rfl
lemma program_length (child:Program) (W:ℕ):(programFor child W).length=child.length+647:=by
 simp only[programFor,List.length_append,List.length_map,UniformKernelHeaderInstallation.block_length,
  UniformConditionalKernelLayout.program_length,List.length_cons,List.length_nil]
 omega
lemma header_code (child:Program) (W:ℕ):BlockAt UniformKernelHeaderInstallation.block (programFor child W) 0:=by
 exact UniformRankCrossPreparationMachine.block_of_segment UniformKernelHeaderInstallation.block []
  ((UniformConditionalKernelLayout.programFor child W).map (relocate 32 (child.length+646))++[.halt]) 0 rfl
lemma kernel_code (child:Program) (W:ℕ):CodeAt (UniformConditionalKernelLayout.programFor child W)
 (programFor child W) 32 (child.length+646):=by
 exact UniformRankCrossPreparationMachine.segment_code (UniformKernelHeaderInstallation.block.map Op.code)
  [.halt] _ 32 (child.length+646) (by rw[List.length_map,UniformKernelHeaderInstallation.block_length])
lemma halt_at (child:Program) (W:ℕ):(programFor child W)[child.length+646]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformKernelHeaderInstallation.block_length,UniformConditionalKernelLayout.program_length];omega)]
 simp only[List.length_append,List.length_map,UniformKernelHeaderInstallation.block_length,
  UniformConditionalKernelLayout.program_length]
 rw[show child.length+646-(32+(child.length+614))=0 by omega]
 rfl
lemma sectors_positive (axes:List UniformSectorPacking.Axis):0 < (UniformSectorPacking.sectorStates axes).length:=by
 rw[UniformSectorBatchDirectoryMachine.sector_count]
 induction axes with
 | nil=>decide
 | cons a axes ih=>
  have positive:0 < a.widths.length:=by
   by_contra no
   have empty:a.widths=[]:=List.length_eq_zero_iff.mp (by omega)
   have h:=a.radix_two
   simp[empty] at h
  exact Nat.mul_pos positive ih

lemma ready_pc {W F R ordinal pc:ℕ} (g:Context W F R) (v:ℕ→Fin g.packing.volume→Scalar) (s:State)
 (h:UniformConditionalKernelLayout.Ready g ordinal v s):
 UniformConditionalKernelLayout.Ready g ordinal v (setPC s pc):=by
 refine ⟨?_,?_,h.source,h.count,h.axes,h.metadataRows,h.suffix,h.stack,h.directory,
  h.batchDirectory,h.childBank,h.native,h.volume,h.ordinal,h.frontier,?_,h.constants⟩
 · exact ⟨h.packing.volume,h.packing.source,h.packing.destination,h.packing.axes,
    h.packing.rows,h.packing.suffix,h.packing.stack,h.packing.inverse⟩
 · exact UniformGlobalRolePackingMachine.banks_transfer g.packing g.physical g.physicalLength h.banks
    (fun _ _ _ _=>rfl) g.widthsBelow g.permutationsBelow
 · cases h.inverse
   constructor <;>assumption

attribute [local irreducible] Nat.add
lemma code_space {a B:ℕ} (h:a+647 ≤ B):32+(a+614) ≤ B:=by omega
lemma return_space {a B:ℕ} (h:a+647 ≤ B):a+646 ≤ B:=by omega
lemma shift_bound {k t:ℕ} (h:t ≤ k+57):32+(t+1) ≤ k+90:=by omega
attribute [local irreducible] programFor UniformConditionalKernelLayout.programFor

/-- Abstract state boundary prevents normalization of actual initialization
instructions inside the independently verified placed kernel proof. -/
theorem after_header {W F R n:ℕ} (child:Program) (g:Context W F R) (cost:ℕ→ℕ)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s t:State)
 (headRun:BoundedRuns (programFor child W) n x g.metadata.B s 32 t)
 (ready:UniformConditionalKernelLayout.Ready g 0 v t) (tp:t.pc=32)
 (outputs:t.outputs=s.outputs) (roots:t.rootOrders=s.rootOrders)
 (root:UniformPreparedSectorLoop.RootBody child W n g.inverse.layout.B F R cost x)
 (prepared:∀r,r<W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0 < W) (code:child.length+647 ≤ g.metadata.B):
 ∃u ticks,BoundedExecution (programFor child W) n x g.metadata.B s ticks u ∧
 ticks ≤ movementCost g+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states g.physical)+
  213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90 ∧u.pc=child.length+646 ∧
 (∀r,r < W → ∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (u.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.dependent=
  some false) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let entry:=setPC t 0
 have ep:entry.pc=0:=rfl
 have bound:WordBound g.metadata.B entry:=changePC_bound _ t 0 headRun.final_bound (by omega)
 have readyE:UniformConditionalKernelLayout.Ready g 0 v entry:=ready_pc g v t ready
 have hi:0 < (UniformProducedSectorChildABI.states g.physical).length:=sectors_positive _
 obtain ⟨z,ticks,kernelRun,cheap,zp,values,out,rootOrders⟩:=UniformPreparedKernelTags.execution
  child g cost v x entry readyE hi root prepared positive (by omega) ep bound
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
  (by simp[step,u,setPC,halt_at])
 refine ⟨u,32+(ticks+1),headRun.executes (moved.executes stop),?_,rfl,values,out.trans outputs,rootOrders.trans roots⟩
 exact shift_bound cheap

/-- Charged32 ABI initialization followed continuously by the literal
packing→gather→finite common child→scatter→inverse kernel. No Ready is
supplied. RootBody remains the explicit actual recursive proof obligation. -/
theorem execution {W F R n:ℕ} (child:Program) (g:Context W F R) (cost:ℕ→ℕ)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s) (constants:UniformBinaryCStageMachine.Constants s)
 (root:UniformPreparedSectorLoop.RootBody child W n g.inverse.layout.B F R cost x)
 (prepared:∀r,r<W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0 < W) (code:child.length+647 ≤ g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x g.metadata.B s ticks u ∧
 ticks ≤ movementCost g+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states g.physical)+
  213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90 ∧u.pc=child.length+646 ∧
 (∀r,r < W → ∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (u.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.dependent=
  some false) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders :=by
 obtain ⟨headRun,ready,heap,scalar,regs,outputs,roots,nat⟩:=UniformKernelHeaderInstallation.execution g
  (programFor child W) x v s input banks source constants (header_code child W) pc (by omega) wb
 have tp:(applyBlock UniformKernelHeaderInstallation.block s).pc=32:=by
  rw[applyBlock_pc,UniformKernelHeaderInstallation.block_length,pc,Nat.zero_add]
 exact after_header child g cost v x s (applyBlock UniformKernelHeaderInstallation.block s)
  headRun ready tp outputs roots root prepared positive code
end
end ExactFourierCircuits.UniformInitializedPreparedKernel
