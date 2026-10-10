import DFTModelSavingNativeRoot
import DFTModelSavingNativeControl
import DFTModelSectorTransposeSaving
import DFTModelSectorTransposeScatterSource
import UniformSameProgramSectorLoop

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, pp.11–12 and §4.3, Proposition 4.2, p.20.
One genuine generated sector calls the closed saving child through the original
nine source instructions. This does not assert a complete sector loop or an
outer cache/compiler. No source instruction is inserted in the held assembly. -/
namespace ExactFourierCircuits.DFTModelGlobalSectorSaving
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformAssembly UniformBoundedAssembly
open UniformTensorMonomialMachine DFTModelAdmissibilityControl DFTModelAffine
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program DFTModelSavingProgram.program

def ready (s : State) : State :=
 setPC (applyBlock UniformSameProgramSectorLoop.setup s) 0

lemma ready_heaps (s : State) :
 (ready s).natHeap=s.natHeap ∧ (ready s).scalarHeap=s.scalarHeap ∧
 (ready s).scalarReg=s.scalarReg ∧ (ready s).outputs=s.outputs ∧
 (ready s).rootOrders=s.rootOrders := by
 exact UniformSameProgramSectorLoop.setup_heaps s

/-- The entry has a real BatchCell and physical child data. The result joins
the actual nine setup instructions and the unchanged placed recursive child,
including its charged continuation jump. -/
theorem execution (n B M E A F i K : ℕ)
 (st : UniformSectorPacking.BlockState) (x : Fin n→ℂ) (s s0 : State)
 (input input0 : Fin DFTModelSavingNativeRoot.W→Fin (2^st.pairs)→Scalar)
 (same : StateMatch s s0)
 (cursor : UniformSameProgramSectorLoop.Cursor M E F i s) (hi : i<M)
 (cell : UniformSectorBatchDirectoryMachine.BatchCell
   DFTModelSavingNativeRoot.W E A i st s)
 (width : st.width=2^st.pairs)
 (data : UniformFixedNetworkShearChildMachine.Present
   (A+DFTModelSavingNativeRoot.W*st.start) DFTModelSavingNativeRoot.W (2^st.pairs) input s)
 (data0 : UniformFixedNetworkShearChildMachine.Present
   (A+DFTModelSavingNativeRoot.W*st.start) DFTModelSavingNativeRoot.W (2^st.pairs) input0 s0)
 (base : 3≤A+DFTModelSavingNativeRoot.W*st.start)
 (extent : A+DFTModelSavingNativeRoot.W*st.start+
   DFTModelSavingNativeRoot.W*2^st.pairs≤F)
 (directoryFit : E+5*M≤B)
 (code : UniformSameProgramSectorLoop.program.length≤B)
 (room : F+34*(st.pairs+1)+DFTModelSavingNativeRoot.R.reserve*(st.pairs+1)*2^st.pairs≤B)
 (square : (2^st.pairs)^2≤B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K)
 (constants : UniformBinaryCStageMachine.Constants s)
 (pc : s.pc=8) (wb : WordBound B s) :
 ∃u u0 ticks output output0,
 BoundedRuns UniformSameProgramSectorLoop.program n x B s (9+ticks)
   (setPC u (17+UniformRecursiveSavingProgram.program.length)) ∧
 BoundedRuns UniformSameProgramSectorLoop.program n (fun _=>0) B s0 (9+ticks)
   (setPC u0 (17+UniformRecursiveSavingProgram.program.length)) ∧
 DFTModelSavingNativeRoot.Result n B st.pairs
   (A+DFTModelSavingNativeRoot.W*st.start) F K x (ready s) (ready s0)
   u u0 ticks input input0 output output0 := by
 have qb : st.pairs≤B := (wb.2.2.1 _ _ cell.1).2
 have vb : st.width≤B := (wb.2.2.1 _ _ cell.2.1).2
 have ab : A+DFTModelSavingNativeRoot.W*st.start≤B :=
   (wb.2.2.1 _ _ cell.2.2.1).2
 have fb : F≤B := by omega
 obtain ⟨setup,header,dp⟩ := UniformSameProgramSectorLoop.setup_execution st x s cursor hi
   directoryFit cell qb vb ab fb code pc wb
 have cursor0 : UniformSameProgramSectorLoop.Cursor M E F i s0 := by
   constructor
   all_goals rw [same.natReg]
   all_goals first | exact cursor.count | exact cursor.one | exact cursor.index |
     exact cursor.directory | exact cursor.fresh | exact cursor.zero | exact cursor.five
 have cell0 : UniformSectorBatchDirectoryMachine.BatchCell
   DFTModelSavingNativeRoot.W E A i st s0 := by
   simpa only [UniformSectorBatchDirectoryMachine.BatchCell,same.natHeap] using cell
 obtain ⟨setup0,_,_⟩ := UniformSameProgramSectorLoop.setup_execution st (fun _=>0) s0
   cursor0 hi directoryFit cell0 qb vb ab fb code (same.pc.trans pc) (same.wordBound wb)
 have matched := DFTModelSavingNativeControl.paired_runs setup setup0 same
 have bound : WordBound B (ready s) :=
   changePC_bound B _ 0 setup.final_bound (by omega)
 have size : (ready s).natReg 4122=2^st.pairs := header.width.trans width
 have cc : UniformBinaryCStageMachine.Constants (ready s) := constants
 obtain ⟨u,u0,ticks,output,output0,result⟩ := DFTModelSavingNativeRoot.execution
   n B st.pairs (A+DFTModelSavingNativeRoot.W*st.start) F K x (ready s) (ready s0)
   input input0 cap (matched.withPC 0) rfl header.exponent header.base size header.frontier dp
   data data0 base extent
   (by have h:=code;rw [UniformSameProgramSectorLoop.program_length] at h;omega)
   room square cc bound
 have fit : 17+UniformRecursiveSavingProgram.program.length≤B := by
   rw [UniformSameProgramSectorLoop.program_length] at code;omega
 have actual := boundedExecution_placed UniformSameProgramSectorLoop.actual_child_code
   fit fit result.actual
 have baseline := boundedExecution_placed UniformSameProgramSectorLoop.actual_child_code
   fit fit result.baseline
 have setupPC : (applyBlock UniformSameProgramSectorLoop.setup s).pc=17 := by
   rw [applyBlock_pc,UniformSameProgramSectorLoop.setup_length,pc]
 have setupPC0 : (applyBlock UniformSameProgramSectorLoop.setup s0).pc=17 := by
   rw [applyBlock_pc,UniformSameProgramSectorLoop.setup_length,same.pc,pc]
 have placedReady := UniformMultiAxisSectorMetadataPreparation.placed_zero
   (applyBlock UniformSameProgramSectorLoop.setup s) 17 setupPC
 have placedReady0 := UniformMultiAxisSectorMetadataPreparation.placed_zero
   (applyBlock UniformSameProgramSectorLoop.setup s0) 17 setupPC0
 change placed 17 (ready s)=_ at placedReady
 change placed 17 (ready s0)=_ at placedReady0
 rw [placedReady] at actual
 rw [placedReady0] at baseline
 exact ⟨u,u0,ticks,output,output0,setup.trans actual,setup0.trans baseline,result⟩

end
end ExactFourierCircuits.DFTModelGlobalSectorSaving
