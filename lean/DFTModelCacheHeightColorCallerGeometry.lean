import DFTModelCacheHeightColorCallerProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightColorCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section

abbrev dag := DFTModelCacheHeightRaw.dag
def localBound (a e:ℕ) : ℕ := e+1+(dag a e).size
def bucket (a e d:ℕ) (enabled:Bool) :=
 UniformCrossDepthReplayPreparation.bucket (dag a e).program enabled d
def edges (a e d:ℕ) (enabled:Bool) := printedEdges (bucket a e d enabled)
def nativeRows (a e A C P d:ℕ) (enabled:Bool) :=
 (bucket a e d enabled).map (UniformCrossShearTableMachine.shiftedRow A
  (UniformCrossShearTableMachine.locations
    (UniformToeplitzCrossDAG.bankSize (DFTModelCacheTopology.exponent a e)) C C P))
def input (c a e A C P d:ℕ) (enabled:Bool) : Input.T :=
 (c,((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e)))
def producedRows (a e A C P d:ℕ) (enabled:Bool) :=
 (run DFTModelCacheHeightRaw.program (input 0 a e A C P d enabled).2).val.2

attribute [local irreducible] Code.run DFTModelCacheHeightRaw.program

/-- Input ports are included. Final copy-to-output ports are not in the DAG bucket. -/
theorem local_range (a e d:ℕ) (enabled:Bool) :
 InRange (localBound a e) (edges a e d enabled) := by
 intro i
 have member:(bucket a e d enabled).get i∈
  UniformDAGLayers.natSweep (dag a e).program enabled :=
  (List.mem_filter.mp (List.get_mem _ i)).1
 have h:=UniformDAGLayers.natSweep_bounds (dag a e).program enabled _ member
 exact ⟨h.2.1,h.2.2.trans h.2.1⟩

theorem degree_six (a e A d:ℕ) (enabled:Bool) :
 DegreeBound (DFTModelCacheColorRebase.shiftedEdges A (edges a e d enabled)) 6 := by
 exact DFTModelCacheHeightRaw.native_degree a e A d enabled

theorem physical_range (a e A R d:ℕ) (enabled:Bool)
 (fit:A+localBound a e≤R) :
 InRange R (DFTModelCacheColorRebase.shiftedEdges A (edges a e d enabled)) := by
 intro i
 have h:=local_range a e d enabled i
 change A+_ < R ∧ A+_ < R
 constructor <;> omega

theorem generated_count (config:DFTModelCacheHeightRaw.Config.T) (a e:ℕ) :
 (run DFTModelCacheHeightRaw.program (config,(a,e))).val.1.1.2.1=(dag a e).size := by
 obtain ⟨u,t,source⟩:=DFTModelCacheTopology.execution_values a e
 rw [DFTModelCacheHeightRaw.program_run]
 change (run DFTModelCacheBucketRaw.program (a,e)).val.1.2.1=_
 rw [DFTModelCacheBucketRaw.program_value]
 exact source.count.trans (DFTModelCacheTopology.typed_count _ _ _
  (DFTModelCacheTopology.dimensions_fit a e).1
  (DFTModelCacheTopology.dimensions_fit a e).2).symm

theorem argument_value (c a e A C P d:ℕ) (enabled:Bool) :
 argumentValue (input c a e A C P d enabled)
  (run DFTModelCacheHeightRaw.program (input c a e A C P d enabled).2).val=
 (c,(A,(localBound a e,producedRows a e A C P d enabled))) := by
 unfold argumentValue input localBound producedRows
 rw [generated_count]
 rfl

theorem rows_value (a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 producedRows a e A C P d enabled=DFTModelCacheHeight.rowTape (nativeRows a e A C P d enabled) :=
 DFTModelCacheHeightRaw.program_value a e A C C P d enabled height

theorem physical_rows (a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 DFTModelCacheColor.Rows
  (DFTModelCacheColorRebase.shiftedEdges A (edges a e d enabled))
  (producedRows a e A C P d enabled) := by
 rw [rows_value a e A C P d enabled height]
 refine ⟨by simp [DFTModelCacheHeight.rowTape,nativeRows,bucket,Tape.tab],?_⟩
 intro i
 have hi:i.val<(nativeRows a e A C P d enabled).length := by
  simpa only [nativeRows,List.length_map] using i.isLt
 unfold DFTModelCacheHeight.rowTape
 rw [Tape.look_of_lt _ _ hi]
 change (((nativeRows a e A C P d enabled).map DFTModelCacheHeight.row3)[i.val]?.getD
  DFTModelCacheHeight.Row.blank).1=_ ∧
  (((nativeRows a e A C P d enabled).map DFTModelCacheHeight.row3)[i.val]?.getD
  DFTModelCacheHeight.Row.blank).2.1=_
 simp only [nativeRows,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
  Option.map_some,Option.getD_some]
 exact ⟨rfl,rfl⟩

theorem rows_length (a e A C P d:ℕ) (enabled:Bool) :
 (producedRows a e A C P d enabled).len≤2*(dag a e).size := by
 unfold producedRows
 rw [DFTModelCacheHeightRaw.program_run]
 dsimp only
 rw [DFTModelCacheHeight.program_value]
 exact (DFTModelCacheHeight.rowsPrefix_length _ _).trans
  (DFTModelCacheHeightRaw.selected_slotCount_le a e A C P d enabled)

end
end ExactFourierCircuits.DFTModelCacheHeightColorCaller
