import DFTModelCacheHeightColorCallerGeometry
import UniformColorLayerTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightColorCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section

def selectionInput (c a e A C P d:ℕ) (enabled:Bool) :=
 DFTModelCacheColorRebaseSelected.selectionInput c A (localBound a e)
  (producedRows a e A C P d enabled)
def colored (a e A C P d:ℕ) (enabled:Bool) :=
 DFTModelCacheColorRebaseSelected.colored A (localBound a e) (producedRows a e A C P d enabled)
def selectedEdges (c a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :=
 DFTModelCacheColorSelection.selectedEdges (selectionInput c a e A C P d enabled)
  (DFTModelCacheColorRebase.shiftedEdges A (edges a e d enabled))
  (physical_rows a e A C P d enabled height).length

theorem program_source_run (c a e A C P d:ℕ) (enabled:Bool) :
 run program (input c a e A C P d enabled)=
 let h:=run DFTModelCacheHeightRaw.program (input c a e A C P d enabled).2
 let z:=producedRows a e A C P d enabled
 let b:=run DFTModelCacheColorRebaseSelected.program (c,(A,(localBound a e,z)))
 ⟨(((input c a e A C P d enabled),h.val),b.val),h.work+b.work+47,
 max h.peak (max (localBound a e) b.peak),h.valid∧b.valid⟩ := by
 rw [program_run]
 dsimp only
 rw [argument_value,generated_count]
 rfl

attribute [local irreducible] Code.run program DFTModelCacheHeightRaw.program
 DFTModelCacheColorRebaseSelected.program DFTModelCacheColorSelection.program

def workBudget (a e:ℕ) : ℕ :=
 DFTModelCacheHeightRaw.localWorkBudget a e+
  50002000*(localBound a e+2*(dag a e).size+1)^3+47

/-- The only physical range condition is ordinary placement of the genuine
logical port span. Rows, colors, degree and matching are all produced/derived. -/
theorem specification (c a e A C P d R:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6)
 (fit:A+localBound a e≤R) :
 ∃u ticks,DFTModelCacheTopology.Result a e u ticks ∧
 (run program (input c a e A C P d enabled)).valid ∧
 (run program (input c a e A C P d enabled)).work≤workBudget a e ∧
 (run program (input c a e A C P d enabled)).val.1.1=input c a e A C P d enabled ∧
 (run program (input c a e A C P d enabled)).val.1.2=
  (run DFTModelCacheHeightRaw.program (input c a e A C P d enabled).2).val ∧
 DFTModelCacheMatchingNat.Rows (selectedEdges c a e A C P d enabled height)
  (run program (input c a e A C P d enabled)).val.2.2 ∧
 Matching (selectedEdges c a e A C P d enabled height) ∧
 InRange R (selectedEdges c a e A C P d enabled height) := by
 obtain ⟨u,ticks,source,raw⟩:=DFTModelCacheHeightRaw.execution_local a e A C P d enabled
 have chosen:=DFTModelCacheColorRebaseSelected.specification c A (localBound a e) R 0
  (fun i=>Fin.elim0 i) (producedRows a e A C P d enabled) (edges a e d enabled)
  (physical_rows a e A C P d enabled height) (local_range a e d enabled)
  (physical_range a e A R d enabled fit) (degree_six a e A d enabled)
 have polynomial:=DFTModelCacheColorRebaseSelected.polynomial_work (localBound a e)
  (producedRows a e A C P d enabled).len
 have length:=rows_length a e A C P d enabled
 have cube:=Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_left length (localBound a e)) 1) 3
 rw [program_source_run]
 refine ⟨u,ticks,source,⟨raw.1,chosen.1⟩,?_,rfl,rfl,chosen.2.2.2.1,
  chosen.2.2.2.2.1,chosen.2.2.2.2.2⟩
 have r:=raw.2.1
 have b:=chosen.2.1
 have p:=polynomial.trans (Nat.mul_le_mul_left 50002000 cube)
 dsimp only [input] at *
 unfold workBudget
 omega

/-- Every compacted output is one original occurrence, including its unchanged
coefficient label. There is no quotient by equal rows or zero coefficients. -/
theorem selected_row (c a e A C P d:ℕ) (enabled:Bool)
 (i:Fin (DFTModelCacheColorSelection.indices (selectionInput c a e A C P d enabled)).length) :
 (run program (input c a e A C P d enabled)).val.2.2.look i.val DFTModelCacheColor.Row.blank=
 (producedRows a e A C P d enabled).look
  (DFTModelCacheColorSelection.originalIndex (selectionInput c a e A C P d enabled) i).val
  DFTModelCacheColor.Row.blank := by
 rw [program_source_run]
 dsimp only
 rw [DFTModelCacheColorRebaseSelected.program_run]
 dsimp only
 exact DFTModelCacheColorSelection.selected_row _ i

/-- Computed colors agree with the genuine native chronological occurrence graph. -/
theorem colors_value (a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 (colored a e A C P d enabled).2.2.2.len=(bucket a e d enabled).length ∧
 ∀i:Fin (bucket a e d enabled).length,
  (colored a e A C P d enabled).2.2.2.look i.val 0=
   greedy (edges a e d enabled) 11 (bucket a e d enabled).length i.val := by
 obtain ⟨_,_,_,_,_,_,_,length,colors,_,_⟩:=DFTModelCacheColorRebase.execution A
  (localBound a e) 0 (fun i=>Fin.elim0 i) (producedRows a e A C P d enabled)
  (edges a e d enabled) (physical_rows a e A C P d enabled height) (local_range a e d enabled)
 refine ⟨length,?_⟩
 intro i
 unfold colored DFTModelCacheColorRebaseSelected.colored
 rw [colors i,DFTModelCacheColorRebase.greedy_shift]

/-- Literal stable occurrence indices agree with native color-layer selection. -/
theorem indices_eq (c a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 DFTModelCacheColorSelection.indices (selectionInput c a e A C P d enabled)=
 UniformColorLayerTableMachine.selected (bucket a e d enabled).length c
  (greedy (edges a e d enabled) 11 (bucket a e d enabled).length) := by
 have length: (producedRows a e A C P d enabled).len=(bucket a e d enabled).length :=
  (physical_rows a e A C P d enabled height).length
 unfold DFTModelCacheColorSelection.indices UniformColorLayerTableMachine.selected
 change (List.range (producedRows a e A C P d enabled).len).filter _=_
 rw [length]
 apply List.filter_congr
 intro j hj
 have bound:j<(bucket a e d enabled).length:=List.mem_range.mp hj
 have color: (colored a e A C P d enabled).2.2.2.look j 0=
  greedy (edges a e d enabled) 11 (bucket a e d enabled).length j:=
  (colors_value a e A C P d enabled height).2 ⟨j,bound⟩
 change decide ((colored a e A C P d enabled).2.2.2.look j 0=c)=_
 rw [color]

/-- Exact selected tape, expressed directly in stable native occurrence order.
Labels are looked up from the ORIGINAL physical tape without recomputation. -/
theorem selected_value (c a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 (run program (input c a e A C P d enabled)).val.2.2=
 let is:=UniformColorLayerTableMachine.selected (bucket a e d enabled).length c
  (greedy (edges a e d enabled) 11 (bucket a e d enabled).length)
 Tape.tab is.length (fun j=>
  (is.map (fun k=>(producedRows a e A C P d enabled).look k DFTModelCacheColor.Row.blank))[j]?.getD
    DFTModelCacheColor.Row.blank) := by
 rw [program_source_run]
 dsimp only
 rw [DFTModelCacheColorRebaseSelected.program_run]
 dsimp only
 rw [DFTModelCacheColorSelection.program_value,DFTModelCacheColorSelection.rowsPrefix_map]
 change Tape.tab _ _=Tape.tab _ _
 rw [←indices_eq c a e A C P d enabled height]
 simp only [List.length_map]
 rfl

end
end ExactFourierCircuits.DFTModelCacheHeightColorCaller
