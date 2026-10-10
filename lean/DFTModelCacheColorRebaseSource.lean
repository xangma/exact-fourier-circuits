import DFTModelCacheColorRebaseProgram
import DFTModelCacheColorShift

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorRebase
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelRecursiveScalarCore
open DFTModelCacheMatchingNat (Budget tab_program_budget fork_budget)
open UniformMatchingAxisTableMachine (InRange)
noncomputable section

/-- Physical coordinates are shifted; local coordinates are passed to native51.
The third physical coefficient word is unchanged by the charged rebase. -/
theorem local_rows {M : ℕ} (A : ℕ) (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
 (physical : DFTModelCacheColor.Rows (shiftedEdges A E) z) :
 DFTModelCacheColor.Rows E (localRows A z) := by
 refine ⟨physical.length,?_⟩
 intro i
 have index:i.val<z.len := physical.length.symm ▸ i.isLt
 have endpoints:=physical.endpoints i
 change ((localRows A z).look i.val Row.blank).1 = (E i).left ∧
   ((localRows A z).look i.val Row.blank).2.1 = (E i).right
 unfold localRows
 simp only [Tape.look_of_lt (Tape.tab z.len (rebaseValue A z)) Row.blank index]
 change (z.look i.val Row.blank).1-A=(E i).left ∧ (z.look i.val Row.blank).2.1-A=(E i).right
 have left:(z.look i.val Row.blank).1=A+(E i).left := endpoints.1
 have right:(z.look i.val Row.blank).2.1=A+(E i).right := endpoints.2
 rw [left,right]
 simp only [Nat.add_sub_cancel_left]
 exact ⟨trivial,trivial⟩

theorem label_preserved (A : ℕ) (z : Tape Row.T) (j : ℕ) (hj : j<z.len) :
 ((localRows A z).look j Row.blank).2.2=(z.look j Row.blank).2.2 := by
 unfold localRows
 rw [Tape.look_of_lt (Tape.tab z.len (rebaseValue A z)) Row.blank hj]
 rfl

theorem rebaseRow_bounds {M : ℕ} (A r : ℕ) (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
 (physical : DFTModelCacheColor.Rows (shiftedEdges A E) z) (range : InRange r E)
 (j : ℕ) (hj : j<z.len) : Budget (run rebaseRow ((A,(r,z)),j)) 51 r := by
 have ji:j<M := physical.length ▸ hj
 have left:(z.look j Row.blank).1=A+(E ⟨j,ji⟩).left := (physical.endpoints ⟨j,ji⟩).1
 have right:(z.look j Row.blank).2.1=A+(E ⟨j,ji⟩).right := (physical.endpoints ⟨j,ji⟩).2
 have bound:=range ⟨j,ji⟩
 rw [rebaseRow_run]
 change True ∧ 51≤51 ∧ max ((z.look j Row.blank).1-A) ((z.look j Row.blank).2.1-A)≤r
 rw [left,right]
 simp only [Nat.add_sub_cancel_left]
 exact ⟨trivial,le_rfl,max_le (Nat.le_of_lt bound.1) (Nat.le_of_lt bound.2)⟩

attribute [local irreducible] Code.run

/-- Work, heap sizes and runtime allocations are independent of A. In
particular no tape of length A+localBound is allocated. -/
theorem prepare_bounds {M : ℕ} (A r : ℕ) (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
 (physical : DFTModelCacheColor.Rows (shiftedEdges A E) z) (range : InRange r E) :
 Budget (run prepare (A,(r,z))) (12+55*z.len) (max z.len r) := by
 have cells:=tab_program_budget count rebaseRow (A,(r,z)) 51 r
  (by rw [count_run];trivial) (by
    intro j hj
    rw [count_run] at hj
    dsimp only [Bill.val] at hj
    exact rebaseRow_bounds A r z E physical range j hj)
 rw [count_run] at cells
 have rb:Budget (run (.tab count rebaseRow) (A,(r,z))) (8+55*z.len) (max z.len r) := by
  change Budget (run (.tab count rebaseRow) (A,(r,z))) (8+55*z.len)
    (max z.len (max z.len r)) at cells
  simpa only [←max_assoc,max_self] using cells
 have cb:Budget (run localBound (A,(r,z))) 3 (max z.len r) := by
  simp [Budget,localBound,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
 have assembled:=fork_budget localBound (.tab count rebaseRow) (A,(r,z)) 3 (8+55*z.len) (max z.len r) cb rb
 change Budget (run prepare (A,(r,z))) (3+(8+55*z.len)+1) (max z.len r) at assembled
 have arithmetic:3+(8+55*z.len)+1=12+55*z.len := by ring
 rw [arithmetic] at assembled
 exact assembled

end
end ExactFourierCircuits.DFTModelCacheColorRebase
