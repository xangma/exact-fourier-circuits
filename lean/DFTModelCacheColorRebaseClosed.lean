import DFTModelCacheColorRebaseSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorRebase
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open UniformMatchingAxisTableMachine (InRange)
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] Code.run DFTModelCacheColor.program prepare

def workBound (r M : ℕ) : ℕ := DFTModelCacheColor.workBound r M+55*M+15
def peakBound (r M : ℕ) : ℕ := max (max M r) (DFTModelCacheColor.peakBound r M)

theorem retained_comp_run {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
 run (.fork (.atom .id) (.comp f g)) x=
 ⟨(x,(run g (run f x).val).val),(run f x).work+(run g (run f x).val).work+3,
 max (run f x).peak (run g (run f x).val).peak,
 (run f x).valid ∧ (run g (run f x).val).valid⟩ := by
 simp only [fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,true_and,and_true]
 congr 1
 omega

theorem program_run (A r:ℕ) (z:Tape Row.T) :
 run program (A,(r,z))=
 ⟨((A,(r,z)),(run DFTModelCacheColor.program (r,localRows A z)).val),
 (run prepare (A,(r,z))).work+(run DFTModelCacheColor.program (r,localRows A z)).work+3,
 max (run prepare (A,(r,z))).peak (run DFTModelCacheColor.program (r,localRows A z)).peak,
 (run prepare (A,(r,z))).valid ∧ (run DFTModelCacheColor.program (r,localRows A z)).valid⟩ := by
 rw [program,retained_comp_run,prepare_value]

attribute [local irreducible] program

/-- The native state and heap use local coordinates. Colors apply to the
original shifted graph; physical rows and labels remain available verbatim.
The charged work and allocations do not depend on the physical base A. -/
theorem execution {M : ℕ} (A r n : ℕ) (x : Fin n→ℂ) (z : Tape Row.T)
 (E : Fin M→UniformColoring.Edge)
 (physical : DFTModelCacheColor.Rows (shiftedEdges A E) z) (range : InRange r E) :
 ∃t u,t≤UniformGreedyColorMachine.runtimeBudget z.len ∧
 UniformMachine.BoundedExecution UniformGreedyColorMachine.program n x
  (DFTModelCacheColor.B r z.len) (DFTModelCacheColor.sourceState r (localRows A z)) t u ∧
 u.pc=50 ∧ (run program (A,(r,z))).valid ∧
 (run program (A,(r,z))).val.1=(A,(r,z)) ∧
 (run program (A,(r,z))).val.2.2.2.len=M ∧
 (∀i:Fin M,(run program (A,(r,z))).val.2.2.2.look i.val 0=
  UniformColoring.greedy (shiftedEdges A E) 11 M i.val) ∧
 (run program (A,(r,z))).work≤workBound r z.len ∧
 (run program (A,(r,z))).peak≤peakBound r z.len := by
 have localRowsCert:=local_rows A z E physical
 obtain ⟨t,u,time,actual,pc,valid,_,_,length,colors,_,work,peak⟩ :=
  DFTModelCacheColor.execution r n x (localRows A z) E localRowsCert range
 have prep:=prepare_bounds A r z E physical range
 rw [program_run]
 refine ⟨t,u,time,actual,pc,⟨prep.1,valid⟩,rfl,length,?_,?_,?_⟩
 · intro i
   rw [greedy_shift]
   exact colors i
 · change (run prepare (A,(r,z))).work+(run DFTModelCacheColor.program (r,localRows A z)).work+3≤_
   change (run DFTModelCacheColor.program (r,localRows A z)).work≤DFTModelCacheColor.workBound r z.len at work
   have hp:=prep.2.1
   unfold workBound
   omega
 · exact max_le_max prep.2.2 peak

/-- The selected physical graph is degree six, but the charged execution uses
only its small local endpoint bound. The physical matching radix stays separate. -/
theorem degree_six {M : ℕ} (A r n : ℕ) (x : Fin n→ℂ) (z : Tape Row.T)
 (E : Fin M→UniformColoring.Edge)
 (physical : DFTModelCacheColor.Rows (shiftedEdges A E) z) (range : InRange r E)
 (degree : UniformColoring.DegreeBound (shiftedEdges A E) 6) :
 (run program (A,(r,z))).valid ∧ (run program (A,(r,z))).val.2.2.2.len=M ∧
 (∀i:Fin M,(run program (A,(r,z))).val.2.2.2.look i.val 0=
  UniformColoring.coloring (shiftedEdges A E) 6 i) ∧
 (∀i:Fin M,(run program (A,(r,z))).val.2.2.2.look i.val 0<11) ∧
 (∀i j:Fin M,i≠j→(run program (A,(r,z))).val.2.2.2.look i.val 0=
  (run program (A,(r,z))).val.2.2.2.look j.val 0→
  ¬UniformColoring.Conflict (shiftedEdges A E i) (shiftedEdges A E j)) := by
 have proper:=DFTModelCacheColor.degree_six r n x (localRows A z) E
  (local_rows A z E physical) range (degree_unshift A E 6 degree)
 have prep:=prepare_bounds A r z E physical range
 rw [program_run]
 refine ⟨⟨prep.1,proper.1⟩,proper.2.1,?_,proper.2.2.2.1,?_⟩
 · intro i
   rw [coloring_shift]
   exact proper.2.2.1 i
 · intro i j different same
   exact (conflict_shift A (E i) (E j)).not.mpr (proper.2.2.2.2 i j different same)

end
end ExactFourierCircuits.DFTModelCacheColorRebase
