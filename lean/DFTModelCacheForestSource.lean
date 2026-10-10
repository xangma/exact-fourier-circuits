import DFTModelCacheForest
import UniformNewtonTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier UniformMachine
noncomputable section

def field (v : Row.T) (q : Fin 5) : ℂ :=
  if q.val=0 then v.1 else if q.val=1 then v.2.1 else
    if q.val=2 then v.2.2.1 else if q.val=3 then v.2.2.2.1 else v.2.2.2.2

theorem row_field (omega : ℂ) (j : ℕ) (q : Fin 5) :
    field (row omega j) q=UniformNewton.Preparation.expected omega j q := by
  fin_cases q <;> rfl

/-- Exact output ordering of the real Newton DAG, including both reciprocals. -/
theorem source_table_values {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) (j : Fin r) (q : Fin 5) :
    field ((run program (r,omega)).val.look j.val Row.blank) q=
      (UniformNewton.Preparation.table r).run (UniformNewton.Preparation.roots omega)
        (UniformNewton.Preparation.table_admissible hr primitive) (finProdFinEquiv (j,q)) := by
  rw [program_lookup,row_field,UniformNewton.Preparation.table_run hr primitive]

def SourceValues (r a : ℕ) (t : Tape Row.T) (u : State) : Prop :=
  t.len=r ∧ ∀j : Fin r,∀q : Fin 5,
    u.scalarHeap (a+((UniformNewton.Preparation.table r).output (finProdFinEquiv (j,q))).val)=
      some ⟨field (t.look j.val Row.blank) q,false⟩

theorem prepared_values {r a : ℕ} {omega : ℂ} {u : State}
    (outputs : UniformNewtonTableMachine.PreparedOutputs r omega a u) :
    SourceValues r a (run program (r,omega)).val u := by
  refine ⟨program_length r omega,?_⟩
  intro j q
  rw [program_lookup,row_field]
  exact outputs j q

/-- Genuine native preparation and the closed typed producer agree. The entry
contains only the primitive root, ordinary allocator headers and retained low
scalars; no produced Newton row or coefficient-table premise is supplied. -/
theorem actual_preparation (n : ℕ) (x : Fin n→ℂ) (r a scratch source B : ℕ)
    (omega : ℂ) (bank : Fin 6→Scalar) (s : State)
    (hr : 0<r) (primitive : IsPrimitiveRoot omega r)
    (layout : UniformNewtonTableMachine.Layout r a scratch source)
    (pc : s.pc=0) (h16 : s.natReg 16=r) (h17 : s.natReg 17=a)
    (h18 : s.natReg 18=source) (h19 : s.natReg 19=scratch)
    (retained : UniformNewtonTableMachine.Bank bank s)
    (axis : s.scalarHeap source=some ⟨omega,false⟩)
    (fit : a+32*r+300≤B) (scratchFit : scratch+6≤B) (wb : WordBound B s) :
    ∃u,BoundedExecution UniformNewtonTableMachine.program n x B s (252*r+170) u ∧
      SourceValues r a (run program (r,omega)).val u ∧
      UniformNewtonTableMachine.Bank bank u ∧
      u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
      u.natHeap=UniformNewtonTableMachine.putWords 0
        (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap ∧
      (∀i,6 ≤ i → (i < a ∨ a+(8*r+3) ≤ i) → (i < scratch ∨ scratch+6 ≤ i) →
        u.scalarHeap i=s.scalarHeap i) ∧
      (run program (r,omega)).valid ∧
      (run program (r,omega)).work≤60*(r+1)^2 ∧
      (run program (r,omega)).peak≤B := by
  obtain ⟨u,runSource,outputs,low,out,roots,nat,outside⟩ :=
    UniformNewtonTableMachine.preparation_execution n x r a scratch source B omega bank s
      hr primitive layout pc h16 h17 h18 h19 retained axis fit scratchFit wb
  refine ⟨u,runSource,prepared_values outputs,low,out,roots,nat,outside,
    program_valid hr primitive,program_work r omega,?_⟩
  exact (program_peak r omega).trans (by omega)

end
end ExactFourierCircuits.DFTModelCacheForest
