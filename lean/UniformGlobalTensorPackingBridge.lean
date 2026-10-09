import UniformGlobalPackingChildPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTensorPackingBridge
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

def argumentRegisters : List ℕ := [5820,5821,5822,5823,5824,5825,5826,5827,
 3201,3202,3213,3214,3215,4441,4442,4530,4531,5800,5801]
def writesArguments : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>argumentRegisters.contains d
 | _=>false
lemma relocated (b ret:ℕ) (i:Instruction):writesArguments (relocate b ret i)=writesArguments i:=by
 cases i <;>rfl
lemma diagonal_free (W:ℕ):
 (UniformGlobalTensorDiagonalPreparation.programFor W).all (fun i=>!writesArguments i)=true := by
 simp only[UniformGlobalTensorDiagonalPreparation.programFor,UniformGlobalDiagonalRowsMachine.program,
  UniformGlobalDiagonalPhasePreparation.program,UniformGlobalTensorDiagonalMachine.programFor,
  List.all_append,List.all_map,Function.comp_def,relocated,List.all_cons,List.all_nil]
 rfl
lemma diagonal_keeps (W q:ℕ) (hq:q∈argumentRegisters):
 ∀i∈UniformGlobalTensorDiagonalPreparation.programFor W,UniformNewtonTableMachine.KeepsNat q i := by
 intro i hi
 have free:=List.all_eq_true.mp (diagonal_free W) i hi
 cases i <;>simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals intro equal;subst_vars
 all_goals simp[writesArguments,hq] at free
lemma execution_keeps {W B n ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x B s ticks u) :
 ∀q∈argumentRegisters,u.natReg q=s.natReg q := by
 intro q hq
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (diagonal_keeps W q hq)
lemma packing_header {W B n ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (gp:UniformGlobalRolePackingMachine.Geometry W)
 (run:BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x B s ticks u)
 (h:UniformGlobalRolePackingMachine.Header gp s) : UniformGlobalRolePackingMachine.Header gp u := by
 have kept:=execution_keeps run
 constructor
 · exact (kept 5820 (by simp[argumentRegisters])).trans h.volume
 · exact (kept 5821 (by simp[argumentRegisters])).trans h.source
 · exact (kept 5822 (by simp[argumentRegisters])).trans h.destination
 · exact (kept 5823 (by simp[argumentRegisters])).trans h.axes
 · exact (kept 5824 (by simp[argumentRegisters])).trans h.rows
 · exact (kept 5825 (by simp[argumentRegisters])).trans h.suffix
 · exact (kept 5826 (by simp[argumentRegisters])).trans h.stack
 · exact (kept 5827 (by simp[argumentRegisters])).trans h.inverse

lemma rows_above (as:List UniformSectorPackingMachine.PhysicalAxis) (depth base lower:ℕ)
 (s u:State) (h:UniformSectorPackingMachine.Rows as depth base s) (below:lower≤base)
 (heap:∀q,lower≤q→u.natHeap q=s.natHeap q) :
 UniformSectorPackingMachine.Rows as depth base u := by
 induction as generalizing depth with
 | nil=>trivial
 | cons a as ih=>
  rcases h with ⟨h0,h1,h2,h3,rest⟩
  refine ⟨?_,?_,?_,?_,ih (depth+1) rest⟩
  · exact (heap _ (by omega)).trans h0
  · exact (heap _ (by omega)).trans h1
  · exact (heap _ (by omega)).trans h2
  · exact (heap _ (by omega)).trans h3

/-- Real131 Nat writes occupy three specified banks. The original physical
partition rows sit above all three; widths and true permutations sit below
all three. Hence153 consumes exactly the same producer metadata. -/
lemma packing_banks {W:ℕ} (gp:UniformGlobalRolePackingMachine.Geometry W)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (L:UniformGlobalDiagonalRowsMachine.Layout)
 (as:List UniformSectorPackingMachine.PhysicalAxis) (s u:State)
 (banks:UniformGlobalRolePackingMachine.Banks gp as s)
 (rowAbove:L.rows+3*L.ell≤gp.rows) (permutationAbove:L.permutation+L.total≤gp.rows)
 (stackAbove:g.natStack+3*g.ell≤gp.rows)
 (widthsBelow:∀a∈as,a.widthsBase+a.geometry.widths.length≤L.rows ∧
  a.widthsBase+a.geometry.widths.length≤L.permutation ∧a.widthsBase+a.geometry.widths.length≤g.natStack)
 (permutationsBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum≤L.rows ∧
  a.permutationBase+a.geometry.widths.sum≤L.permutation ∧a.permutationBase+a.geometry.widths.sum≤g.natStack)
 (outside:∀q,(q<L.rows ∨L.rows+3*L.ell≤q)→(q<L.permutation ∨L.permutation+L.total≤q)→
  (q<g.natStack ∨g.natStack+3*g.ell≤q)→u.natHeap q=s.natHeap q) :
 UniformGlobalRolePackingMachine.Banks gp as u := by
 refine ⟨rows_above as 0 gp.rows gp.rows s u banks.1 (by omega) ?_,?_,?_⟩
 · intro q hq
   exact outside q (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
 · intro a member j
   have b:=widthsBelow a member
   exact (outside _ (Or.inl (by have:=j.isLt;omega)) (Or.inl (by have:=j.isLt;omega))
    (Or.inl (by have:=j.isLt;omega))).trans (banks.2.1 a member j)
 · intro a member j
   have b:=permutationsBelow a member
   exact (outside _ (Or.inl (by have:=j.isLt;omega)) (Or.inl (by have:=j.isLt;omega))
    (Or.inl (by have:=j.isLt;omega))).trans (banks.2.2 a member j)

lemma output_volume {W:ℕ} (gp:UniformGlobalRolePackingMachine.Geometry W)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (as:List UniformGlobalDiagonalRowsMachine.Entry)
 (lane:Fin 9) (P C:ℕ) (same:gp.volume=g.volume)
 (volume:g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod) :
 gp.volume=(radices (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as)).prod := by
 rw[UniformGlobalDiagonalRowsMachine.axes_radices];exact same.trans volume

def outputValues {W:ℕ} (gp:UniformGlobalRolePackingMachine.Geometry W)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (as:List UniformGlobalDiagonalRowsMachine.Entry)
 (lane:Fin 9) (P C:ℕ) (same:gp.volume=g.volume)
 (volume:g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
 (v:ℕ→ℕ→Scalar) (i:ℕ) (j:Fin gp.volume) : Scalar :=
 UniformPairMachine.product (tensorCoefficient (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as)
  (finCongr (output_volume gp g as lane P C same volume) j)) (v i j.val)

/-- The actual131 output supplies the native source of153, preserving every
input dependency tag and the exact physically selected tensor coefficients. -/
lemma packing_source {W:ℕ} (gp:UniformGlobalRolePackingMachine.Geometry W)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (as:List UniformGlobalDiagonalRowsMachine.Entry)
 (lane:Fin 9) (P C:ℕ) (same:gp.volume=g.volume)
 (volume:g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
 (native:gp.source=g.destination) (v:ℕ→ℕ→Scalar) (u:State)
 (done:UniformGlobalTensorDiagonalMachine.Filled g
  (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) v W u) :
 UniformGlobalRolePackingMachine.Source gp (outputValues gp g as lane P C same volume v) u := by
 intro i hi j
 have produced:=UniformGlobalTensorDiagonalPreparation.diagonal_values done i hi
  (finCongr (output_volume gp g as lane P C same volume) j)
 simpa only[outputValues,native,same,finCongr_apply,Fin.val_cast] using produced

end
end ExactFourierCircuits.UniformGlobalTensorPackingBridge
