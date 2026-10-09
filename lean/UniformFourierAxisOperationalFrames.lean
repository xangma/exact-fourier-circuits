import UniformFourierAxisOperationalCases
import UniformCacheRangeSelectorOutput

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisOperationalCases
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
noncomputable section
namespace W
export UniformFourierAxisWorkspace (axis)
end W

structure Frame(c:Constants)(n:ℕ)(j:Fin (ell n))(s u:State):Prop where
 natPrefix:∀z,z<(W.axis c n j).selected→u.natHeap z=s.natHeap z
 scalarOutside:∀z,(z<slab c n∨slab c n+9*UniformAllAxisSeedPreparation.radix n j≤z)→u.scalarHeap z=s.scalarHeap z
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,UniformFourierAxisPrepareHead.Protected q→u.natReg q=s.natReg q

lemma Branch.pc {c:Constants}{n d g rectangleCount:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u):u.pc=388:=by
 cases actual with
 | tree _ a=>exact a.pc
 | boundary _ _ a=>exact a.pc
 | inactive _ a=>exact a.pc

lemma Branch.inputs {c:Constants}{n d g rectangleCount:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u):UniformAxisCacheInputs.Inputs n x u:=by
 cases actual with
 | tree _ a=>exact a.inputs
 | boundary _ _ a=>exact a.inputs
 | inactive _ a=>exact a.inputs

lemma Branch.frame {c:Constants}{n d g rectangleCount:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u):Frame c n j s u:=by
 cases actual with
 | tree _ a=>
  refine ⟨?_,fun z _=>congrFun a.scalarHeap z,a.outputs,a.roots,a.registers⟩
  intro z low
  rw[a.bank]
  exact UniformCacheRangeSelector.writeSelections_low _ _ _ _ _ low
 | boundary _ _ a=>
  exact ⟨a.frame.natPrefix,a.frame.scalarOutside,a.frame.outputs,a.frame.roots,a.frame.natReg⟩
 | inactive _ a=>
  exact ⟨fun z _=>congrFun a.frame.natHeap z,fun z _=>congrFun a.frame.scalarHeap z,
   a.frame.outputs,a.frame.roots,a.frame.natReg⟩

lemma Branch.footer {c:Constants}{n d g rectangleCount:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u)
 (physical:s.natReg 6028=5*slab c n)(directory:s.natReg 5923=slab c n+2*j.val):∃count,
 UniformFourierAxisPrepareFooter.Result (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) count j.val (s.natReg 6028) (s.natReg 5923)
  (UniformJointCacheAllocation.axis c n j).endNat (UniformJointCacheAllocation.axis c n j).endScalar u:=by
 cases actual with
 | tree _ a=>exact ⟨_,a.footer⟩
 | boundary _ _ a=>
  refine ⟨1,?_⟩
  rw[physical,directory]
  exact a.footer
 | inactive _ a=>exact ⟨0,a.footer⟩

lemma selected_length(r control rectangleCount tick:ℕ)(rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range):
 (UniformCacheRangeSelector.selections r control rectangleCount tick rectangle nodes).length≤rectangleCount+R.total nodes:=by
 unfold UniformCacheRangeSelector.selections
 rw[List.length_append]
 exact Nat.add_le_add (UniformGlobalCalendarSelector.selected_length _ _ _ _ _ _)
  (UniformCacheRangeSelector.selectedRanges_length _ _ _)

lemma tree_natOutside{c:Constants}{n d g rectangleCount:ℕ}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (actual:UniformFourierAxisPrepareTree.Result c n d g rectangleCount j rectangle nodes x s u)
 (capacity:rectangleCount+R.total nodes≤UniformJointCacheExtent.capacity (UniformAllAxisSeedPreparation.radix n j)):
 ∀z,(z<(W.axis c n j).selected∨(W.axis c n j).phase≤z)→u.natHeap z=s.natHeap z:=by
 have length:=(selected_length (UniformAllAxisSeedPreparation.radix n j)
  (UniformJointCacheAllocation.axis c n j).control rectangleCount
  (UniformFourierAxisPrepareTree.localTick d g) rectangle nodes).trans capacity
 have geometry:=UniformFourierAxisWorkspace.axis_geometry c n j
 intro z outside
 rw[actual.bank]
 rcases outside with low|high
 · exact UniformCacheRangeSelector.writeSelections_low _ _ _ _ _ low
 · apply UniformCacheRangeSelector.writeSelections_high
   have twice:=Nat.mul_le_mul_left 2 length
   omega

end
end ExactFourierCircuits.UniformFourierAxisOperationalCases
