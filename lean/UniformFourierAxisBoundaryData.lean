import UniformFourierAxisBoundaryBindings
import UniformFourierAxisPrepareHead
import UniformFourierAxisPrepareControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareBoundary
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
namespace H
export UniformFourierAxisPrepareHead (freshNat freshScalar Protected Frame)
end H
namespace C
export UniformFourierAxisPrepareControl (Frame decisionState footerWrites)
end C
namespace W
export UniformFourierAxisWorkspace (axis axisBank)
end W
noncomputable section

/-- A diagonal epoch and the corresponding original five-lane seed family. -/
def BoundaryAt(d g:ℕ):Prop:=g=0∨g=d+1∨g=d+2∨g=d+3∨g=2*d+4
def FamilyAt(d g:ℕ)(q:Fin 3):Prop:=
 ((g=0∨g=2*d+4)∧q.val=0)∨((g=d+1∨g=d+3)∧q.val=1)∨(g=d+2∧q.val=2)
lemma boundary_values{d g:ℕ}{s:State}(h:UniformEpochSelectorMachine.Selected d g s)
 (boundary:BoundaryAt d g):∃q:Fin 3,s.natReg 7080=1∧s.natReg 7001=q.val∧FamilyAt d g q:=by
 rcases h with h|h|h|h|h|h
 · exact ⟨0,h.2.1,h.2.2,Or.inl ⟨h.1,rfl⟩⟩
 · rcases boundary with b|b|b|b|b <;>rcases h with ⟨a,b',c,e⟩ <;>omega
 · exact ⟨1,h.2.1,h.2.2,Or.inr (Or.inl ⟨h.1,rfl⟩)⟩
 · exact ⟨2,h.2.1,h.2.2,Or.inr (Or.inr ⟨h.1,rfl⟩)⟩
 · rcases boundary with b|b|b|b|b <;>rcases h with ⟨a,b',c,e⟩ <;>omega
 · rcases boundary with b|b|b|b|b <;>rcases h with ⟨a,b',c,e⟩ <;>omega

lemma boundary_away(q:ℕ)(h:H.Protected q):q∉UniformBoundaryDiagonalCaller.written:=by
 simp only[UniformBoundaryDiagonalCaller.written,UniformBoundaryDiagonalMachine.written,
  List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 unfold H.Protected at h
 omega
lemma decision_away(q:ℕ)(h:H.Protected q):q∉[7081]:=by
 simp only[List.mem_cons,List.not_mem_nil,or_false]
 unfold H.Protected at h
 omega
lemma footer_away(q:ℕ)(h:H.Protected q):q∉C.footerWrites:=by
 simp only[C.footerWrites,UniformFourierAxisPrepareControl.footerWrites,List.mem_cons,List.not_mem_nil,or_false]
 unfold H.Protected at h
 omega

lemma input_transport(c:Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s u:State)
 (h:UniformAxisCacheInputs.Inputs n x s)
 (nat:∀z,z<slab c n→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<slab c n→u.scalarHeap z=s.scalarHeap z)
 (regs:∀q,100≤q→q≤106→u.natReg q=s.natReg q)
 (outputs:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):UniformAxisCacheInputs.Inputs n x u:=by
 obtain ⟨last,conjugate,directory,conjugateDirectory⟩:=retained_below c n hn
 change UniformAllAxisSeedPreparation.axisBase n (ell n)≤ slab c n at last
 change UniformAllAxisConjugatePreparation.axisBase n (ell n)≤ slab c n at conjugate
 change UniformAllAxisSeedPreparation.directoryBase n+2*ell n≤ slab c n at directory
 change UniformAllAxisConjugatePreparation.directoryBase n+2*ell n≤ slab c n at conjugateDirectory
 have global:UniformGlobalLocalPreparation.globalEnd n≤ slab c n:=by
  unfold UniformAllAxisSeedPreparation.axisBase UniformLocalSeedTableMachine.poolBase at last
  omega
 have protect:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=
  ⟨fun z _ hi=>nat z (by omega),fun z hi=>scalar z (by omega),regs,outputs,roots⟩
 refine ⟨protect.metadata h.metadata,protect.operands h.operands,?_,?_⟩
 · constructor
   · intro j hj q l
     exact (scalar _ ((UniformAllAxisSeedPreparation.compact_address_before j hj q l).trans_le last)).trans
      (h.original.coefficients j hj q l)
   · intro j hj;exact (nat _ (by omega)).trans (h.original.address j hj)
   · intro j hj;exact (nat _ (by omega)).trans (h.original.width j hj)
 · constructor
   · intro j hj q l
     exact (scalar _ ((UniformAllAxisConjugatePreparation.compact_address_before j hj q l).trans_le conjugate)).trans
      (h.conjugate.coefficients j hj q l)
   · intro j hj;exact (nat _ (by omega)).trans (h.conjugate.address j hj)
   · intro j hj;exact (nat _ (by omega)).trans (h.conjugate.width j hj)

structure Frame(c:Constants)(n:ℕ)(j:Fin (ell n))(s u:State):Prop where
 natPrefix:∀z,z<(W.axis c n j).selected→u.natHeap z=s.natHeap z
 scalarOutside:∀z,(z<slab c n∨slab c n+9*UniformAllAxisSeedPreparation.radix n j≤z)→u.scalarHeap z=s.scalarHeap z
 scalarReg:∀q,q≠32→q≠125→u.scalarReg q=s.scalarReg q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,H.Protected q→u.natReg q=s.natReg q

/-- Data actually printed by the boundary138, independent of its local PC. -/
structure Payload(c:Constants)(n g:ℕ)(hn:0<n)(j:Fin (ell n))(q:Fin 3)(s:State):Prop where
 selected:UniformGlobalCalendarDispatch.Selected (W.axis c n j).selected 0
  (UniformBoundaryDiagonalCaller.descriptor (UniformAllAxisSeedPreparation.radix n j) (slab c n) (W.axis c n j).boundary) s
 stored:UniformGlobalCalendarDispatch.Stored
  (UniformBoundaryDiagonalCaller.descriptor (UniformAllAxisSeedPreparation.radix n j) (slab c n) (W.axis c n j).boundary) s
 entry:UniformLocalMatchingSlotDirectory.Entry ((W.axis c n j).boundary+3*UniformAllAxisSeedPreparation.radix n j+4)
  g (UniformAllAxisSeedPreparation.radix n j) (slab c n) (UniformAllAxisSeedPreparation.radix n j)
  ((W.axis c n j).boundary+UniformAllAxisSeedPreparation.radix n j) (W.axis c n j).boundary 1 s
 pools:UniformGlobalDiagonalRowsMachine.Pools
  [UniformBoundaryDiagonalMachine.poolEntry (UniformAllAxisSeedPreparation.radix n j) (slab c n)
   (UniformFourierAxisGeometry.geometry c hn j).radix
   (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) q] s
 row:UniformSectorPackingMachine.Rows
  [UniformBoundaryDiagonalMachine.axis (UniformAllAxisSeedPreparation.radix n j) (W.axis c n j).boundary
   (UniformFourierAxisGeometry.geometry c hn j).radix] 0
  ((W.axis c n j).boundary+3*UniformAllAxisSeedPreparation.radix n j) s
 widths:UniformSectorPackingMachine.Widths
  [UniformBoundaryDiagonalMachine.axis (UniformAllAxisSeedPreparation.radix n j) (W.axis c n j).boundary
   (UniformFourierAxisGeometry.geometry c hn j).radix] s
 permutation:UniformSectorPackingMachine.Permutations
  [UniformBoundaryDiagonalMachine.axis (UniformAllAxisSeedPreparation.radix n j) (W.axis c n j).boundary
   (UniformFourierAxisGeometry.geometry c hn j).radix] s

end
end ExactFourierCircuits.UniformFourierAxisPrepareBoundary
