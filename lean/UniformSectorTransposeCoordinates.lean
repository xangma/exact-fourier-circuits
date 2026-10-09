import UniformAllSectorTransposeMachine
import UniformSectorNetworkAction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorTransposeCoordinates
open UniformMachine UniformSectorPacking
noncomputable section
/-- Actual sector enumeration covers every packed coordinate; this is derived
from the explicit packing codec rather than supplied as a movement certificate. -/
lemma canonical_cover (axes:List Axis) (j:Fin (radices axes).prod):
 ∃i,∃hi:i < (sectorStates axes).length,∃t,t < ((sectorStates axes)[i]'hi).width ∧
 ((sectorStates axes)[i]'hi).start+t=j.val:=by
 obtain ⟨b,t,coordinate⟩:=sectors_cover axes j
 have mem:expectedBlockState axes b ∈ sectorStates axes:=by
  simp only[sectorStates,List.mem_ofFn]
  exact ⟨sectorIndexEquiv axes b,congrArg (expectedBlockState axes) ((sectorIndexEquiv axes).symm_apply_apply b)⟩
 obtain ⟨i,hi,equal⟩:=List.mem_iff_getElem.1 mem
 refine ⟨i,hi,t.val,?_,?_⟩
 · rw[equal];exact t.isLt
 · rw[equal]
   exact (sectorCoordinate_value axes b t).symm.trans (congrArg Fin.val coordinate)
/-- Whole reverse41 writes every native coordinate, including the singleton
spectator coordinates. Each output came from the genuine sector child bank. -/
theorem reverse_complete {W:ℕ} (axes:List Axis)
 (g:UniformAllSectorTransposeMachine.Geometry W true (sectorStates axes)) (v:ℕ→ℕ→Scalar) (u:State)
 (filled:UniformAllSectorTransposeMachine.Filled g v (sectorStates axes).length u):
 ∀r,r < W→∀j:Fin (radices axes).prod,u.scalarHeap (g.native+r*g.volume+j.val)=some (v r j.val):=by
 intro r hr j
 obtain ⟨i,hi,t,ht,address⟩:=canonical_cover axes j
 have h:=filled i hi hi r hr t ht
 change u.scalarHeap (g.native+r*g.volume+((sectorStates axes)[i]'hi).start+t)=
  some (v r (((sectorStates axes)[i]'hi).start+t)) at h
 simpa only[Nat.add_assoc,address] using h
/-- The physical39 child width is exactly2^q for every canonical record. -/
lemma canonical_width (axes:List Axis) (i:ℕ) (hi:i < (sectorStates axes).length):
 ((sectorStates axes)[i]'hi).width=2^((sectorStates axes)[i]'hi).pairs:=
 UniformSectorBatchDirectoryMachine.sector_width axes i hi
end
end ExactFourierCircuits.UniformSectorTransposeCoordinates
