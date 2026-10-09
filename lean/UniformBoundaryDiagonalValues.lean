import UniformBoundaryDiagonalMachine
import UniformGlobalDiagonalRowsMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalMachine
open UniformMachine UniformPairMachine
noncomputable section

def family (omega:ℂ)(q:Fin 3)(j:ℕ):ℂ:=UniformLocalSeedTableMachine.seedValue omega ⟨q.val,by omega⟩ j
lemma family_H (omega:ℂ)(j:ℕ):family omega 0 j=OAI.ExactFourier.NewtonFourier.H omega j:=by
 simp[family,UniformLocalSeedTableMachine.seedValue]
lemma family_scale (omega:ℂ)(j:ℕ):family omega 1 j=OAI.ExactFourier.NewtonFourier.scale omega j:=by
 simp[family,UniformLocalSeedTableMachine.seedValue]
lemma family_inverseDiagonal (omega:ℂ)(j:ℕ):family omega 2 j=(UniformNewton.diagonalValue omega j)⁻¹:=by
 simp[family,UniformLocalSeedTableMachine.seedValue]

lemma axis_widths (r arena:ℕ)(positive:2≤r):
 (axis r arena positive).geometry.widths=List.replicate r 1:=by
 simp[axis,UniformMatchingAxisTableMachine.physicalAxis,UniformMatchingAxisTableMachine.geometry,
  UniformMatchingAxisTableMachine.widths]
lemma axis_no_pairs (r arena:ℕ)(positive:2≤r):2∉(axis r arena positive).geometry.widths:=by
 rw[axis_widths];simp
lemma ordered_empty (r:ℕ):UniformMatchingAxisTableMachine.ordered r emptyEdges=List.range r:=by
 simp[UniformMatchingAxisTableMachine.ordered,UniformMatchingAxisTableMachine.paired,
  UniformMatchingAxisTableMachine.singletons]
def poolEntry (r pool:ℕ)(positive:2≤r)(omega:ℂ)(q:Fin 3):UniformGlobalDiagonalRowsMachine.Entry where
 radix:=r
 positive:=by omega
 pool:=pool
 value:=fun lane j=>if lane.val=0 then family omega q j.val else 1

lemma pools_of_written {r pool:ℕ}(positive:2≤r)(omega:ℂ)(q:Fin 3)(s:State)
 (copied:∀j:Fin r,s.scalarHeap (pool+j.val)=some (prepared (family omega q j.val)))
 (ones:∀lane:Fin 9,lane.val≠0→∀j:Fin r,s.scalarHeap (pool+lane.val*r+j.val)=some (prepared 1)):
 UniformGlobalDiagonalRowsMachine.Pools [poolEntry r pool positive omega q] s:=by
 intro a member lane j
 have eq:a=poolEntry r pool positive omega q:=by simpa only[List.mem_singleton] using member
 subst a
 change s.scalarHeap (pool+lane.val*r+j.val)=some (prepared (if lane.val=0 then family omega q j.val else 1))
 by_cases zero:lane.val=0
 · simpa only[zero,ite_true,Nat.zero_mul,Nat.add_zero] using copied j
 · simpa only[zero,ite_false] using ones lane zero j
end
end ExactFourierCircuits.UniformBoundaryDiagonalMachine
