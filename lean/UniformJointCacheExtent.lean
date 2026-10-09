import UniformJointAllocation
import UniformLocalReplayAssembly
import UniformLocalCacheTreeCoverage
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointCacheExtent
open UniformJointAllocation UniformWorkspacePlanner

/-- Actual six-phase259 slot count, including both empty disabled sweeps. -/
def slotCount (K:ℕ):ℕ:=11*UniformLocalReplayAssembly.phasePrefix (8*K+6) 6
lemma slotCount_formula (K:ℕ):slotCount K=352*K+330:=by
 rw[slotCount,UniformLocalReplayAssembly.prefix_total]
 ring
lemma slotCount_mono {K L:ℕ} (h:K≤ L):slotCount K≤ slotCount L:=by
 rw[slotCount_formula,slotCount_formula]
 omega

/-- Ragged rectangles plus generous four orientations per direct leaf. -/
def capacity (r:ℕ):ℕ:=r^2*(slotCount (Nat.clog 2 (4*r))+4)
def natSize (r:ℕ):ℕ:=13*(2*r+2)+7*(2*r+2)*r^2+9*r^2+(3*r+11)*capacity r
def scalarSize (r:ℕ):ℕ:=9*r*capacity r
/-- Include the real top-factor scalar9r and directory2 in the joint total. -/
def jointSize (r:ℕ):ℕ:=natSize r+scalarSize r+9*r+2

lemma exponent_le {r a e:ℕ} (ha:a≤ r) (he:e≤ r):exponent a e≤ Nat.clog 2 (4*r):=by
 unfold exponent
 exact Nat.clog_mono_right 2 (by omega)

lemma sum_bound (ls:List ℕ) (C:ℕ) (h:∀v∈ls,v≤ C):ls.sum≤ ls.length*C:=by
 induction ls with
 | nil=>simp
 | cons a ls ih=>
  have head:=h a (by simp)
  have tail:=ih (fun v hv=>h v (by simp[hv]))
  simp only[List.sum_cons,List.length_cons]
  nlinarith only[head,tail]

lemma actual_request_slots (r:ℕ) (P:UniformBalancedToeplitz.Plan r):
 ((UniformLocalPreparationDAG.requests P (le_refl r)).map (fun q=>slotCount q.k)).sum+2*r^2≤ capacity r:=by
 have length:=UniformLocalPreparationDAG.requests_length P (le_refl r)
 have sizes:((UniformLocalPreparationDAG.requests P (le_refl r)).map (fun q=>slotCount q.k)).sum≤ 
  (UniformLocalPreparationDAG.requests P (le_refl r)).length*slotCount (Nat.clog 2 (4*r)):=by
  have h:=sum_bound
   ((UniformLocalPreparationDAG.requests P (le_refl r)).map (fun q=>slotCount q.k))
   (slotCount (Nat.clog 2 (4*r))) (by
    intro k hk
    obtain ⟨q,_,eq⟩:=List.mem_map.mp hk
    rw[←eq]
    apply slotCount_mono
    exact exponent_le q.a_le q.e_le)
  simpa only[List.length_map] using h
 have total:=Nat.mul_le_mul_right (slotCount (Nat.clog 2 (4*r))) length
 unfold capacity
 rw[Nat.mul_add]
 omega

/-- Weighted slot demand of the actual produced forest, using its proven
kernel permutation to the genuine typed requests. No row-count premise. -/
lemma actual_walk_slots (r o R:ℕ):
 ((UniformLocalCacheTreeCoverage.visitedRows
  (UniformLocalCacheTreeMachine.walk (2*r+1) 0 R [⟨r,o,0,0⟩]).1).map
  (fun q=>slotCount (exponent q.a q.e))).sum+2*r^2≤ capacity r:=by
 have perm:=(UniformLocalCacheTreeCoverage.root_walk_kernel_coverage r o R).map
  (fun k:ℕ×ℕ×ℕ×ℕ×ℕ=>slotCount (exponent k.1 k.2.1))
 simp only[List.map_map,Function.comp_def,UniformLocalCacheTreeMachine.Row.kernel,
  UniformLocalCacheTreeMachine.requestKernel] at perm
 have eq:=perm.sum_eq
 change ((UniformLocalCacheTreeCoverage.visitedRows
  (UniformLocalCacheTreeMachine.walk (2*r+1) 0 R [⟨r,o,0,0⟩]).1).map
  (fun q=>slotCount (exponent q.a q.e))).sum=
  ((UniformLocalPreparationDAG.requests (UniformBalancedToeplitz.plan r) (le_refl r)).map
  (fun q=>slotCount q.k)).sum at eq
 rw[eq]
 exact actual_request_slots r (UniformBalancedToeplitz.plan r)

lemma slot_bound {n r:ℕ} (hr:r≤ 4*n):slotCount (Nat.clog 2 (4*r))+4≤ 6000*(n+2):=by
 have h:Nat.clog 2 (4*r)≤ 4*r:=Nat.clog_le_of_le_pow
  (UniformRecursiveBatchHeaderMachine.index_le_power (4*r))
 rw[slotCount_formula]
 omega

lemma joint_bound {n r:ℕ} (hr:r≤ 4*n):jointSize r≤ 6000000*(n+2)^4:=by
 let z:=n+2
 have hz:2≤ z:=by dsimp[z];omega
 have rb: r≤ 4*z:=by dsimp[z];omega
 have r2:r^2≤ 16*z^2:=by convert Nat.pow_le_pow_left rb 2 using 1;ring
 have slots:=slot_bound hr
 change slotCount (Nat.clog 2 (4*r))+4≤ 6000*z at slots
 have cap:capacity r≤ 96000*z^3:=by
  have h:=Nat.mul_le_mul r2 slots
  unfold capacity
  convert h using 1;ring
 have factor:scalarSize r≤ 3456000*z^4:=by
  have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 9 rb) cap
  unfold scalarSize
  convert h using 1;ring
 have stride:3*r+11≤ 18*z:=by omega
 have slab:(3*r+11)*capacity r≤ 1728000*z^4:=by
  have h:=Nat.mul_le_mul stride cap
  convert h using 1;ring
 have nodes:2*r+2≤ 9*z:=by omega
 have rect:7*(2*r+2)*r^2≤ 1008*z^3:=by
  have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 7 nodes) r2
  convert h using 1;ring
 have z1:z≤ z^4:=by simpa only[pow_one] using Nat.pow_le_pow_right (by omega:1≤ z) (by decide:1≤ 4)
 have z2:z^2≤ z^4:=Nat.pow_le_pow_right (by omega:1≤ z) (by decide:2≤ 4)
 have z3:z^3≤ z^4:=Nat.pow_le_pow_right (by omega:1≤ z) (by decide:3≤ 4)
 have one:1≤ z^4:=Nat.one_le_pow _ _ (by omega)
 unfold jointSize natSize
 change _≤ 6000000*z^4
 nlinarith only[factor,slab,rect,nodes,r2,rb,z1,z2,z3,one]

lemma selected_joint_bound (n:ℕ) (hn:0<n) (j:Fin (UniformAllAxisSeedPreparation.axisCount n)):
 jointSize (UniformAllAxisSeedPreparation.radix n j)≤ 6000000*(n+2)^4:=
 joint_bound ((UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1)

lemma search_bound {n r:ℕ} (c:Constants) (hr:r≤ 4*n):UniformWorkspaceSearchMachine.budget r≤ slab c n:=by
 have f:=fixed_large c
 have h:UniformWorkspaceSearchMachine.budget r≤ 20000*(n+2)^2:=by
  unfold UniformWorkspaceSearchMachine.budget
  nlinarith
 have k:20000≤ 100000*(fixed c+1):=by omega
 exact h.trans ((Nat.mul_le_mul_right ((n+2)^2) k).trans
  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega:1≤ n+2) (by decide:2≤ 19))))

end ExactFourierCircuits.UniformJointCacheExtent
