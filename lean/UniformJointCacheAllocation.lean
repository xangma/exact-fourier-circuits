import UniformJointCacheExtent
import UniformMatchingAxisTableMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointCacheAllocation
open UniformJointAllocation UniformJointCacheExtent

/-- Integer-only cumulative allocation. No produced bank/output is an input. -/
def offsetSum (f:ℕ→ℕ) (k:ℕ):ℕ:=∑i∈Finset.range k,f i
lemma offsetSum_step (f:ℕ→ℕ) (k:ℕ):offsetSum f (k+1)=offsetSum f k+f k:=Finset.sum_range_succ _ _
lemma offsetSum_mono (f:ℕ→ℕ) {i j:ℕ} (h:i≤   j):offsetSum f i≤   offsetSum f j:=
 Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _=>Nat.zero_le _)

abbrev ell (n:ℕ):ℕ:=UniformAllAxisSeedPreparation.axisCount n
def natTotal (n:ℕ):ℕ:=offsetSum (fun i=>natSize (UniformAllAxisSeedPreparation.radixAt n i)) (ell n)
def scalarTotal (n:ℕ):ℕ:=offsetSum (fun i=>scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) (ell n)
def total (n:ℕ):ℕ:=natTotal n+scalarTotal n+9*UniformAllAxisSeedPreparation.prefixSum n (ell n)+2*ell n
lemma total_formula (n:ℕ):total n=offsetSum (fun i=>jointSize (UniformAllAxisSeedPreparation.radixAt n i)) (ell n):=by
 unfold total natTotal scalarTotal offsetSum jointSize UniformAllAxisSeedPreparation.prefixSum
 simp only[Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,Finset.card_range,smul_eq_mul]
 ring

lemma total_bound (c:Constants) (n:ℕ) (hn:0<n):total n≤   slab c n:=by
 have first:total n≤  ell n*(6000000*(n+2)^4):=by
  rw[total_formula]
  calc
   offsetSum (fun i=>jointSize (UniformAllAxisSeedPreparation.radixAt n i)) (ell n)≤  ∑_i∈Finset.range (ell n),6000000*(n+2)^4:=by
    apply Finset.sum_le_sum
    intro i hi
    have lt:i<ell n:=Finset.mem_range.mp hi
    have r:UniformAllAxisSeedPreparation.radixAt n i=UniformAllAxisSeedPreparation.radix n ⟨i,lt⟩:=UniformAllAxisSeedPreparation.radixAt_eq n ⟨i,lt⟩
    rw[r]
    exact selected_joint_bound n hn ⟨i,lt⟩
   _=ell n*(6000000*(n+2)^4):=by simp
 have axes:ell n≤  2*(n+2):=by have h:=(actual_sizes n hn).1;change ell n≤  2*n+1 at h;omega
 have second:ell n*(6000000*(n+2)^4)≤  12000000*(n+2)^5:=by
  have h:=Nat.mul_le_mul_right (6000000*(n+2)^4) axes
  convert h using 1;ring
 have big:12000000≤  100000*(fixed c+1):=by have:=fixed_large c;omega
 exact first.trans (second.trans ((Nat.mul_le_mul_right ((n+2)^5) big).trans
  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega:1≤  n+2) (by decide:5≤  19)))))

def natStart (c:Constants) (n:ℕ):ℕ:=slab c n+2*ell n
def scalarStart (c:Constants) (n:ℕ):ℕ:=slab c n+9*UniformAllAxisSeedPreparation.prefixSum n (ell n)
def natEnd (c:Constants) (n:ℕ):ℕ:=natStart c n+natTotal n
def scalarEnd (c:Constants) (n:ℕ):ℕ:=scalarStart c n+scalarTotal n
lemma ends_bound (c:Constants) (n:ℕ) (hn:0<n):natEnd c n≤  2*slab c n ∧scalarEnd c n≤  2*slab c n:=by
 have h:=total_bound c n hn
 unfold total natEnd scalarEnd natStart scalarStart at *
 omega

structure AxisAddresses where
 radix:ℕ
 tasks:ℕ
 nodes:ℕ
 requests:ℕ
 control:ℕ
 leafForward:ℕ
 leafTranspose:ℕ
 durations:ℕ
 nodeStarts:ℕ
 requestStarts:ℕ
 endNat:ℕ
 pool:ℕ
 endScalar:ℕ
 deriving Repr,DecidableEq

/-- Genuine nonoverlapping persistent regions, and actual173 conservative
worklist/directory/request extents. Timings retain two words per node. -/
def axisBank (r N S:ℕ):AxisAddresses:=
 let nodes:=N+4*(2*r+2)
 let requests:=nodes+7*(2*r+2)
 let control:=requests+7*(2*r+2)*r^2
 let leaf:=control+(3*r+11)*capacity r
 let time:=leaf+8*r^2
 ⟨r,N,nodes,requests,control,leaf,leaf+4*r^2,time,time+(2*r+2),time+2*(2*r+2),
  time+2*(2*r+2)+r^2,S,S+9*r*capacity r⟩
lemma axis_ends (r N S:ℕ):(axisBank r N S).endNat=N+natSize r ∧
 (axisBank r N S).endScalar=S+scalarSize r:=by dsimp[axisBank,natSize,scalarSize];constructor <;>ring

noncomputable section
/-- The selected actual radix supplies every axis size. -/
def axis (c:Constants) (n:ℕ) (j:Fin (ell n)):AxisAddresses:=
 axisBank (UniformAllAxisSeedPreparation.radix n j)
  (natStart c n+offsetSum (fun i=>natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  (scalarStart c n+offsetSum (fun i=>scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
lemma axis_radix (c:Constants) (n:ℕ) (j:Fin (ell n)):(axis c n j).radix=UniformAllAxisSeedPreparation.radix n j:=rfl
lemma axis_fit (c:Constants) (n:ℕ) (j:Fin (ell n)):
 (axis c n j).endNat≤  natEnd c n ∧(axis c n j).endScalar≤  scalarEnd c n:=by
 have r:=UniformAllAxisSeedPreparation.radixAt_eq n j
 have en:=offsetSum_mono (fun i=>natSize (UniformAllAxisSeedPreparation.radixAt n i)) (Nat.succ_le_of_lt j.isLt)
 have es:=offsetSum_mono (fun i=>scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) (Nat.succ_le_of_lt j.isLt)
 rw[offsetSum_step,r] at en es
 unfold axis
 rw[(axis_ends _ _ _).1,(axis_ends _ _ _).2]
 unfold natEnd scalarEnd natTotal scalarTotal
 omega
lemma axis_separation (c:Constants) (n:ℕ) (i j:Fin (ell n)) (h:i.val<j.val):
 (axis c n i).endNat≤  (axis c n j).tasks ∧(axis c n i).endScalar≤  (axis c n j).pool:=by
 have r:=UniformAllAxisSeedPreparation.radixAt_eq n i
 have en:=offsetSum_mono (fun k=>natSize (UniformAllAxisSeedPreparation.radixAt n k)) (Nat.succ_le_of_lt h)
 have es:=offsetSum_mono (fun k=>scalarSize (UniformAllAxisSeedPreparation.radixAt n k)) (Nat.succ_le_of_lt h)
 rw[offsetSum_step,r] at en es
 unfold axis
 rw[(axis_ends _ _ _).1,(axis_ends _ _ _).2]
 change _≤   natStart c n+offsetSum (fun k=>natSize (UniformAllAxisSeedPreparation.radixAt n k)) j.val ∧
  _≤   scalarStart c n+offsetSum (fun k=>scalarSize (UniformAllAxisSeedPreparation.radixAt n k)) j.val
 omega

structure SlotAddresses where
 permutation:ℕ
 widths:ℕ
 markers:ℕ
 physicalAxis:ℕ
 abi:ℕ
 factor:ℕ
 deriving Repr,DecidableEq
/-- Actual80 ordering: P[r], widths[r], markers[r], physical axis4, ABI7. -/
def slot (a:AxisAddresses) (j:ℕ):SlotAddresses:=
 let P:=a.control+(3*a.radix+11)*j
 ⟨P,P+a.radix,P+2*a.radix,P+3*a.radix,P+3*a.radix+4,a.pool+9*a.radix*j⟩
lemma slot_abi_end (a:AxisAddresses) (j:ℕ):
 (slot a j).abi+7=a.control+(3*a.radix+11)*(j+1):=by dsimp[slot];ring
lemma slot_regions (a:AxisAddresses) (j:ℕ):
 (slot a j).permutation+a.radix=(slot a j).widths ∧
 (slot a j).widths+a.radix=(slot a j).markers ∧
 (slot a j).markers+a.radix=(slot a j).physicalAxis ∧
 (slot a j).physicalAxis+4=(slot a j).abi:=by
 dsimp[slot]
 exact ⟨by ring,by ring,by ring,by ring⟩
lemma slots_separate (a:AxisAddresses) {i j:ℕ} (h:i<j):
 (slot a i).abi+7≤  (slot a j).permutation ∧(slot a i).factor+9*a.radix≤  (slot a j).factor:=by
 rw[slot_abi_end]
 have first:=Nat.mul_le_mul_left (3*a.radix+11) (Nat.succ_le_of_lt h)
 have last:=Nat.mul_le_mul_left (9*a.radix) (Nat.succ_le_of_lt h)
 dsimp[slot]
 constructor <;>nlinarith
lemma slot_fit (r N S j:ℕ) (h:j<capacity r):
 (slot (axisBank r N S) j).abi+7≤  (axisBank r N S).leafForward ∧
 (slot (axisBank r N S) j).factor+9*r≤  (axisBank r N S).endScalar:=by
 rw[slot_abi_end]
 have first:=Nat.mul_le_mul_left (3*r+11) (Nat.succ_le_of_lt h)
 have last:=Nat.mul_le_mul_left (9*r) (Nat.succ_le_of_lt h)
 dsimp[axisBank,slot]
 constructor <;>nlinarith

/-- Exact ordinary geometry for the actual80 matching-axis/ABI adapter.
Its genuine translated producer source is required below the persistent slab;
that workspace installation remains a separate machine composition seam. -/
theorem matching_geometry (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n))
 (k M T:ℕ) (hk:k<capacity (axis c n j).radix)
 (E:Fin M→UniformColoring.Edge) (hm:UniformMatchingAxisTableMachine.Matching E)
 (hr:UniformMatchingAxisTableMachine.InRange (axis c n j).radix E) (source:T≤  slab c n):
 let a:=axis c n j
 let g:=slot a k
 T+3*M≤  g.permutation ∧g.permutation+a.radix≤  g.widths ∧
 g.widths+a.radix≤  g.markers ∧g.markers+a.radix≤  g.physicalAxis ∧
 g.physicalAxis+4≤  g.abi ∧g.abi+7≤  envelope c n ∧
 g.factor+9*a.radix≤  envelope c n ∧80≤  envelope c n:=by
 dsimp only
 have count:=UniformMatchingAxisTableMachine.matching_capacity (axis c n j).radix E hm hr
 have regions:=slot_regions (axis c n j) k
 have fit:(slot (axis c n j) k).abi+7≤  (axis c n j).leafForward ∧
  (slot (axis c n j) k).factor+9*(axis c n j).radix≤  (axis c n j).endScalar:=by
  unfold axis
  exact slot_fit _ _ _ k hk
 have endNat:=((axis_fit c n j).1.trans (ends_bound c n hn).1)
 have endScalar:=((axis_fit c n j).2.trans (ends_bound c n hn).2)
 have leaf:(axis c n j).leafForward≤  (axis c n j).endNat:=by dsimp[axis,axisBank];omega
 refine ⟨?_,regions.1.le,regions.2.1.le,regions.2.2.1.le,regions.2.2.2.le,?_,?_,?_⟩
 · dsimp[axis,axisBank,slot,natStart] at count ⊢
   omega
 · exact fit.1.trans (leaf.trans (endNat.trans (by unfold envelope;omega)))
 · exact fit.2.trans (endScalar.trans (by unfold envelope;omega))
 · have:=fixed_large c
   unfold envelope
   omega

/-- Concrete separation required by the real131→153 metadata bridge. -/
theorem tensor_packing_regions (c:Constants) (n:ℕ) (hn:0<n) (roles:0<c.roles):
 (rowLayout c n hn).rows+3*(rowLayout c n hn).ell≤ (packingGeometry c n hn).rows ∧
 (rowLayout c n hn).permutation+(rowLayout c n hn).total≤ (packingGeometry c n hn).rows ∧
 (tensorGeometry c n hn roles).natStack+3*(tensorGeometry c n hn roles).ell≤ (packingGeometry c n hn).rows:=by
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw[Nat.mul_assoc 2 c.roles] at h
 dsimp[rowLayout,tensorGeometry,packingGeometry,allocate]
 omega

/-- Persistent produced cache slot banks stay below each subsequent131 Nat
scratch region; their values must still come from the actual cache conductor. -/
theorem cache_banks_before_tensor (c:Constants) (n:ℕ) (hn:0<n) (roles:0<c.roles)
 (j:Fin (ell n)) (k:ℕ) (hk:k<capacity (axis c n j).radix):
 let a:=axis c n j
 let g:=slot a k
 g.permutation+a.radix≤ (rowLayout c n hn).rows ∧g.widths+a.radix≤ (rowLayout c n hn).rows ∧
 g.permutation+a.radix≤ (rowLayout c n hn).permutation ∧g.widths+a.radix≤ (rowLayout c n hn).permutation ∧
 g.permutation+a.radix≤ (tensorGeometry c n hn roles).natStack ∧
 g.widths+a.radix≤ (tensorGeometry c n hn roles).natStack:=by
 dsimp only
 have fit:(slot (axis c n j) k).abi+7≤ (axis c n j).leafForward:=by
  unfold axis
  exact (slot_fit _ _ _ k hk).1
 have leaf:(axis c n j).leafForward≤ (axis c n j).endNat:=by dsimp[axis,axisBank];omega
 have bound:=(fit.trans leaf).trans ((axis_fit c n j).1.trans (ends_bound c n hn).1)
 have widths:(slot (axis c n j) k).widths+(axis c n j).radix≤ (slot (axis c n j) k).abi+7:=by dsimp[slot];omega
 have permutation:(slot (axis c n j) k).permutation+(axis c n j).radix≤ (slot (axis c n j) k).abi+7:=by dsimp[slot];omega
 dsimp[rowLayout,tensorGeometry,allocate]
 omega

/-- Actual173 Layout is constructed from generated allocation; no forest,
request-directory or prepared-value premise is supplied. -/
theorem forestLayout (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n)):
 UniformLocalCacheTreeExecution.Layout (axis c n j).radix 0 (axis c n j).tasks
  (axis c n j).nodes (axis c n j).requests (envelope c n) where
 code:=by have:=fixed_large c;unfold envelope;omega
 search:=by
  have r:UniformAllAxisSeedPreparation.radix n j≤  4*n:=
   (UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1
  exact (search_bound c r).trans (show slab c n≤  envelope c n by unfold envelope;omega)
 stack:=by dsimp[axis,axisBank];omega
 directory:=by dsimp[axis,axisBank];omega
 requests:=by
  have e:=(axis_fit c n j).1.trans (ends_bound c n hn).1
  have a:=axis_ends (UniformAllAxisSeedPreparation.radix n j)
   (natStart c n+offsetSum (fun i=>natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
   (scalarStart c n+offsetSum (fun i=>scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  dsimp[axis,axisBank,envelope] at *
  omega
 native:=by
  have r:UniformAllAxisSeedPreparation.radix n j≤  4*n:=
   (UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1
  have h:=search_bound c r
  unfold UniformWorkspaceSearchMachine.budget at h
  change 0+UniformAllAxisSeedPreparation.radix n j≤  envelope c n
  unfold envelope
  nlinarith
 width:=by
  have r:UniformAllAxisSeedPreparation.radix n j≤  4*n:=
   (UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1
  have h:=search_bound c r
  unfold UniformWorkspaceSearchMachine.budget at h
  change 2*UniformAllAxisSeedPreparation.radix n j+173≤  envelope c n
  unfold envelope
  nlinarith

end
end ExactFourierCircuits.UniformJointCacheAllocation
