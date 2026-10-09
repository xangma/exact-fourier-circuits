import UniformGlobalAxisCalendarArena

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisWorkspace
open UniformJointAllocation UniformJointCacheAllocation UniformJointCacheExtent
namespace Arena
export UniformGlobalCalendarArena (natBase scalarBase size)
end Arena
open scoped BigOperators

/-- Selected entries, raw call rows, three radix tables and a phase word bank. -/
def natAmount(r:ℕ):ℕ:=2*capacity r+9*r+80
lemma natAmount_bound{r:ℕ}(positive:2 ≤ r):natAmount r ≤ natSize r:=by
 have square:4 ≤ r^2:=by nlinarith only [positive]
 have cap:16 ≤ capacity r:=Nat.mul_le_mul square (show 4 ≤ slotCount (Nat.clog 2 (4*r))+4 by omega)
 have h:4*capacity r ≤ (3*r+11)*capacity r:=
  Nat.mul_le_mul_right _ (by omega)
 unfold natAmount natSize
 nlinarith only [h,positive,cap]

noncomputable section
def natPrefix(n k:ℕ):ℕ:=offsetSum (fun i=>natAmount (UniformAllAxisSeedPreparation.radixAt n i)) k
def natDemand(n:ℕ):ℕ:=natPrefix n (ell n)
lemma demand_bound{n:ℕ}(hn:0<n):natDemand n ≤ natTotal n:=by
 unfold natDemand natPrefix natTotal offsetSum
 apply Finset.sum_le_sum
 intro i hi
 have lt:i<ell n:=Finset.mem_range.mp hi
 rw [UniformAllAxisSeedPreparation.radixAt_eq n ⟨i,lt⟩]
 exact natAmount_bound (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn ⟨i,lt⟩)
lemma prefix_step(n k:ℕ):natPrefix n (k+1)=natPrefix n k+
 natAmount (UniformAllAxisSeedPreparation.radixAt n k):=offsetSum_step _ _
lemma prefix_mono(n:ℕ){i j:ℕ}(h:i ≤ j):natPrefix n i ≤ natPrefix n j:=offsetSum_mono _ h
lemma demand_fits(c:Constants){n:ℕ}(hn:0<n):
 Arena.natBase c n+natDemand n ≤ 2*slab c n ∧
 Arena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n (ell n) ≤ 2*slab c n:=by
 have budget:=UniformGlobalCalendarArena.axis_budgets n
 have nd: natDemand n ≤ Arena.size n:=(demand_bound hn).trans budget.1
 exact ⟨(Nat.add_le_add_left nd _).trans (UniformGlobalCalendarArena.nat_fits c hn),
  (Nat.add_le_add_left budget.2.2 _).trans (UniformGlobalCalendarArena.scalar_fits c hn)⟩

structure AxisAddresses where
 selected:ℕ
 boundary:ℕ
 rawRows:ℕ
 permutation:ℕ
 widths:ℕ
 markers:ℕ
 phase:ℕ
 endNat:ℕ
 pool:ℕ
 endScalar:ℕ
 deriving Repr,DecidableEq

def axisBank(r N S:ℕ):AxisAddresses:=
 let boundary:=N+2*capacity r
 let phase:=boundary+3*r+11
 let T:=phase+64
 let P:=T+3*r
 let W:=P+r
 let M:=W+r
 ⟨N,boundary,T,P,W,M,phase,M+r+5,S,S+9*r⟩
lemma axis_ends(r N S:ℕ):
 (axisBank r N S).endNat=N+natAmount r ∧(axisBank r N S).endScalar=S+9*r:=by
 dsimp [axisBank,natAmount]
 exact ⟨by ring,rfl⟩
def axis(c:Constants)(n:ℕ)(j:Fin (ell n)):AxisAddresses:=
 axisBank (UniformAllAxisSeedPreparation.radix n j)
  (Arena.natBase c n+natPrefix n j.val)
  (Arena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val)
lemma axis_fit(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (axis c n j).endNat ≤ 2*slab c n ∧(axis c n j).endScalar ≤ 2*slab c n:=by
 have en:=prefix_mono n (Nat.succ_le_of_lt j.isLt)
 rw [prefix_step,UniformAllAxisSeedPreparation.radixAt_eq n j] at en
 have es:=UniformAllAxisSeedPreparation.prefix_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformAllAxisSeedPreparation.prefix_succ,UniformAllAxisSeedPreparation.radixAt_eq n j] at es
 have fits:=demand_fits c hn
 unfold axis
 rw [(axis_ends _ _ _).1,(axis_ends _ _ _).2]
 change _ ≤ 2*slab c n ∧ _ ≤ 2*slab c n
 constructor
 · calc
    Arena.natBase c n+natPrefix n j.val+natAmount (UniformAllAxisSeedPreparation.radix n j) =
     Arena.natBase c n+(natPrefix n j.val+natAmount (UniformAllAxisSeedPreparation.radix n j)):=Nat.add_assoc _ _ _
    _ ≤ Arena.natBase c n+natPrefix n (ell n):=Nat.add_le_add_left en _
    _ ≤ 2*slab c n:=fits.1
 · have scaled:=Nat.mul_le_mul_left 9 es
   calc
    Arena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val+
     9*UniformAllAxisSeedPreparation.radix n j =
      Arena.scalarBase c n+9*(UniformAllAxisSeedPreparation.prefixSum n j.val+
       UniformAllAxisSeedPreparation.radix n j):=by ring
    _ ≤ _:= (Nat.add_le_add_left scaled _).trans fits.2
lemma axis_geometry(c:Constants)(n:ℕ)(j:Fin (ell n)):
 let r:=UniformAllAxisSeedPreparation.radix n j
 let a:=axis c n j
 a.selected+2*capacity r=a.boundary ∧a.boundary+3*r+11=a.phase ∧
 a.phase+64=a.rawRows ∧a.rawRows+3*r=a.permutation ∧
 a.permutation+r=a.widths ∧a.widths+r=a.markers ∧a.markers+r+5=a.endNat:=by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma caches_before(c:Constants)(n:ℕ)(i j:Fin (ell n)):
 (UniformJointCacheAllocation.axis c n i).endNat ≤ (axis c n j).selected ∧
 (UniformJointCacheAllocation.axis c n i).endScalar ≤ (axis c n j).pool:=by
 have oldN:=UniformGlobalCalendarArena.prior_nat c n i
 have oldS:=UniformGlobalCalendarArena.prior_scalar c n i
 change _ ≤ Arena.natBase c n+natPrefix n j.val ∧
  _ ≤ Arena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val
 exact ⟨oldN.trans (Nat.le_add_right _ _),oldS.trans (Nat.le_add_right _ _)⟩
lemma boundary_before_caches(c:Constants)(n:ℕ)(j:Fin (ell n)):
 slab c n+9*UniformAllAxisSeedPreparation.radix n j ≤ UniformJointCacheAllocation.scalarStart c n:=by
 have h:=UniformAllAxisSeedPreparation.prefix_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformAllAxisSeedPreparation.prefix_succ,UniformAllAxisSeedPreparation.radixAt_eq n j] at h
 unfold UniformJointCacheAllocation.scalarStart
 omega
lemma boundary_before_merged(c:Constants)(n:ℕ)(j:Fin (ell n)):
 slab c n+9*UniformAllAxisSeedPreparation.radix n j ≤ (axis c n j).pool:=by
 have h:=boundary_before_caches c n j
 change _ ≤ Arena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val
 have old:UniformJointCacheAllocation.scalarStart c n ≤ Arena.scalarBase c n:=by
  unfold Arena.scalarBase UniformJointCacheAllocation.scalarEnd
  omega
 exact h.trans (old.trans (Nat.le_add_right _ _))

end
end ExactFourierCircuits.UniformFourierAxisWorkspace
