import UniformFinalCacheAsymptotics
import UniformGlobalDiagonalChildPrefix

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
§5.2 (5.6), PDF p.22 (`eq:working-transform`), and §5.4, PDF pp.23-24 (`thm:main`).

Charged-budget bookkeeping refines the paper's composition of local work,
array movement and three transforms. Cache/register constants and conservative
majorants are implementation details, without separate paper statements.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOverhead
open UniformAllAxisSeedPreparation UniformFinalCacheAsymptotics Filter Asymptotics
noncomputable section

/-- One conservative majorant for all real389 branches, followed by the axis
factor consumer. The selected count and the scanned registry are bounded
separately by the actual cache capacity. -/
def axisScanBudget(r:ℕ):ℕ:=4*Nat.clog 2 (4*r)+16*(2*r+1)+136*r+533+
 UniformJointCacheExtent.capacity r*(9*r+69)
lemma axis_scan_bound(r prep N entries nodes:ℕ)
 (hp:prep ≤ 4*Nat.clog 2 (4*r)+169+21*entries+16*nodes+70*r+112+19)
 (hn:N ≤ UniformJointCacheExtent.capacity r)(he:entries ≤ UniformJointCacheExtent.capacity r)
 (hd:nodes ≤ 2*r+1):
 prep+66*r+233+N*(9*r+48) ≤ axisScanBudget r:=by
 have m:=Nat.mul_le_mul_right (9*r+48) hn
 have e:=Nat.mul_le_mul_left 21 he
 have d:=Nat.mul_le_mul_left 16 hd
 unfold axisScanBudget
 nlinarith only[hp,m,e,d]

lemma axisScanBudget_bound(r:ℕ):axisScanBudget r ≤ 1000000*(r+1)^4:=by
 have log:Nat.clog 2 (4*r) ≤ 4*r:=Nat.clog_le_of_le_pow
  (UniformRecursiveBatchHeaderMachine.index_le_power (4*r))
 have cap:UniformJointCacheExtent.capacity r ≤ r^2*(1408*r+334):=by
  have b:UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4 ≤ 1408*r+334:=by
   rw[UniformJointCacheExtent.slotCount_formula];omega
  exact Nat.mul_le_mul_left (r^2) b
 have product:=Nat.mul_le_mul_right (9*r+69) cap
 unfold axisScanBudget
 nlinarith only[log,product,Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3),Nat.zero_le (r^4)]

def axesScanBudget(n:ℕ):ℕ:=∑j:Fin (axisCount n),axisScanBudget (radix n j)
def scanUnit:ℕ:=1000000*129^4
lemma axesScanBudget_bound(n:ℕ)(hn:0<n):axesScanBudget n ≤ scanUnit*axisSize n^9:=by
 let t:=axisSize n
 have each(j:Fin (axisCount n)):axisScanBudget (radix n j) ≤ 1000000*129^4*t^8:=by
  have b:=UniformSelectedCRT.radix_quadratic hn j
  have pos:1 ≤ t^2:=by have h:=pow_pos (show 0<t by dsimp[t,axisSize];omega) 2;omega
  have hr:radix n j+1 ≤ 129*t^2:=by change radix n j ≤ 128*t^2 at b;omega
  have p:=Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hr 4)
  exact (axisScanBudget_bound _).trans (by convert p using 1;ring)
 have sum:=Finset.sum_le_sum (fun j (_:j∈Finset.univ)=> each j)
 have count:axisCount n ≤ t:=by unfold axisCount UniformInitialPreparation.ell;dsimp[t,axisSize];omega
 have mul:=Nat.mul_le_mul_right (1000000*129^4*t^8) count
 simp only[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sum
 calc
  axesScanBudget n ≤ axisCount n*(1000000*129^4*t^8):=sum
  _ ≤ t*(1000000*129^4*t^8):=mul
  _ = scanUnit*axisSize n^9:=by dsimp[t,scanUnit];ring

lemma horizon_isBigO_log_four :
 (fun n:ℕ=> (UniformFourierClockBounds.horizon n:ℝ)) =O[atTop] (fun n:ℕ=> Real.log (n:ℝ)^4):=by
 have h:(fun n:ℕ=> (UniformFourierClockBounds.horizon n:ℝ)) =O[atTop] (fun n:ℕ=> (axisSize n:ℝ)^4):=by
  apply IsBigO.of_bound (UniformActualCalendarLogBounds.horizonUnit:ℝ)
  filter_upwards[eventually_ge_atTop (1:ℕ)] with n hn
  have bound:=UniformActualCalendarLogBounds.horizon_bound (show 0<n by omega)
  have log:UniformNetworkCost.logFactor n ≤ (axisSize n:ℝ):=by
   have b:=Real.log_le_sub_one_of_pos (show 0<(axisSize n:ℝ) by exact_mod_cast (show 0<axisSize n by unfold axisSize;omega))
   unfold UniformNetworkCost.logFactor axisSize at *
   linarith
  have power:=pow_le_pow_left₀ (show (0:ℝ) ≤ UniformNetworkCost.logFactor n by linarith[UniformNetworkCost.logFactor_one_le n]) log 4
  have scaled:=mul_le_mul_of_nonneg_left power (Nat.cast_nonneg UniformActualCalendarLogBounds.horizonUnit)
  have result:=bound.trans scaled
  simpa only[Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity:0 ≤ (axisSize n:ℝ)^4)] using result
 exact h.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 4)

lemma axesScanBudget_isBigO_log_nine:
 (fun n:ℕ=> (axesScanBudget n:ℝ)) =O[atTop] (fun n:ℕ=> Real.log (n:ℝ)^9):=by
 have h:(fun n:ℕ=> (axesScanBudget n:ℝ)) =O[atTop] (fun n:ℕ=> (axisSize n:ℝ)^9):=by
  apply IsBigO.of_bound (scanUnit:ℝ)
  filter_upwards[eventually_ge_atTop (1:ℕ)] with n hn
  have b:(axesScanBudget n:ℝ) ≤ (scanUnit:ℝ)*(axisSize n:ℝ)^9:=by exact_mod_cast axesScanBudget_bound n (show 0<n by omega)
  simpa only[Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity:0 ≤ (axisSize n:ℝ)^9)] using b
 exact h.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 9)

def clockScanBudget(n:ℕ):ℕ:=7+UniformFourierClockBounds.horizon n*(8+axesScanBudget n)
lemma clockScanBudget_isLittleO_input:
 (fun n:ℕ=> (clockScanBudget n:ℝ)) =o[atTop] (fun n:ℕ=> (n:ℝ)):=by
 have constant8:(fun _n:ℕ=> (8:ℝ)) =O[atTop] (fun n:ℕ=> Real.log (n:ℝ)^9):=by
  apply IsBigO.of_bound 8
  have ht:Tendsto (fun n:ℕ=> Real.log (n:ℝ)) atTop atTop:=Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards[ht.eventually (eventually_ge_atTop (1:ℝ))] with n hn
  have power:=one_le_pow₀ hn (n:=9)
  simp only[Real.norm_of_nonneg (by norm_num:0 ≤ (8:ℝ)),Real.norm_of_nonneg (by positivity:0 ≤ Real.log (n:ℝ)^9)]
  nlinarith only[power]
 have product:=horizon_isBigO_log_four.mul (constant8.add axesScanBudget_isBigO_log_nine)
 have p:(fun n:ℕ=> (UniformFourierClockBounds.horizon n:ℝ)*(8+(axesScanBudget n:ℝ))) =O[atTop]
  (fun n:ℕ=> Real.log (n:ℝ)^13):=by
  convert product using 1
  ext n;ring
 have little:(fun n:ℕ=> Real.log (n:ℝ)^13) =o[atTop] (fun n:ℕ=> (n:ℝ)):=
  Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
 have constant7:(fun _n:ℕ=> (7:ℝ)) =o[atTop] (fun n:ℕ=> (n:ℝ)):=
  (isLittleO_const_id_atTop (7:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
 simpa only[clockScanBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using constant7.add (p.trans_isLittleO little)

lemma radix_list_bounds(rs:List ℕ)(h:∀r∈rs,2 ≤ r):1 ≤ rs.prod∧rs.sum ≤ 2*rs.prod∧rs.length ≤ rs.prod:=by
 induction rs with
 | nil=> norm_num
 | cons r rs ih=>
  have head:=h r (by simp)
  have tail:=ih (fun q hq=> h q (by simp[hq]))
  have first:=Nat.mul_le_mul_left r tail.1
  have second:=Nat.mul_le_mul_right rs.prod head
  simp only[List.prod_cons,List.sum_cons,List.length_cons]
  omega

/-- The actual147 diagonal tree and its following copy are linear in volume,
including the per-axis coefficient printing. No axis count multiplies volume. -/
lemma diagonal_extra_linear{W:ℕ}(d:UniformGlobalDiagonalChildPrefix.Context W)
 (h:∀a∈d.entries,2 ≤ a.radix):
 UniformGlobalDiagonalChildPrefix.diagonalTicks d+7*(W*d.tensor.volume)+29 ≤ (130*W+100)*d.tensor.volume:=by
 let rs:=d.entries.map UniformGlobalDiagonalRowsMachine.Entry.radix
 have good:∀r∈rs,2 ≤ r:=by intro r hr;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr;exact h a ha
 obtain ⟨positive,sum,length⟩:=radix_list_bounds rs good
 have nodes:UniformTraversal.nodeCount rs ≤ 2*rs.prod:=(UniformTraversal.nodeCount_lt_twice_product rs good).le
 have balance:=UniformTensorMonomialMachine.treeCost_balance rs
 have tree:UniformTensorMonomialMachine.treeCost rs ≤ 102*rs.prod:=by omega
 have scaled:=Nat.mul_le_mul_left W tree
 have fixed:=Nat.mul_le_mul_left (20*W+43) positive
 dsimp only[rs] at positive sum length tree scaled fixed
 change (d.entries.map UniformGlobalDiagonalRowsMachine.Entry.radix).sum ≤ 2*_ at sum
 rw[←d.tensorVolume] at sum tree positive scaled fixed
 simp only[List.length_map] at length
 rw[d.entryLength,←d.tensorVolume] at length
 change UniformGlobalDiagonalRowsMachine.amount d.entries ≤ 2*d.tensor.volume at sum
 rw[d.entryTotal] at sum
 unfold UniformGlobalDiagonalChildPrefix.diagonalTicks
 nlinarith only[sum,length,scaled,fixed]

end
end ExactFourierCircuits.UniformFinalClockOverhead
