import UniformFinalCacheRuntime
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCacheAsymptotics
open UniformAllAxisSeedPreparation UniformJointAllocation Filter Asymptotics
noncomputable section

def axisSize (n:ℕ):ℕ:=UniformWorkingLength.axisCount n+2
def logSize (n:ℕ):ℕ:=Nat.clog 2 (n+2)+1
def cacheUnit:ℕ:=1200000000*129^6
def cacheBudget (c:Constants)(n:ℕ):ℕ:=20+axisCount n*UniformAxisCacheLoopState.maxBudget c n+1

lemma maxBudget_bound (c:Constants)(n:ℕ)(hn:0<n):
 UniformAxisCacheLoopState.maxBudget c n≤cacheUnit*axisSize n^12*logSize n:=by
 apply Finset.sup_le
 intro j _
 let t:=axisSize n
 have ht:2≤t:=by dsimp[t,axisSize];omega
 have hr:radix n j+1≤129*t^2:=by
  have b:=UniformSelectedCRT.radix_quadratic hn j
  change radix n j≤128*t^2 at b
  have one:1≤t^2:=by have:=pow_pos (show 0<t by omega) 2;omega
  omega
 have pow:=Nat.pow_le_pow_left hr 6
 have log:12*Nat.clog 2 (n+2)+1+1≤12*logSize n:=by unfold logSize;omega
 have b:=UniformFinalCacheRuntime.axis_budget c n hn j _ (UniformFinalCacheRuntime.master_log_bound hn)
 calc
  UniformAxisCacheAxisExecution.budget c n j+11≤100000000*(radix n j+1)^6*(12*Nat.clog 2 (n+2)+1+1):=b
  _≤100000000*(129*t^2)^6*(12*logSize n):=Nat.mul_le_mul (Nat.mul_le_mul_left _ pow) log
  _=cacheUnit*axisSize n^12*logSize n:=by dsimp[cacheUnit,t];ring

lemma logSize_isBigO_log : (fun n:ℕ=>(logSize n:ℝ)) =O[atTop] (fun n:ℕ=>Real.log (n:ℝ)):=by
 apply IsBigO.of_bound 8
 have htlog:Tendsto (fun n:ℕ=>Real.log (n:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
 filter_upwards[eventually_ge_atTop (1:ℕ),htlog.eventually (eventually_ge_atTop (1:ℝ))] with n hn hlog
 have hnpos:0<n:=by omega
 have nonneg:0≤Real.log ((n+2:ℕ):ℝ):=Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega))
 have clog:(Nat.clog 2 (n+2):ℝ)≤Real.logb 2 ((n+2:ℕ):ℝ)+1:=by
  have h:0≤Real.logb 2 ((n+2:ℕ):ℝ):=Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤n+2 by omega))
  rw[←Real.natCeil_logb_natCast 2 (n+2)]
  exact (Nat.ceil_lt_add_one h).le
 have shift:Real.log ((n+2:ℕ):ℝ)≤2+Real.log (n:ℝ):=by
  have hp:0<(n:ℝ):=by exact_mod_cast hnpos
  have le:((n+2:ℕ):ℝ)≤3*(n:ℝ):=by exact_mod_cast (show n+2≤3*n by omega)
  have h:=Real.log_le_log (by positivity:0<((n+2:ℕ):ℝ)) le
  rw[Real.log_mul (by norm_num) hp.ne'] at h
  have three:Real.log (3:ℝ)≤2:=by
   have h:=Real.log_le_sub_one_of_pos (by norm_num:0<(3:ℝ));norm_num at h;exact h
  linarith
 have frac:Real.log ((n+2:ℕ):ℝ)/Real.log 2≤2*Real.log ((n+2:ℕ):ℝ):=by
  apply (div_le_iff₀ (Real.log_pos (by norm_num:1<(2:ℝ)))).2
  have lower:=UniformWorkingLength.log_two_lower
  have h:=mul_nonneg nonneg (show 0≤2*Real.log 2-1 by linarith)
  nlinarith
 rw[Real.logb] at clog
 have bound:(logSize n:ℝ)≤8*Real.log (n:ℝ):=by
  simp only[logSize,Nat.cast_add,Nat.cast_one];linarith
 simpa only[Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by linarith:0≤Real.log (n:ℝ))] using bound

lemma maxBudget_isBigO_log_thirteen (c:Constants):
 (fun n:ℕ=>(UniformAxisCacheLoopState.maxBudget c n:ℝ)) =O[atTop] (fun n:ℕ=>Real.log (n:ℝ)^13):=by
 have h:(fun n:ℕ=>(UniformAxisCacheLoopState.maxBudget c n:ℝ)) =O[atTop]
  (fun n:ℕ=>(axisSize n:ℝ)^12*(logSize n:ℝ)):=by
  apply IsBigO.of_bound (cacheUnit:ℝ)
  filter_upwards[eventually_ge_atTop (1:ℕ)] with n hn
  have h:=maxBudget_bound c n (show 0<n by omega)
  have cast:(UniformAxisCacheLoopState.maxBudget c n:ℝ)≤(cacheUnit:ℝ)*(axisSize n:ℝ)^12*(logSize n:ℝ):=by exact_mod_cast h
  simpa only[Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity:0≤(axisSize n:ℝ)^12*(logSize n:ℝ)),mul_assoc] using cast
 have axis:(fun n:ℕ=>(axisSize n:ℝ)) =O[atTop] (fun n:ℕ=>Real.log (n:ℝ)):=UniformWorkingPreparation.axisCount_plus_two_isBigO_log
 have product: (fun n:ℕ=>(axisSize n:ℝ)^12*(logSize n:ℝ)) =O[atTop] (fun n:ℕ=>Real.log (n:ℝ)^13):=by
  simpa only[pow_succ] using (axis.pow 12).mul logSize_isBigO_log
 exact h.trans product

lemma cacheBudget_isLittleO_input (c:Constants):
 (fun n:ℕ=>(cacheBudget c n:ℝ)) =o[atTop] (fun n:ℕ=>(n:ℝ)):=by
 have count:(fun n:ℕ=>(axisCount n:ℝ)) =O[atTop] (fun n:ℕ=>Real.log (n:ℝ)):=by
  have small:(fun n:ℕ=>(axisCount n:ℝ)) =O[atTop] (fun n:ℕ=>(axisSize n:ℝ)):=by
   apply IsBigO.of_bound 1
   filter_upwards[] with n
   have h:axisCount n≤axisSize n:=by unfold axisCount axisSize UniformInitialPreparation.ell;omega
   simpa only[one_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)] using (show (axisCount n:ℝ)≤(axisSize n:ℝ) by exact_mod_cast h)
  exact small.trans UniformWorkingPreparation.axisCount_plus_two_isBigO_log
 have prod:(fun n:ℕ=>(axisCount n:ℝ)*(UniformAxisCacheLoopState.maxBudget c n:ℝ)) =O[atTop]
  (fun n:ℕ=>Real.log (n:ℝ)^14):=by
  convert count.mul (maxBudget_isBigO_log_thirteen c) using 1
  ext n;ring
 have little:(fun n:ℕ=>Real.log (n:ℝ)^14) =o[atTop] (fun n:ℕ=>(n:ℝ)):=
  Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
 have constant:(fun _n:ℕ=>(21:ℝ)) =o[atTop] (fun n:ℕ=>(n:ℝ)):=
  (isLittleO_const_id_atTop (21:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
 convert constant.add (prod.trans_isLittleO little) using 1
 ext n
 simp only[cacheBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
 ring

end
end ExactFourierCircuits.UniformFinalCacheAsymptotics
