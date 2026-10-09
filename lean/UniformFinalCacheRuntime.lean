import UniformAxisCacheWholeExecution
import UniformCacheTimingCost
import UniformActualCalendarAsymptotics
import UniformCKernelPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCacheRuntime
open UniformAllAxisSeedPreparation UniformJointAllocation
noncomputable section

/-- The runtime of the real rank-kernel printer, spectrum producer, topology
printer and depth pass depends on sizes, not on the arena addresses. -/
lemma rank_budget (p:UniformRankCrossPreparationMachine.Parameters)(r L:ℕ)
 (hk:p.K≤r)(hw:UniformRadixTwoDAG.width p.K≤r)
 (ht:UniformRadixTwoDAG.count p.K≤r)
 (ha:p.a≤r)(he:p.e≤r)(hs:p.split≤r)
 (hg:UniformRankCrossPreparationMachine.Shape p≤r)
 (hl:Nat.log2 (p.D+1)+1≤L):
 UniformRankCrossPreparationMachine.runtimeBudget p≤10000*(r+1)^3+49*L:=by
 have kernel : UniformRankKernelMachine.runtime p.rank≤28+30*UniformRadixTwoDAG.width p.K+
  p.e*(19+11*p.split)+p.a*(21+11*p.split):=by
  simpa only[UniformRankKernelMachine.runtimeBudget,UniformRankCrossPreparationMachine.Parameters.rank]
   using UniformRankKernelMachine.runtime_bound p.rank
 have spectrum:=UniformKernelSpectrumMachine.runtime_log_bound p.D p.K
 have kprod:=Nat.mul_le_mul he (show 19+11*p.split≤19+11*r by omega)
 have aprod:=Nat.mul_le_mul ha (show 21+11*p.split≤21+11*r by omega)
 have fft:=Nat.mul_le_mul (show 19*p.K+85≤19*r+85 by omega) ht
 have top:=Nat.mul_le_mul (show 19*p.K+344≤19*r+344 by omega)
  (show UniformToeplitzCrossTopologyMachine.G p.K≤r by
   have:UniformToeplitzCrossTopologyMachine.G p.K≤UniformRankCrossPreparationMachine.Shape p:=by
    have eqG : UniformToeplitzCrossTopologyMachine.G p.K=3*p.K*UniformRadixTwoDAG.width p.K+
     2*UniformRadixTwoDAG.width p.K:=by
     simpa only[UniformToeplitzCrossTopologyMachine.G,UniformConvolutionDAG.records_length,
      UniformRadixTwoDAG.width_eq] using UniformConvolutionDAG.gate_count p.K
    rw[eqG];unfold UniformRankCrossPreparationMachine.Shape;omega
   omega)
 simp only[UniformRankCrossPreparationMachine.runtimeBudget,UniformDAGDepthMachine.runtimeBudget]
 nlinarith only[kernel,spectrum,kprod,aprod,fft,top,hk,hw,ha,he,hg,hl,
  Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3)]

lemma replay_budget (p:UniformRankCrossReplayPreparationMachine.ReplayParameters)(r L:ℕ)
 (hk:p.base.K≤r)(hw:UniformRadixTwoDAG.width p.base.K≤r)
 (ht:UniformRadixTwoDAG.count p.base.K≤r)
 (ha:p.base.a≤r)(he:p.base.e≤r)(hs:p.base.split≤r)
 (hg:UniformRankCrossPreparationMachine.Shape p.base≤r)
 (hl:Nat.log2 (p.base.D+1)+1≤L):
 UniformRankCrossReplayPreparationMachine.runtimeBudget p≤20000*(r+1)^3+49*L:=by
 have h:=rank_budget p.base r L hk hw ht ha he hs hg hl
 have mul:=Nat.mul_le_mul hg (show UniformRankCrossPreparationMachine.Shape p.base+1≤r+1 by omega)
 simp only[UniformRankCrossReplayPreparationMachine.runtimeBudget,UniformDAGBucketMachine.runtimeBudget,
  UniformReplayCoefficientMachine.runtime]
 nlinarith only[h,mul,hg,hk,hw,Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3)]

lemma height_budget (n:ℕ)(j:Fin (axisCount n))(c:UniformSeedHeightPreparation.Config)(r L:ℕ)
 (hk:c.exponent≤r)(hw:c.width≤r)(ht:UniformRadixTwoDAG.count c.exponent≤r)
 (ha:c.a≤r)(he:c.e≤r)(hs:c.split≤r)(hg:c.gates≤r)
 (hl:Nat.log2 (UniformMasterRootMachine.order n+1)+1≤L):
 UniformSeedHeightPreparation.runtimeBudget n j c≤1000000*(r+1)^4+49*L:=by
 have h:=replay_budget (UniformSeedHeightPreparation.parameters n j c) r L
  hk hw ht ha he hs hg hl
 have square:=Nat.pow_le_pow_left (show 2*c.gates+1≤2*r+1 by omega) 2
 have product:=Nat.mul_le_mul (show 8*c.exponent+7≤8*r+7 by omega)
  (show 64*c.gates+200*(2*c.gates+1)^2+56≤64*r+200*(2*r+1)^2+56 by omega)
 simp only[UniformSeedHeightPreparation.runtimeBudget,UniformSeedRankCrossPreparation.runtimeBudget]
 nlinarith only[h,product,hk,Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3),Nat.zero_le (r^4)]

structure Sizes (c:UniformSeedHeightPreparation.Config)(r:ℕ):Prop where
 exponent:c.exponent≤r
 width:c.width≤r
 count:UniformRadixTwoDAG.count c.exponent≤r
 target:c.a≤r
 source:c.e≤r
 split:c.split≤r
 gates:c.gates≤r

lemma sizes_of_capacity (c:UniformSeedHeightPreparation.Config)(r:ℕ)
 (capacity:UniformWorkspacePlanner.gateCount c.a c.e+c.a+c.e≤r)(split:c.split≤r):Sizes c r:=by
 have total:UniformConvolutionDAG.total c.exponent≤r:=by
  unfold UniformWorkspacePlanner.gateCount at capacity
  change 6*UniformConvolutionDAG.total c.exponent+2*c.a+c.a+c.e≤r at capacity
  omega
 have w:c.width≤r:=by dsimp[UniformConvolutionDAG.total] at total;change UniformRadixTwoDAG.width c.exponent≤r;omega
 have ct:UniformRadixTwoDAG.count c.exponent≤r:=by dsimp[UniformConvolutionDAG.total] at total;omega
 have kg:c.exponent≤c.width:=by
  have h:=UniformCrossDepthReplayPreparation.power_ge_successor c.exponent
  rw[←UniformRadixTwoDAG.width_eq] at h
  change c.exponent≤UniformRadixTwoDAG.width c.exponent;omega
 have gateEq:UniformWorkspacePlanner.gateCount c.a c.e=c.gates:=by
  rw[UniformWorkspacePlanner.gateCount_eq]
  simp only[UniformSeedHeightPreparation.Config.gates,UniformSeedHeightPreparation.Config.width,
   UniformSeedHeightPreparation.Config.exponent,UniformRadixTwoDAG.width_eq]
 exact ⟨kg.trans w,w,ct,by omega,by omega,split,by rw[←gateEq];omega⟩

lemma rectangle_budget (n:ℕ)(j:Fin (axisCount n))(q:UniformLocalRectangleDescriptors.Row)
 (original:UniformSeedHeightPreparation.Config)(work:UniformRankCrossPreparationMachine.Parameters)(r L:ℕ)
 (s:Sizes (UniformLocalRectangleBankMachine.geometry q original) r)
 (hl:Nat.log2 (UniformMasterRootMachine.order n+1)+1≤L):
 UniformLocalRectanglePhaseBanks.runtimeBudget n j q original work≤2000000*(r+1)^4+98*L:=by
 let c:=UniformLocalRectangleBankMachine.geometry q original
 change Sizes c r at s
 have height:=height_budget n j c r L s.exponent s.width s.count s.target s.source s.split s.gates hl
 have rank:=rank_budget
  (UniformConjugateRankSpectrumPreparation.selected n j
   (UniformLocalRectangleCoefficientMachine.nextParameters n j q original work)) r L
  s.exponent s.width s.count s.target s.source s.split s.gates hl
 have square:=Nat.pow_le_pow_left (show 2*c.gates+1≤2*r+1 by have:=s.gates;omega) 2
 have product:=Nat.mul_le_mul (show 8*c.exponent+7≤8*r+7 by have:=s.exponent;omega)
  (show 64*c.gates+200*(2*c.gates+1)^2+56≤64*r+200*(2*r+1)^2+56 by have:=s.gates;omega)
 simp only[UniformLocalRectanglePhaseBanks.runtimeBudget,UniformLocalRectangleCoefficientMachine.runtimeBudget,
  UniformLocalReplayAssembly.prefix_total]
 change UniformSeedHeightPreparation.runtimeBudget n j c+
  UniformRankCrossPreparationMachine.runtimeBudget _+91*c.width+71+
  247*(4*(8*c.exponent+6+1)+2)+113+
  (4*c.exponent+34+(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56))+1≤_
 nlinarith only[height,rank,product,s.exponent,s.width,Nat.zero_le r,
  Nat.zero_le (r^2),Nat.zero_le (r^3),Nat.zero_le (r^4)]

lemma request_budget (n:ℕ)(j:Fin (axisCount n))(q:UniformLocalRectangleDescriptors.Row)(L:ℕ)
 (g:UniformJointCacheWorkspace.Geometry n j q)(width:q.width≤radix n j)
 (hl:Nat.log2 (UniformMasterRootMachine.order n+1)+1≤L):
 UniformLocalStoredRequestLoop.requestCharge n j q≤10000000*(radix n j+1)^4+98*L:=by
 let r:=radix n j
 let c:=UniformJointCacheWorkspace.original n q
 have s:Sizes c r:=sizes_of_capacity c r g.capacity (by exact le_of_lt g.gSplit)
 have b:=rectangle_budget n j q c (UniformJointCacheWorkspace.work n) r L s hl
 have mul:=Nat.mul_le_mul
  (show UniformLocalRequestPlan.slotCount n q≤352*r+330 by change 352*c.exponent+330≤_;have:=s.exponent;omega)
  (show 4*c.exponent+191*q.width+227*r+315≤4*r+191*r+227*r+315 by have:=s.exponent;omega)
 simp only[UniformLocalStoredRequestLoop.requestCharge,UniformLocalStoredRequestLoop.bodyCharge]
 change UniformLocalRectanglePhaseBanks.runtimeBudget n j q c (UniformJointCacheWorkspace.work n)+
  UniformLocalRequestPlan.slotCount n q*(4*c.exponent+191*q.width+227*r+315)+153+16≤_
 nlinarith only[b,mul,Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3),Nat.zero_le (r^4)]

lemma master_log_bound {n:ℕ}(hn:0<n):
 Nat.log2 (UniformMasterRootMachine.order n+1)+1≤12*Nat.clog 2 (n+2)+1:=by
 have poly:UniformMasterRootMachine.order n+1≤(n+2)^12:=by
  have h:=(UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have o:=(UniformMasterRootMachine.order_bounds hn).2
  omega
 have power:(n+2)^12≤2^(12*Nat.clog 2 (n+2)):=by
  calc
   _≤(2^Nat.clog 2 (n+2))^12:=Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 12
   _=_:=by rw[←pow_mul,Nat.mul_comm]
 have clog:=Nat.clog_le_of_le_pow (poly.trans power)
 have log:Nat.log2 (UniformMasterRootMachine.order n+1)≤12*Nat.clog 2 (n+2):=by
  rw[Nat.log2_eq_log_two]
  exact (Nat.log_le_clog _ _).trans clog
 omega

lemma costPrefix_bound (n:ℕ)(j:Fin (axisCount n))(qs:List UniformLocalRequestPlan.Request)
 (C:ℕ)(bound:∀q∈qs,UniformLocalStoredRequestLoop.requestCharge n j q.row≤C):
 ∀k,k≤qs.length→UniformLocalStoredRequestLoop.costPrefix n j qs k≤k*C:=by
 intro k hk
 induction k with
 | zero=>simp[UniformLocalStoredRequestLoop.costPrefix]
 | succ k ih=>
  rw[UniformLocalStoredRequestLoop.costPrefix_step n j qs k (by omega)]
  have b:=bound (qs[k]'(by omega)) (List.getElem_mem (by omega))
  have t:=ih (by omega)
  rw[Nat.add_mul,Nat.one_mul]
  omega

lemma canonical_request_budget (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n))(L:ℕ)
 (hl:Nat.log2 (UniformMasterRootMachine.order n+1)+1≤L):
 UniformLocalStoredRequestLoop.costPrefix n j (UniformAxisCacheCanonicalRequests.canonical c n j)
  (UniformAxisCacheCanonicalRequests.canonical c n j).length≤
 (radix n j)^2*(10000000*(radix n j+1)^4+98*L):=by
 let qs:=UniformAxisCacheCanonicalRequests.canonical c n j
 have geo:=UniformAxisCacheCanonicalRequests.geometry c n hn j
 have each:∀q∈qs,UniformLocalStoredRequestLoop.requestCharge n j q.row≤10000000*(radix n j+1)^4+98*L:=by
  intro q member
  obtain ⟨k,hk,rfl⟩:=List.getElem_of_mem member
  obtain ⟨v,o,hv,hp,extent,inRows⟩:=UniformAxisCacheRequestBounds.origin (radix n j)
   (UniformJointCacheAllocation.axis c n j).requests (qs[k]'hk) (List.getElem_mem hk)
  have width:(qs[k]'hk).row.width=v:=by
   unfold UniformLocalRectangleDescriptors.rows at inRows
   obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp inRows
   obtain ⟨j,_,eq⟩:=List.mem_map.mp hi
   rw[←eq];rfl
  apply request_budget n j _ L (geo.workspace k hk) (by change (qs[k]'hk).row.width≤radix n j;omega) hl
 have b:=costPrefix_bound n j qs _ each qs.length le_rfl
 have len:=UniformAxisCacheCanonicalRequests.length_bound c n j
 exact b.trans (Nat.mul_le_mul_right _ len)

lemma timing_budget (r R:ℕ):UniformLocalCacheTimingExecution.printerBudget r 0 R≤1000*(r+1)^3:=by
 let vs:=UniformLocalCacheTimingMetadata.rootVisits r 0 R
 have each:∀q∈vs,∀a∈UniformLocalCacheTreeCoverage.currentRows q.task,
  Nat.clog 2 (2*(a.a+a.e))≤2*r:=by
  intro q hq a ha
  have width:=UniformLocalCacheTimingMetadata.root_width r 0 R q hq
  have dims:=UniformLocalCacheTimingMetadata.current_row_dimensions q.task a ha
  have power:=UniformCrossDepthReplayPreparation.power_ge_successor (2*r)
  apply Nat.clog_le_of_le_pow
  omega
 have b:=UniformCacheTimingCost.whole_ticks_bound vs (2*r) each
 have poly:=UniformCacheTimingCost.polynomial_bound r vs.length
  (UniformLocalCacheTreeExecution.visitSum vs)
  (UniformAxisCacheTimingGeometry.nodes_bound r R) (UniformAxisCacheTimingGeometry.requests_bound r R)
 exact b.trans (by convert poly using 1;ring)

lemma axis_budget (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (axisCount n))(L:ℕ)
 (hl:Nat.log2 (UniformMasterRootMachine.order n+1)+1≤L):
 UniformAxisCacheAxisExecution.budget c n j+11≤
 100000000*(radix n j+1)^6*(L+1):=by
 let r:=radix n j
 let R:=(UniformJointCacheAllocation.axis c n j).requests
 have req:=canonical_request_budget c n hn j L hl
 have timing:=timing_budget r R
 have nodes:=UniformAxisCacheTimingGeometry.nodes_bound r R
 have demand:UniformDirectLeafForestModel.demand (UniformAxisCacheForestEntry.visits c n j)≤r^2:=by
  have eq:=UniformDirectLeafForestModel.root_demand r 0 R
  have b:=UniformJointCacheTime.leaf_operations_bound (UniformBalancedToeplitz.plan r)
  rw[←eq] at b
  exact b
 have dm:=Nat.mul_le_mul_left (62*r+246) demand
 have nm:=Nat.mul_le_mul_left 93 nodes
 have clog:Nat.clog 2 (4*r)≤4*r:=by
  apply Nat.clog_le_of_le_pow
  have:=UniformCrossDepthReplayPreparation.power_ge_successor (4*r)
  omega
 have small: (r+1)^2≤(r+1)^6:=by
  nlinarith only[Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3),
   Nat.zero_le (r^4),Nat.zero_le (r^5),Nat.zero_le (r^6)]
 have more:=Nat.mul_le_mul_right L small
 simp only[UniformAxisCacheAxisExecution.budget,UniformLocalCacheTreeExecution.nodeBudget]
 change 4*Nat.clog 2 (4*r)+66+((2*r+1)*(256*(r+1)^4+(22*r+9)*r+69)+18)+6+
  UniformLocalCacheTimingExecution.printerBudget r 0 R+7+8+
  (UniformLocalStoredRequestLoop.costPrefix n j (UniformAxisCacheCanonicalRequests.canonical c n j)
   (UniformAxisCacheCanonicalRequests.canonical c n j).length+23)+
  ((62*r+246)*UniformDirectLeafForestModel.demand (UniformAxisCacheForestEntry.visits c n j)+
   93*(UniformAxisCacheForestEntry.visits c n j).length+40)+11≤_
 change _≤r^2*(10000000*(r+1)^4+98*L) at req
 change 93*(UniformAxisCacheForestEntry.visits c n j).length≤93*(2*r+1) at nm
 nlinarith only[req,timing,dm,nm,clog,more,Nat.zero_le L,Nat.zero_le (r^2*L),
  Nat.zero_le r,Nat.zero_le (r^2),Nat.zero_le (r^3),Nat.zero_le (r^4),Nat.zero_le (r^5),Nat.zero_le (r^6)]

end
end ExactFourierCircuits.UniformFinalCacheRuntime
