import UniformCacheLowRectangle
import UniformLocalStoredRectanglePreparation
import UniformLocalRectangleCachePriorRetention
import UniformLocalStoredRequestGeometry
import UniformCanonicalCachePhaseEnds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRectanglePreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors UniformJointAllocation
open UniformLocalRectangleCacheBindings UniformLocalCacheSlotConductorMachine
noncomputable section
/-- One fixed charged program starts at the actual stored request and workspace
bank. It derives the low row, all reused producer headers, both spectra and
enabled banks, and every six-phase cached factor/partition entry internally. -/
theorem execution_low (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n))(D:ℕ)(q:Row)
 (g:UniformJointCacheWorkspace.Geometry n j q)(c:Header.Parameters)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (geometry:Geometry (envelope constants n) c q ha he (W.inverse n))
 (binding:Bindings c q (W.original n q) (W.lowRow n) (W.control n) (W.conjugate n)
  (W.falseRows n) (W.falseColors n) (W.falsePalette n) (W.falseDirectory n))
 (prefixPlacement:UniformLocalCacheContextConductor.Prefixes n c)
 (workspaces:∀k (hk:k<352*c.height.K+330) slot (witness:SlotWitness c.height.K k slot),
  UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c k) q slot
   (geometry.layout k hk slot witness) (geometry.broadcast k hk) ha he (W.inverse n) ≤ slab constants n)
 (x:Fin n → ℂ)(s:State)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)(axis:s.natReg 4200=j.val)
 (pointer:s.natReg 6173=D)(source:UniformLocalRectangleBankMachine.RowSource D q s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)(seed:Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (operands:UniformInitialPreparation.Operands n x s)
 (driver:Driver j c (W.inverse n) (slab constants n) s)
 (apart:W.lowRow n+7 ≤ D)(db:D+7 ≤ envelope constants n)
 (code:3738 ≤ envelope constants n)(total:352*c.height.K+330 ≤ envelope constants n)
 (scalar:9*c.ambient ≤ envelope constants n)(natural:3*c.ambient+11 ≤ envelope constants n)
 (contextLow:W.z n≤c.borrowed∧W.z n≤c.pool∧W.z n≤c.mu∧W.z n≤c.conjugateMu)
 (pc:s.pc=0)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedExecution program n x (envelope constants n) s ticks u ∧
 ticks ≤ UniformLocalRectanglePhaseBanks.runtimeBudget n j q (W.original n q) (W.work n)+
  (352*c.height.K+330)*(bodyBudget c q+11)+153 ∧ u.pc=3737 ∧
 (∀k,k<352*c.height.K+330 → Cached (B:=envelope constants n) c q ha he (coefficientBank j q (W.original n q) c) geometry.positive k u) ∧
 Cursor.Control c (352*c.height.K+330) u ∧
 Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀i,slab constants n ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 (∀i,slab constants n ≤ i → (i<c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) →
  i≠c.mu → i≠c.conjugateMu → u.scalarHeap i=s.scalarHeap i) ∧
 (∀r,6160 ≤ r → r ≤ 6179 → u.natReg r=s.natReg r) ∧
 (∀r,6400 ≤ r → u.natReg r=s.natReg r) ∧
 (∀i,slab constants n ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i) ∧ UniformCacheLowRetention.Frame n s u:=by
 let B:=envelope constants n
 have ambient:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*W.z n ≤ B at ambient
 have zpositive:0<W.z n:=by change 0<(n+2)^19;positivity
 have lowEnd:W.lowRow n+7 ≤ B:=by
  change W.z n+7 ≤ B
  omega
 have highEnd:W.lowRow n+7 ≤ slab constants n:=by
  have low:=UniformJointCacheWorkspace.below_cache constants n
  change 2000*W.z n ≤ slab constants n at low
  change W.z n+7 ≤ slab constants n
  omega
 obtain ⟨a,setup,ap,lowRow,stored,args,nextArgs,falseArgs,slot,outside,sh,sr,out,roots,kept⟩:=
  UniformLocalStoredRequestBootstrap.execution j D q x s bank axis pointer source apart db lowEnd (by omega) pc wb
 have placedSetup:=UniformBoundedAssembly.boundedExecution_placed setup_code
  (by rw [UniformLocalStoredRequestBootstrap.program_length];omega) (by omega) setup
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedSetup
 let start:=setPC a 0
 have bw:=changePC_bound B a 0 setup.final_bound (by omega)
 have prefixOld:=UniformLocalStoredRequestBootstrap.prefix_frame setup
  (UniformJointCacheWorkspace.retained hn).2.2.1 outside sh out roots
 have startFrame:UniformSeedRankCrossPreparation.PreservedFrame n a start:=
  ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
 have allFrame:=prefixOld.trans startFrame
 have vc:=UniformLocalRectangleCoefficientMachine.conjugate_retained
  (s:=s) (u:=start) conjugate (fun i _=>congrFun sh i)
  (fun i hi=>outside i (Or.inl (lt_of_lt_of_le hi (UniformJointCacheWorkspace.retained hn).2.2.2)))
 have realEntry:=UniformJointCacheWorkspace.entry constants hn j q g x start args nextArgs slot lowRow
  (allFrame.protected.metadata metadata) (allFrame.retained seed) vc (allFrame.protected.operands operands)
 have driverStart:=UniformLocalStoredRequestBootstrap.driver_retained (u:=start) driver highEnd kept outside
 have falseStart:UniformLocalDisabledHeightMachine.Args (W.falseRows n) (W.falseColors n)
  (W.falsePalette n) (W.falseDirectory n) start:=
  ⟨falseArgs.rows,falseArgs.colors,falseArgs.palette,falseArgs.directory⟩
 let layout:=UniformLocalStoredRequestGeometry.phase_layout constants hn j q g
 have endShapes:=UniformLocalStoredRequestGeometry.phase_ends constants hn j q g
 obtain ⟨last,nt,cache,cost,lp,cached,outputs,rootOrders,ss,prior,control,ret,conj,metadataFinal,ops,driverNat,highNat,suffix,cacheLow⟩:=
  UniformLocalRectangleCachePreparation.PriorRetention.execution_low hn j (W.lowRow n) q (W.original n q)
   (W.work n) (W.conjugate n) (W.control n) (W.falseRows n) (W.falseColors n) (W.falsePalette n)
   (W.falseDirectory n) B (slab constants n) (W.inverse n) c x start layout realEntry falseStart
   (UniformJointCacheWorkspace.false_layout hn j q g)
   ((UniformJointCacheWorkspace.false_budget hn j q g).trans ambient)
   (UniformLocalStoredRequestGeometry.true_before hn j q g)
   (UniformLocalStoredRequestGeometry.slots_before hn j q g)
   binding driverStart endShapes ha he geometry prefixPlacement workspaces (by omega) total scalar natural (UniformCacheLowRetention.workspace_below n j q) contextLow rfl bw
 have placedCache:=UniformBoundedAssembly.boundedExecution_placed cache_code
  (by rw [UniformLocalRectangleCachePreparation.program_length];omega) (by omega) cache
 have ceq:placed 47 start=setPC a 47:=by cases a;rfl
 rw [ceq] at placedCache
 let u:=setPC last 3737
 have finishFrame:UniformSeedRankCrossPreparation.PreservedFrame n last u:=
  ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
 have finalConj:=UniformLocalRectangleCoefficientMachine.conjugate_retained
  (s:=last) (u:=u) conj (fun _ _=>rfl) (fun _ _=>rfl)
 have stop:BoundedExecution program n x B u 1 u:=.halt placedCache.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,90+nt+1,?_,by omega,rfl,?_,control.withPC 3737,finishFrame.retained ret,finalConj,
  finishFrame.protected.metadata metadataFinal,finishFrame.protected.operands ops,
  outputs.trans out,rootOrders.trans roots,?_,?_,?_,?_,?_,?_⟩
 · exact placedSetup.executes (placedCache.executes stop)
 · intro k hk;exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 · intro i hi before;exact (prior i hi before).trans (outside i (Or.inr (highEnd.trans hi)))
 · intro i hi loc hm hb;exact (ss i hi loc hm hb).trans (congrFun sh i)
 · intro r lo hi;exact (driverNat r lo hi).trans (kept r (by omega) (by omega))
 · intro r hr;exact (highNat r hr).trans (kept r (by omega) (by omega))
 · intro i hi afterCache;exact (suffix i hi afterCache).trans (outside i (Or.inr (highEnd.trans hi)))
 · exact ⟨fun i hi=>(cacheLow.nat i hi).trans (outside i (Or.inl hi)),
     fun i hi=>(cacheLow.scalar i hi).trans (congrFun sh i)⟩
end
end ExactFourierCircuits.UniformLocalStoredRectanglePreparation
