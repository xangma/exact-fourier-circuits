import UniformLocalStoredRequestResult
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl UniformLocalRequestGeometry
open UniformLocalCacheSlotConductorMachine
noncomputable section

/-- The real stored-row3738 producer consumes only the physical row/time
source and retained startup banks. All six phases and cached factors arise
inside this execution. -/
theorem body {constants n j qs R T}(hn:0 < n)
 (g:UniformLocalRequestGeometry.Geometry constants n j qs R T)(x:Fin n → ℂ)
 (i:ℕ)(hi:i < qs.length)(s:State)(ready:Ready constants n j qs R T g x i s)
 (axis:s.natReg 4200=j.val)(code:3776 ≤ envelope constants n)
 (pc:s.pc=24)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedRuns program n x (envelope constants n) s ticks u ∧
 ticks ≤ bodyCharge n j (qs[i]'hi).row ∧u.pc=3762 ∧BodyResult g x i hi s u:=by
 let start:=setPC s 0
 have sr:=ready.withPC 0
 have bounds:=changePC_bound (envelope constants n) s 0 wb (by omega)
 have driver:UniformLocalRectangleCacheBindings.Driver j (controller constants n j qs i)
  (UniformJointCacheWorkspace.inverse n) (slab constants n) start:=by
  rw[controller,requestAt_eq qs i hi]
  exact UniformLocalRequestDriver.driver constants j (qs[i]'hi).row (slotPrefix n qs i)
   (qs[i]'hi).time (R+7*i) (T+i) i qs.length (slab constants n) start sr.control.bank
   (by simpa only[controller,requestAt_eq qs i hi] using sr.control.live) sr.control.selected
   (by have:=g.timesHigh;omega) (sr.source.times i hi)
 have small:=small_budgets constants hn j
 have apart:UniformJointCacheWorkspace.lowRow n+7 ≤ R+7*i:=
  (low_before_cache constants n).1.trans (by have:=g.rowsHigh;omega)
 obtain ⟨last,t,run,cheap,lp,cached,measured,ret,conj,metadataFinal,ops,out,roots,low,scalar,lowNat,highNat,high⟩:=
  UniformLocalStoredRectanglePreparation.execution constants hn j (R+7*i) (qs[i]'hi).row
   (g.workspace i hi) (controller constants n j qs i) (aBound constants n j qs i hi)
   (eBound constants n j qs i hi) (g.slots i hi) (g.binding i hi) (g.prefixes hn i hi)
   (g.workspaces hn i hi) x start sr.control.bank axis sr.control.live.pointer (sr.source.rows i hi)
   sr.metadata sr.original sr.conjugate sr.operands driver apart
   (by have:=g.rowsBound;omega) (by omega) (g.total i hi) small.1 small.2 rfl bounds
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed cache_code
  (by rw[UniformLocalStoredRectanglePreparation.program_length];omega) (by omega) run
 rw[UniformSeedRankCrossPreparation.placed_zero s 24 pc] at placedRun
 let u:=setPC last 3762
 have nc:Control constants n j qs R T i u:=sr.control.retained lowNat highNat
 have ns:Source R T qs u:=g.source_retained i hi sr.source low high
 have current:Complete constants n j qs R T g i hi u:=by
  intro k hk
  exact (cached k (by rw[controller_count constants n j qs i hi];exact hk)).heaps
   (cache_shift (g.slots i hi).cache k) rfl rfl
 have prior:∀k (hk:k < qs.length),k < i → Complete constants n j qs R T g k hk u:=by
  intro k hk old
  exact Complete.retained g hk hi old (sr.completed k hk old) low (scalar_prior g i hi scalar)
 have finalSeed:Retained n (axisCount n) u:=by
  exact (show UniformSeedRankCrossPreparation.PreservedFrame n last u from
   ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩).retained ret
 have finalConj:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=
  UniformLocalRectangleCoefficientMachine.conjugate_retained conj (fun _ _=>rfl) (fun _ _=>rfl)
 have finalProtected:UniformAllAxisSeedPreparation.ProtectedFrame n last u:=
  (show UniformSeedRankCrossPreparation.PreservedFrame n last u from
   ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩).protected
 refine ⟨u,t,placedRun,?_,rfl,?_⟩
 · simpa only[bodyCharge,bodyBudget,controller,requestAt_eq qs i hi,
    UniformCanonicalCacheSlotGeometry.context,slotCount,UniformSeedHeightPreparation.Config.height,Nat.add_assoc,
    show (304:ℕ)+11=315 from rfl] using cheap
 · refine ⟨⟨nc,ns,finalSeed,finalConj,finalProtected.metadata metadataFinal,finalProtected.operands ops,prior⟩,
    current,?_,out,roots,low,high,scalar,lowNat,highNat⟩
   simpa only[controller_count constants n j qs i hi] using measured.withPC 3762

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
