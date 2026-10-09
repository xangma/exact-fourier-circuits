import UniformLocalCacheSlotExecutionLoop

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine.PriorRetention
open UniformMachine UniformTensorMonomialMachine UniformLocalFactorDispatchMachine
noncomputable section

/-- One genuine cursor iteration: branch,74,1156,80,nine updates,back-edge.
The slot and selected enabled/disabled bank come from the physical2308 output. -/
theorem iteration {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I) (H:ℕ)
 (workspaces:∀j (hj:j < 352*c.height.K+330) slot (witness:SlotWitness c.height.K j slot),
  natEnd (Cursor.shifted c j) q slot (geometry.layout j hj slot witness) (geometry.broadcast j hj) ha he I ≤ H)
 (j:ℕ) (hj:j < 352*c.height.K+330)
 (x:Fin n → ℂ) (s:State) (control:Cursor.Control c j s)
 (inputs:Inputs c q ha he I bank s)
 (cached:∀k,k < j → Cached (B:=B) c q ha he bank geometry.positive k s)
 (code:1336 ≤ B) (total:352*c.height.K+330 ≤ B) (pc:s.pc=14) (wb:WordBound B s):∃u ticks,
 BoundedRuns program n x B s ticks u ∧ ticks ≤ bodyBudget c q+11 ∧u.pc=14 ∧
 Cursor.Control c (j+1) u ∧Inputs c q ha he I bank u ∧
 (∀k,k < j+1 → Cached (B:=B) c q ha he bank geometry.positive k u) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀i, i < c.borrowed → u.natHeap i=s.natHeap i) ∧
 (∀i, (i < c.pool ∨ c.pool+9*c.ambient*(j+1) ≤ i) → i≠c.mu → i≠c.conjugateMu →
  u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,H ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 (∀i,H ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i):=by
 have first:=enter (x:=x) control hj pc wb code
 let a:=setPC s 15
 have ai:=inputs.withPC 15
 obtain ⟨slot,witness,record⟩:=ai.slot hj
 let l:=geometry.layout j hj slot witness
 let bl:=geometry.broadcast j hj
 have cacheBefore:c.borrowed ≤ (Cursor.shifted c j).cachePermutation:=by
  change c.borrowed ≤ c.cachePermutation+(3*c.ambient+11)*j
  have:=geometry.inputs.cache;omega
 obtain ⟨b,bt,body,cost,bp,post⟩:=slot_execution (Cursor.shifted c j) q slot l bl ha he I
  (geometry.inverse j hj slot witness) bank x a (control.withPC 15).args ai.rectangle record
  (ai.processed j slot) ai.sources ai.constants geometry.positive ai.inverse geometry.rectangle
  (by have:=geometry.slots j hj;omega) (geometry.rows j hj slot witness)
  (by have:=geometry.permutation;change c.cachePermutation+(3*c.ambient+11)*j+c.ambient ≤ c.cacheWidths+(3*c.ambient+11)*j;omega)
  (by have:=geometry.widths;change c.cacheWidths+(3*c.ambient+11)*j+c.ambient ≤ c.cacheMarkers+(3*c.ambient+11)*j;omega)
  (by have:=geometry.markers;change c.cacheMarkers+(3*c.ambient+11)*j+c.ambient ≤ c.cacheAxis+(3*c.ambient+11)*j;omega)
  (by have:=geometry.axis;change c.cacheAxis+(3*c.ambient+11)*j+4 ≤ c.cacheDirectory+(3*c.ambient+11)*j;omega)
  (geometry.directories j hj) code rfl first.final_bound
 have bc:Cursor.Control c j b:=(control.withPC 15).transport post.driver
 have bi:Inputs c q ha he I bank b:=ai.transport_banks geometry.inputs
  (fun i hi=>post.natPrefix i hi (lt_of_lt_of_le hi cacheBefore)) post.sources post.constants post.inverseHeader
 have all:∀k,k < j+1 → Cached (B:=B) c q ha he bank geometry.positive k b:=by
  intro k hk
  by_cases earlier:k < j
  · have prior:Cached (B:=B) c q ha he bank geometry.positive k a:=
     (cached k earlier).heaps (cache_shift geometry.cache k) rfl rfl
    exact Cached.afterStored prior
     earlier geometry.cache geometry.mu geometry.conjugateMu (geometry.natEnd j hj slot witness) post
  · have eq:k=j:=by omega
    subst k
    exact ⟨slot,witness,l,bl,post.contents⟩
 have endpoints:=geometry.endpoints (j+1) (by omega)
 obtain ⟨u,last,up,uc,unh,ush,usr,uout,uroot,ui⟩:=advance_execution c x b bc bp body.final_bound code
  endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2.1 endpoints.2.2.2.2.1
  endpoints.2.2.2.2.2.1 endpoints.2.2.2.2.2.2.1 endpoints.2.2.2.2.2.2.2 (by omega)
 refine ⟨u,1+bt+10,?_,?_,up,uc,bi.transport geometry.inputs (fun i _=>congrFun unh i) ush ui,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (first.trans body).trans last
 · have cheap:=body_cost (Cursor.shifted c j) q slot l bl ha he
   change runtimeBudget (Cursor.shifted c j) q slot l bl ha he+21*c.ambient+116 ≤ bodyBudget c q at cheap
   change bt ≤ runtimeBudget (Cursor.shifted c j) q slot l bl ha he+21*c.ambient+116 at cost
   omega
 · intro k hk;exact (all k hk).heaps (cache_shift geometry.cache k) unh ush
 · exact uout.trans post.outputs
 · exact uroot.trans post.roots

 · intro i low
   exact (congrFun unh i).trans (post.natPrefix i low (lt_of_lt_of_le low cacheBefore))
 · intro i outside hm hb
   have current:(i < (Cursor.shifted c j).pool ∨ (Cursor.shifted c j).pool+9*(Cursor.shifted c j).ambient ≤ i):=by
    simp only [Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters,Nat.mul_add,Nat.mul_one] at *
    omega
   exact (congrFun ush i).trans (post.scalarOutside i current hm hb)

 · intro i hi before
   apply (congrFun unh i).trans
   apply post.cached i (le_trans (workspaces j hj slot witness) hi)
   change i<c.cachePermutation+(3*c.ambient+11)*j
   omega
 · intro i hi afterCache
   apply (congrFun unh i).trans
   apply post.natHigh i (le_trans (workspaces j hj slot witness) hi)
   have directory:=geometry.cache.directoryHigh
   have order:=Nat.mul_le_mul_left (3*c.ambient+11) (show j+1 ≤ 352*c.height.K+330 by omega)
   change c.cacheDirectory+(3*c.ambient+11)*j+7 ≤ i
   calc
    _ ≤ c.cachePermutation+(3*c.ambient+11)*(j+1) := by
     rw[Nat.mul_add,Nat.mul_one];omega
    _ ≤ c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) := Nat.add_le_add_left order _
    _ ≤ i := afterCache

/-- The actual fixed loop visits every physically generated six-phase ordinal.
All source banks, measured row counts, factor pools and cached partition rows
are derived inside the loop. The remaining premises are ordinary geometry. -/
theorem loop {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I) (H:ℕ)
 (workspaces:∀j (hj:j < 352*c.height.K+330) slot (witness:SlotWitness c.height.K j slot),
  natEnd (Cursor.shifted c j) q slot (geometry.layout j hj slot witness) (geometry.broadcast j hj) ha he I ≤ H)
 (f j:ℕ) (remaining:j+f=352*c.height.K+330)
 (x:Fin n → ℂ) (s:State) (control:Cursor.Control c j s)
 (inputs:Inputs c q ha he I bank s)
 (cached:∀k,k < j → Cached (B:=B) c q ha he bank geometry.positive k s)
 (code:1336 ≤ B) (total:352*c.height.K+330 ≤ B) (pc:s.pc=14) (wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ f*(bodyBudget c q+11)+2 ∧u.pc=1335 ∧
 Cursor.Control c (352*c.height.K+330) u ∧Inputs c q ha he I bank u ∧
 (∀k,k < 352*c.height.K+330 → Cached (B:=B) c q ha he bank geometry.positive k u) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀i, i < c.borrowed → u.natHeap i=s.natHeap i) ∧
 (∀i, (i < c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) → i≠c.mu → i≠c.conjugateMu →
  u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,H ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 (∀i,H ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i):=by
 induction f generalizing j s with
 | zero=>
  have eq:j=352*c.height.K+330:=by omega
  subst j
  refine ⟨setPC s 1335,2,stop control pc wb code,by simp,rfl,control.withPC 1335,
   inputs.withPC 1335,?_,rfl,rfl,by intros;rfl,by intros;rfl,by intros;rfl,by intros;rfl⟩
  intro k hk
  exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 | succ f ih=>
  have more:j < 352*c.height.K+330:=by omega
  obtain ⟨a,t,first,cheap,ap,ac,ai,ca,out,roots,low,scalar,prior,high⟩:=iteration c q ha he I bank geometry H workspaces j more x s
   control inputs cached code total pc wb
  obtain ⟨u,ticks,tail,cost,up,uc,ui,cu,uout,uroot,ulo,ush,ukeep,uhigh⟩:=ih (j+1) (by omega) a ac ai ca ap first.final_bound
  refine ⟨u,t+ticks,first.executes tail,?_,up,uc,ui,cu,uout.trans out,uroot.trans roots,?_,?_,?_,?_⟩
  · rw [Nat.add_mul,Nat.one_mul];omega
  · intro i hi;exact (ulo i hi).trans (low i hi)
  · intro i outside hm hb
    have mul:=Nat.mul_le_mul_left (9*c.ambient) (show j+1 ≤ 352*c.height.K+330 by omega)
    exact (ush i outside hm hb).trans (scalar i (by omega) hm hb)
  · intro i hi before;exact (ukeep i hi before).trans (prior i hi before)
  · intro i hi afterCache;exact (uhigh i hi afterCache).trans (high i hi afterCache)

/-- Initialization, every cache slot and the final halt are one continuous
execution of a1336-instruction program independent of all runtime dimensions.
This is a rectangle cache preparer, not a full Fourier transform executor. -/
theorem execution {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I) (H:ℕ)
 (workspaces:∀j (hj:j < 352*c.height.K+330) slot (witness:SlotWitness c.height.K j slot),
  natEnd (Cursor.shifted c j) q slot (geometry.layout j hj slot witness) (geometry.broadcast j hj) ha he I ≤ H)
 (x:Fin n → ℂ) (s:State)
 (args:UniformLocalCacheSlotHeaderMachine.Args c s) (inputs:Inputs c q ha he I bank s)
 (code:1336 ≤ B) (total:352*c.height.K+330 ≤ B) (scalar:9*c.ambient ≤ B)
 (natural:3*c.ambient+11 ≤ B) (pc:s.pc=0) (wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ (352*c.height.K+330)*(bodyBudget c q+11)+16 ∧u.pc=1335 ∧
 Cursor.Control c (352*c.height.K+330) u ∧Inputs c q ha he I bank u ∧
 (∀k,k < 352*c.height.K+330 → Cached (B:=B) c q ha he bank geometry.positive k u) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀i, i < c.borrowed → u.natHeap i=s.natHeap i) ∧
 (∀i, (i < c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) → i≠c.mu → i≠c.conjugateMu →
  u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,H ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 (∀i,H ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i):=by
 obtain ⟨a,boot,ap,control,nh,sh,sr,out,roots,inverse⟩:=boot_execution c x s args pc wb code total scalar natural
 have ready:=inputs.transport geometry.inputs (fun i _=>congrFun nh i) sh inverse
 obtain ⟨u,t,tail,cost,up,uc,ui,cached,uout,uroot,ulo,ush,prior,high⟩:=loop c q ha he I bank geometry H workspaces
  (352*c.height.K+330) 0 (by omega) x a control ready (by intro k hk;omega) code total ap boot.final_bound
 refine ⟨u,14+t,boot.executes tail,by omega,up,uc,ui,cached,uout.trans out,uroot.trans roots,?_,?_,?_,?_⟩
 · intro i hi;exact (ulo i hi).trans (congrFun nh i)
 · intro i outside hm hb;exact (ush i outside hm hb).trans (congrFun sh i)
 · intro i hi before;exact (prior i hi before).trans (congrFun nh i)
 · intro i hi afterCache;exact (high i hi afterCache).trans (congrFun nh i)

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine.PriorRetention
