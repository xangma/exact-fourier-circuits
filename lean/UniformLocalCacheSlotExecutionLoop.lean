import UniformLocalCacheSlotIteration

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformTensorMonomialMachine
noncomputable section

/-- The actual fixed loop visits every physically generated six-phase ordinal.
All source banks, measured row counts, factor pools and cached partition rows
are derived inside the loop. The remaining premises are ordinary geometry. -/
theorem loop {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I) (f j:ℕ) (remaining:j+f=352*c.height.K+330)
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
  u.scalarHeap i=s.scalarHeap i):=by
 induction f generalizing j s with
 | zero=>
  have eq:j=352*c.height.K+330:=by omega
  subst j
  refine ⟨setPC s 1335,2,stop control pc wb code,by simp,rfl,control.withPC 1335,
   inputs.withPC 1335,?_,rfl,rfl,by intros;rfl,by intros;rfl⟩
  intro k hk
  exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 | succ f ih=>
  have more:j < 352*c.height.K+330:=by omega
  obtain ⟨a,t,first,cheap,ap,ac,ai,ca,out,roots,low,scalar⟩:=iteration c q ha he I bank geometry j more x s
   control inputs cached code total pc wb
  obtain ⟨u,ticks,tail,cost,up,uc,ui,cu,uout,uroot,ulo,ush⟩:=ih (j+1) (by omega) a ac ai ca ap first.final_bound
  refine ⟨u,t+ticks,first.executes tail,?_,up,uc,ui,cu,uout.trans out,uroot.trans roots,?_,?_⟩
  · rw [Nat.add_mul,Nat.one_mul];omega
  · intro i hi;exact (ulo i hi).trans (low i hi)
  · intro i outside hm hb
    have mul:=Nat.mul_le_mul_left (9*c.ambient) (show j+1 ≤ 352*c.height.K+330 by omega)
    exact (ush i outside hm hb).trans (scalar i (by omega) hm hb)

/-- Initialization, every cache slot and the final halt are one continuous
execution of a1336-instruction program independent of all runtime dimensions.
This is a rectangle cache preparer, not a full Fourier transform executor. -/
theorem execution {B n:ℕ} (c:Header.Parameters) (q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I) (x:Fin n → ℂ) (s:State)
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
  u.scalarHeap i=s.scalarHeap i):=by
 obtain ⟨a,boot,ap,control,nh,sh,sr,out,roots,inverse⟩:=boot_execution c x s args pc wb code total scalar natural
 have ready:=inputs.transport geometry.inputs (fun i _=>congrFun nh i) sh inverse
 obtain ⟨u,t,tail,cost,up,uc,ui,cached,uout,uroot,ulo,ush⟩:=loop c q ha he I bank geometry
  (352*c.height.K+330) 0 (by omega) x a control ready (by intro k hk;omega) code total ap boot.final_bound
 refine ⟨u,14+t,boot.executes tail,by omega,up,uc,ui,cached,uout.trans out,uroot.trans roots,?_,?_⟩
 · intro i hi;exact (ulo i hi).trans (congrFun nh i)
 · intro i outside hm hb;exact (ush i outside hm hb).trans (congrFun sh i)

end
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
