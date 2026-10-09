import UniformGlobalCalendarDispatchRows

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformGlobalMatchingScaleMachine (Phase)
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs)
noncomputable section

lemma Header.atPC {A N r O T used phaseBank j : ℕ} {s : State}
 (h : Header A N r O T used phaseBank j s) (pc : ℕ) :
 Header A N r O T used phaseBank j {s with pc:=pc}:=
 ⟨h.selected,h.count,h.radix,h.pool,h.rows,h.usedReg,h.phaseBankReg,h.index,h.one,h.two,h.zero⟩
lemma Loaded.atPC {r : ℕ} {d : Descriptor} {s : State} (h : Loaded r d s) (pc : ℕ) :
 Loaded r d {s with pc:=pc}:=
 ⟨h.address,h.elapsed,h.pool,h.widthCount,h.permutation,h.kind,h.pairs⟩

lemma control {n B target : ℕ} (x : Fin n→ℂ) (s : State) (wb : WordBound B s)
 (fit : target ≤ B) (stepEq : step program n x s=.running {s with pc:=target}) :
 BoundedRuns program n x B s 1 {s with pc:=target}:=
 .next wb stepEq (.refl (changePC_bound B s target wb fit))

/-- The actual positive loop test and17-op reader consume the selected-bank
address/elapsed pair and genuine cache ABI. -/
theorem prefix_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (h : Header A N r O T used phaseBank j s)
 (selected : Selected A j d s) (stored : Stored d s) (pc : s.pc=10) (wb : WordBound B s)
 (code : 281 ≤ B) (index : j<N) (selectionFit : A+2*N ≤ B) (entryFit : d.address+7 ≤ B) :
 ∃u, BoundedRuns program n x B s 18 u∧u.pc=28∧Header A N r O T used phaseBank j u∧Loaded r d u∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 let a : State:={s with pc:=11}
 have branch : BoundedRuns program n x B s 1 a:=control x s wb (by omega)
  (by simp [step,pc,code_10,h.index,h.count,index])
 have reader:=readEntry_execution x a d (h.atPC 11) selected stored rfl branch.final_bound code index selectionFit entryFit
 let u:=applyBlock readEntry a
 refine ⟨u,branch.trans reader,?_,readEntry_header (h.atPC 11),readEntry_loaded d (h.atPC 11) selected stored,rfl,rfl,rfl,rfl⟩
 rw [applyBlock_pc];rfl

/-- Only genuine ordinary28 phases, direct one-tick scales and genuine bare
one-tick C events are accepted by the physical kind decoder. -/
def Decoded (d : Descriptor) (p : Phase) : Prop :=
 (∃h:d.elapsed<28,d.kind=0∧UniformGlobalMatchingScaleMachine.phases.get
  ⟨d.elapsed,by rw [UniformGlobalMatchingScaleMachine.phases_length];exact h⟩=p)∨
 (d.kind=1∧p=.diagonal ⟨0,by omega⟩)∨(d.kind=2∧p=.kernel)

def PhaseEntry (p : Phase) (s : State) : Prop := match p with
 | .diagonal lane=>s.pc=36∧s.natReg 6765=lane.val
 | .kernel=>s.pc=42

def scaleLiteral : List Op:=[.literal 6765 0]
lemma scaleLiteral_code : BlockAt scaleLiteral program 34:=by
 intro i hi
 have eq:i=0:=by change i<1 at hi;omega
 subst i
 exact code_34


/-- Actual kind/phase branching reaches the scalar merger or ordered-row
printer. Ordinary phases are read from the internally printed decoder. -/
theorem route_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (p : Phase) (h : Header A N r O T used phaseBank j s) (loaded : Loaded r d s)
 (decoded : Decoded d p) (pc : s.pc=28) (wb : WordBound B s) (code : 281 ≤ B)
 (printed : UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words s)
 (phaseFit : phaseBank+56 ≤ B) :
 ∃u time, BoundedRuns program n x B s time u∧time ≤ 13∧PhaseEntry p u∧
 Header A N r O T used phaseBank j u∧Loaded r d u∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 rcases decoded with ordinary|scale|kernel
 · rcases ordinary with ⟨elapsed,kind,phase⟩
   let a : State:={s with pc:=30}
   have branch : BoundedRuns program n x B s 1 a:=control x s wb (by omega)
    (by simp [step,pc,code_28,loaded.kind,h.one,kind])
   obtain ⟨u,run,up,uh,ul,k,l,nh,sh,roots,outputs⟩:=phase_execution x a d (h.atPC 30) (loaded.atPC 30) elapsed rfl
    branch.final_bound code printed phaseFit
   rw [phase] at k l
   cases p with
   | diagonal lane=>
    have last : BoundedRuns program n x B u 1 {u with pc:=36}:=control x u run.final_bound (by omega)
     (by simp [step,up,code_33,k,UniformGlobalCalendarPhaseDirectory.kind,uh.one])
    exact ⟨{u with pc:=36},13,(branch.trans run).trans last,le_rfl,⟨rfl,l⟩,uh.atPC 36,ul.atPC 36,nh,sh,roots,outputs⟩
   | kernel=>
    have last : BoundedRuns program n x B u 1 {u with pc:=42}:=control x u run.final_bound (by omega)
     (by simp [step,up,code_33,k,UniformGlobalCalendarPhaseDirectory.kind,uh.one])
    exact ⟨{u with pc:=42},13,(branch.trans run).trans last,le_rfl,rfl,uh.atPC 42,ul.atPC 42,nh,sh,roots,outputs⟩
 · rcases scale with ⟨kind,rfl⟩
   let a : State:={s with pc:=29}
   have first : BoundedRuns program n x B s 1 a:=control x s wb (by omega)
    (by simp [step,pc,code_28,loaded.kind,h.one,kind])
   let b : State:={s with pc:=34}
   have second : BoundedRuns program n x B a 1 b:=control x a first.final_bound (by omega)
    (by simp [step,a,code_29,loaded.kind,h.two,kind])
   let c:=applyBlock scaleLiteral b
   have literal : BoundedRuns program n x B b 1 c:=block_runs scaleLiteral program 34 n B x b scaleLiteral_code rfl
    second.final_bound (by change 35 ≤ B;omega)
    (by simp [scaleLiteral,readable,Op.readable]) (by simp [scaleLiteral,peak,Op.peak])
   have cp : c.pc=35:=by rw [applyBlock_pc];rfl
   have last : BoundedRuns program n x B c 1 {c with pc:=36}:=control x c literal.final_bound (by omega)
    (by simp [step,cp,code_35])
   refine ⟨{c with pc:=36},4,((first.trans second).trans literal).trans last,by omega,?_,?_,?_,rfl,rfl,rfl,rfl⟩
   · exact ⟨rfl,by simp [c,scaleLiteral,applyBlock,Op.apply,writeNat,next]⟩
   · exact h.transfer (by intro z lo hi;simp (disch := omega) [c,scaleLiteral,b,applyBlock,Op.apply,writeNat,next])
   · constructor <;> simp [c,scaleLiteral,b,applyBlock,Op.apply,writeNat,next,loaded.address,loaded.elapsed,loaded.pool,
      loaded.widthCount,loaded.permutation,loaded.kind,loaded.pairs]
 · rcases kernel with ⟨kind,rfl⟩
   let a : State:={s with pc:=29}
   have first : BoundedRuns program n x B s 1 a:=control x s wb (by omega)
    (by simp [step,pc,code_28,loaded.kind,h.one,kind])
   have last : BoundedRuns program n x B a 1 {s with pc:=42}:=control x a first.final_bound (by omega)
    (by simp [step,a,code_29,loaded.kind,h.two,kind])
   exact ⟨{s with pc:=42},2,first.trans last,by omega,rfl,h.atPC 42,loaded.atPC 42,rfl,rfl,rfl,rfl⟩

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
