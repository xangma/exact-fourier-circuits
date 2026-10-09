import UniformGlobalCalendarDispatchReader
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs)
noncomputable section

structure Inputs (A N r O T phaseBank : ℕ) (s : State) : Prop where
 selected : s.natReg 6766=A
 count : s.natReg 6767=N
 radix : s.natReg 6768=r
 pool : s.natReg 6769=O
 rows : s.natReg 6770=T
 phaseBankReg : s.natReg 6772=phaseBank

lemma Header.transfer {A N r O T used phaseBank j : ℕ} {s u : State}
 (h : Header A N r O T used phaseBank j s)
 (keep : ∀ z, 6766 ≤ z → z ≤ 6776 → u.natReg z=s.natReg z) :
 Header A N r O T used phaseBank j u := by
 constructor
 · exact (keep _ (by omega) (by omega)).trans h.selected
 · exact (keep _ (by omega) (by omega)).trans h.count
 · exact (keep _ (by omega) (by omega)).trans h.radix
 · exact (keep _ (by omega) (by omega)).trans h.pool
 · exact (keep _ (by omega) (by omega)).trans h.rows
 · exact (keep _ (by omega) (by omega)).trans h.usedReg
 · exact (keep _ (by omega) (by omega)).trans h.phaseBankReg
 · exact (keep _ (by omega) (by omega)).trans h.index
 · exact (keep _ (by omega) (by omega)).trans h.one
 · exact (keep _ (by omega) (by omega)).trans h.two
 · exact (keep _ (by omega) (by omega)).trans h.zero


lemma boot_header {A N r O T phaseBank : ℕ} {s : State} (h : Inputs A N r O T phaseBank s) :
 Header A N r O T 0 phaseBank 0 (applyBlock boot s) := by
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.selected,h.count,h.radix,h.pool,h.rows,h.phaseBankReg]

lemma code_6 : program[6]?=some (.jump 52) := rfl
lemma code_9 : program[9]?=some (.jump 224) := rfl
lemma initSetup_code : BlockAt initSetup program 7 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl

/-- The literal281 dispatcher prints its own real phase directory and prepares
all9r fresh factor cells. Both helpers are charged inside this very program. -/
theorem boot_execution {n A N r O T phaseBank B : ℕ} (x : Fin n→ℂ) (s : State)
 (h : Inputs A N r O T phaseBank s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 281 ≤ B) (phaseFit : phaseBank+56 ≤ B) (poolFit : O+9*r ≤ B) :
 ∃u, BoundedRuns program n x B s (45*r+189) u ∧ u.pc=10 ∧
 Header A N r O T 0 phaseBank 0 u ∧
 UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words u ∧
 UniformGlobalScalePoolMachine.Prefix O (9*r) u ∧
 (∀z,z<phaseBank → u.natHeap z=s.natHeap z) ∧
 (∀z,z<O ∨ O+9*r ≤ z → u.scalarHeap z=s.scalarHeap z) ∧
 u.rootOrders=s.rootOrders ∧u.outputs=s.outputs := by
 let b:=applyBlock boot s
 have bh : Header A N r O T 0 phaseBank 0 b:=boot_header h
 have br : BoundedRuns program n x B s 6 b:=block_runs boot program 0 n B x s boot_code pc wb
  (by change 6 ≤ B;omega)
  (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.phaseBankReg];omega)
 have bp : b.pc=6:=by rw [applyBlock_pc,pc];rfl
 have j1 : step program n x b=.running {b with pc:=52}:=by simp [step,bp,code_6]
 have phs : WordBound B {b with pc:=0}:=changePC_bound B b 0 br.final_bound (by omega)
 obtain ⟨p,pr,printed,ph,frames,_ptr⟩:=UniformGlobalCalendarPhaseDirectory.execution phaseBank B n x
  {b with pc:=0} (by simp [b,boot,applyBlock,Op.apply,writeNat,next,h.phaseBankReg]) rfl phs phaseFit (by omega)
 have placedP:=UniformBoundedAssembly.boundedExecution_placed phasePrinter_code
  (by rw [phasePrinter_length];omega) (by omega) pr
 change BoundedRuns program n x B {b with pc:=52} 172 {p with pc:=7} at placedP
 have first : BoundedRuns program n x B s 179 {p with pc:=7}:=
  br.trans (.next br.final_bound j1 placedP)
 have hp : Header A N r O T 0 phaseBank 0 p:=bh.transfer (by
  intro z lo hi;exact frames.natReg z (by omega) (by omega) (by omega) (by omega))
 let ready:=applyBlock initSetup {p with pc:=7}
 have setup : BoundedRuns program n x B {p with pc:=7} 2 ready:=block_runs initSetup program 7 n B x
  {p with pc:=7} initSetup_code rfl first.final_bound (by change 9 ≤ B;omega)
  (by simp [initSetup,readable,Op.readable])
  (by simp [initSetup,peak,Op.peak,Op.apply,writeNat,next,hp.pool,hp.radix,hp.one];omega)
 have rh : Header A N r O T 0 phaseBank 0 ready:=hp.transfer (by
  intro z lo hi;simp (disch := omega) [ready,initSetup,applyBlock,Op.apply,writeNat,next])
 have rp : ready.pc=9:=by rw [applyBlock_pc];rfl
 have j2 : step program n x ready=.running {ready with pc:=224}:=by simp [step,rp,code_9]
 have ihs : WordBound B {ready with pc:=0}:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨u,ir,_ip,pool,sf,ff⟩:=UniformGlobalScalePoolMachine.execution O r n B x {ready with pc:=0}
  (by simp [ready,initSetup,applyBlock,Op.apply,writeNat,next,hp.pool,hp.one])
  (by simp [ready,initSetup,applyBlock,Op.apply,writeNat,next,hp.radix,hp.one]) poolFit (by omega) rfl ihs
 have placedI:=UniformBoundedAssembly.boundedExecution_placed init_code
  (by rw [UniformGlobalScalePoolMachine.program_length];omega) (by omega) ir
 change BoundedRuns program n x B {ready with pc:=224} (45*r+7) {u with pc:=10} at placedI
 have last:=setup.trans (.next setup.final_bound j2 placedI)
 have uh : Header A N r O T 0 phaseBank 0 {u with pc:=10}:=rh.transfer (by
  intro z lo hi;exact ff.natReg z (by omega) (by omega) (by omega) (by omega))
 refine ⟨{u with pc:=10},?_,rfl,uh,?_,pool,?_,?_,?_,?_⟩
 · convert first.trans last using 1;omega
 · intro j hj
   exact (congrFun ff.natHeap _).trans (printed j hj)
 · intro z hz
   exact (congrFun ff.natHeap z).trans ((ph z (Or.inl hz)).trans rfl)
 · intro z outside
   exact (sf z outside).trans ((congrFun frames.scalarHeap z).trans rfl)
 · exact ff.roots.trans (frames.roots.trans rfl)
 · exact ff.outputs.trans (frames.outputs.trans rfl)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
