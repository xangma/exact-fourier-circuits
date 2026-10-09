import UniformGlobalCalendarDispatchBoot

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs)
noncomputable section

lemma code_32 : program[32]?=some (.jump 235) := rfl
lemma code_40 : program[40]?=some (.jump 243) := rfl

/-- The actual dynamic phase decoder is invoked inside the281 program. -/
theorem phase_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (h : Header A N r O T used phaseBank j s) (loaded : Loaded r d s)
 (phase : d.elapsed<28) (pc : s.pc=30) (wb : WordBound B s) (code : 281 ≤ B)
 (printed : UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words s)
 (phaseFit : phaseBank+56 ≤ B) :
 ∃u, BoundedRuns program n x B s 11 u ∧u.pc=33∧Header A N r O T used phaseBank j u∧Loaded r d u∧
 u.natReg 6764=UniformGlobalCalendarPhaseDirectory.kind (UniformGlobalMatchingScaleMachine.phases.get
  ⟨d.elapsed,by rw [UniformGlobalMatchingScaleMachine.phases_length];exact phase⟩)∧
 u.natReg 6765=UniformGlobalCalendarPhaseDirectory.lane (UniformGlobalMatchingScaleMachine.phases.get
  ⟨d.elapsed,by rw [UniformGlobalMatchingScaleMachine.phases_length];exact phase⟩)∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 let ready:=applyBlock phaseSetup s
 have er: d.elapsed ≤ B:=by simpa only [loaded.elapsed] using (wb.2.1 6779)
 have setup:=block_runs phaseSetup program 30 n B x s phaseSetup_code pc wb (by change 32 ≤ B;omega)
  (by simp [phaseSetup,readable,Op.readable])
  (by simp [phaseSetup,peak,Op.peak,Op.apply,writeNat,next,h.phaseBankReg,h.one,loaded.elapsed];omega)
 have rp : ready.pc=32:=by rw [applyBlock_pc,pc];rfl
 have jump : step program n x ready=.running {ready with pc:=235}:=by simp [step,rp,code_32]
 have rs : WordBound B {ready with pc:=0}:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨run,k,l⟩:=UniformGlobalCalendarPhaseDirectory.read_execution phaseBank B n x {ready with pc:=0} ⟨d.elapsed,phase⟩
  (by simp [ready,phaseSetup,applyBlock,Op.apply,writeNat,next,h.phaseBankReg,h.one])
  (by simp [ready,phaseSetup,applyBlock,Op.apply,writeNat,next,loaded.elapsed,h.one]) rfl rs printed phaseFit (by omega)
 have placedR:=UniformBoundedAssembly.boundedExecution_placed phase_code
  (by rw [UniformGlobalCalendarPhaseDirectory.program_length];omega) (by omega) run
 let u : State:={applyBlock UniformGlobalCalendarPhaseDirectory.readOps {ready with pc:=0} with pc:=33}
 change BoundedRuns program n x B {ready with pc:=235} 8 u at placedR
 refine ⟨u,by convert setup.trans (.next setup.final_bound jump placedR) using 1;rfl,rfl,?_,?_,k,l,rfl,rfl,rfl,rfl⟩
 · exact h.transfer (by intro z lo hi;simp (disch := omega)
    [u,UniformGlobalCalendarPhaseDirectory.readOps,ready,phaseSetup,applyBlock,Op.apply,writeNat,next])
 · constructor <;> simp [u,UniformGlobalCalendarPhaseDirectory.readOps,ready,phaseSetup,applyBlock,Op.apply,writeNat,next,
    loaded.address,loaded.elapsed,loaded.pool,loaded.widthCount,loaded.permutation,loaded.kind,loaded.pairs]

/-- The actual lane merger multiplies the fresh accumulator by every scalar
cell in the selected cached lane, preserving the whole cache and other lanes. -/
theorem factor_execution {n A N r O T used phaseBank j B lane : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (f g : ℕ→ℂ) (h : Header A N r O T used phaseBank j s) (loaded : Loaded r d s)
 (laneReg : s.natReg 6765=lane) (laneFit : lane<9) (pc : s.pc=36) (wb : WordBound B s)
 (code : 281 ≤ B) (source : UniformGlobalCalendarFactorMerge.Factors (d.pool+lane*r) r f s.scalarHeap)
 (target : UniformGlobalCalendarFactorMerge.Factors O r g s.scalarHeap)
 (sourceFit : d.pool+9*r ≤ B) (fresh : d.pool+9*r ≤ O) (outputFit : O+r ≤ B) :
 ∃u, BoundedRuns program n x B s (9*r+12) u ∧u.pc=41∧Header A N r O T used phaseBank j u∧
 UniformGlobalCalendarFactorMerge.Factors O r (fun i=>f i*g i) u.scalarHeap∧
 (∀z,z<O∨O+r ≤ z→u.scalarHeap z=s.scalarHeap z)∧
 u.natHeap=s.natHeap∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 let ready:=applyBlock factorSetup s
 have setup:=block_runs factorSetup program 36 n B x s factorSetup_code pc wb (by change 40 ≤ B;omega)
  (by simp [factorSetup,readable,Op.readable])
  (by simp [factorSetup,peak,Op.peak,Op.apply,writeNat,next,loaded.pool,h.radix,h.one,h.pool,laneReg];omega)
 simp only [show factorSetup.length=4 from rfl] at setup
 have args : UniformGlobalCalendarFactorMerge.Args d.pool r lane O {ready with pc:=0}:=by
  constructor <;> simp [ready,factorSetup,applyBlock,Op.apply,writeNat,next,loaded.pool,h.radix,h.one,h.pool,laneReg]
 have rp : ready.pc=40:=by rw [applyBlock_pc,pc];rfl
 have jump : step program n x ready=.running {ready with pc:=243}:=by simp [step,rp,code_40]
 have rs : WordBound B {ready with pc:=0}:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨u,run,uh,heap,nh,roots,outputs⟩:=UniformGlobalCalendarFactorMerge.execution x f g {ready with pc:=0}
  args rfl rs (by omega) source target sourceFit fresh laneFit outputFit
 have placedR:=UniformBoundedAssembly.boundedExecution_placed factor_code
  (by rw [UniformGlobalCalendarFactorMerge.program_length];omega) (by omega) run
 change BoundedRuns program n x B {ready with pc:=243} (9*r+7) {u with pc:=41} at placedR
 refine ⟨{u with pc:=41},?_,rfl,?_,?_,?_,nh,roots,outputs⟩
 · convert setup.trans (.next setup.final_bound jump placedR) using 1;omega
 · exact h.transfer (by
    intro z lo hi
    exact (UniformGlobalCalendarPrinterFrames.factor_natFrame run z (by omega)).trans
     (by simp (disch := omega) [ready,factorSetup,applyBlock,Op.apply,writeNat,next]))
 · intro i hi;rw [heap];exact UniformGlobalCalendarFactorMerge.mergeHeap_get O f g 0 r s.scalarHeap i (by omega) (by omega)
 · intro z outside;rw [heap];exact UniformGlobalCalendarFactorMerge.mergeHeap_frame O f g 0 r s.scalarHeap z (by omega)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
