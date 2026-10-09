import UniformGlobalCalendarDispatchFactors

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs)
noncomputable section

lemma code_46 : program[46]?=some (.jump 258) := rfl
lemma code_48 : program[48]?=some (.jump 49) := rfl
lemma code_50 : program[50]?=some (.jump 10) := rfl

/-- The281 dispatcher appends each genuine ordered pair bank via its literal23
row printer and copies back the actual updated row count. -/
theorem rows_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (records : ℕ→ℕ×ℕ) (h : Header A N r O T used phaseBank j s) (loaded : Loaded r d s)
 (pc : s.pc=42) (wb : WordBound B s) (code : 281 ≤ B)
 (source : UniformGlobalCalendarUnionRows.Rows d.permutation (r-d.widthCount) records s.natHeap)
 (sourceFit : d.permutation+2*(r-d.widthCount) ≤ B) (fresh : d.permutation+2*(r-d.widthCount) ≤ T)
 (values : ∀i,i<r-d.widthCount→(records i).1 ≤ B∧(records i).2 ≤ B)
 (outputFit : T+3*(used+(r-d.widthCount)) ≤ B) :
 ∃u, BoundedRuns program n x B s (16*(r-d.widthCount)+15) u∧u.pc=49∧
 Header A N r O T (used+(r-d.widthCount)) phaseBank j u∧
 u.natHeap=UniformGlobalCalendarUnionRows.writeRows T used records 0 (r-d.widthCount) s.natHeap∧
 u.scalarHeap=s.scalarHeap∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 let ready:=applyBlock rowsSetup s
 have setup:=block_runs rowsSetup program 42 n B x s rowsSetup_code pc wb (by change 46 ≤ B;omega)
  (by simp [rowsSetup,readable,Op.readable])
  (by simp [rowsSetup,peak,Op.peak,Op.apply,writeNat,next,loaded.permutation,loaded.pairs,h.rows,h.usedReg,h.one];omega)
 simp only [show rowsSetup.length=4 from rfl] at setup
 have args : UniformGlobalCalendarUnionRows.Args d.permutation (r-d.widthCount) T used {ready with pc:=0}:=by
  constructor <;> simp [ready,rowsSetup,applyBlock,Op.apply,writeNat,next,loaded.permutation,loaded.pairs,h.rows,h.usedReg,h.one]
 have rp : ready.pc=46:=by rw [applyBlock_pc,pc];rfl
 have jump : step program n x ready=.running {ready with pc:=258}:=by simp [step,rp,code_46]
 have rs : WordBound B {ready with pc:=0}:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨u,run,uh,heap⟩:=UniformGlobalCalendarUnionRows.execution x records {ready with pc:=0}
  args rfl rs (by omega) source sourceFit fresh values outputFit
 have frames:=UniformGlobalCalendarUnionRows.execution_scalarFrame run
 have placedR:=UniformBoundedAssembly.boundedExecution_placed rows_code
  (by rw [UniformGlobalCalendarUnionRows.program_length];omega) (by omega) run
 change BoundedRuns program n x B {ready with pc:=258} (16*(r-d.widthCount)+8) {u with pc:=47} at placedR
 have part:=setup.trans (.next setup.final_bound jump placedR)
 have hh : Header A N r O T used phaseBank j u:=h.transfer (by
  intro z lo hi
  exact (UniformGlobalCalendarPrinterFrames.rows_natFrame run z (by omega)).trans
   (by simp (disch := omega) [ready,rowsSetup,applyBlock,Op.apply,writeNat,next]))
 let last:=applyBlock rowsReturn {u with pc:=47}
 have usedBound : used+(r-d.widthCount) ≤ B:=by omega
 have back:=block_runs rowsReturn program 47 n B x {u with pc:=47} rowsReturn_code rfl part.final_bound
  (by change 48 ≤ B;omega) (by simp [rowsReturn,readable,Op.readable])
  (by simp [rowsReturn,peak,Op.peak,uh.used,hh.one];omega)
 simp only [show rowsReturn.length=1 from rfl] at back
 have lp : last.pc=48:=by rw [applyBlock_pc];rfl
 have exit : step program n x last=.running {last with pc:=49}:=by simp [step,lp,code_48]
 have outBound : WordBound B {last with pc:=49}:=changePC_bound B last 49 back.final_bound (by omega)
 refine ⟨{last with pc:=49},?_,rfl,?_,heap,frames.scalarHeap,frames.rootOrders,frames.outputs⟩
 · convert (part.trans back).trans (.next back.final_bound exit (.refl outBound)) using 1;omega
 · constructor <;> simp [last,rowsReturn,applyBlock,Op.apply,writeNat,next,uh.used,hh.selected,hh.count,hh.radix,
    hh.pool,hh.rows,hh.phaseBankReg,hh.index,hh.one,hh.two,hh.zero]

/-- The actual loop increment and back edge cost two instructions. -/
theorem advance_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (h : Header A N r O T used phaseBank j s) (pc : s.pc=49) (wb : WordBound B s)
 (code : 281 ≤ B) (index : j<N) :
 BoundedRuns program n x B s 2 {applyBlock advance s with pc:=10}∧
 Header A N r O T used phaseBank (j+1) {applyBlock advance s with pc:=10} := by
 have countBound : N ≤ B:=by simpa only [h.count] using (wb.2.1 6767)
 have run:=block_runs advance program 49 n B x s advance_code pc wb (by change 50 ≤ B;omega)
  (by simp [advance,readable,Op.readable])
  (by simp [advance,peak,Op.peak,h.index,h.one];omega)
 have endPC : (applyBlock advance s).pc=50:=by rw [applyBlock_pc,pc];rfl
 have jump : step program n x (applyBlock advance s)=.running {applyBlock advance s with pc:=10}:=by simp [step,endPC,code_50]
 have bound : WordBound B {applyBlock advance s with pc:=10}:=changePC_bound B _ 10 run.final_bound (by omega)
 refine ⟨run.trans (.next run.final_bound jump (.refl bound)),?_⟩
 constructor <;> simp [advance,applyBlock,Op.apply,writeNat,next,h.selected,h.count,h.radix,h.pool,h.rows,h.usedReg,
  h.phaseBankReg,h.index,h.one,h.two,h.zero]

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
