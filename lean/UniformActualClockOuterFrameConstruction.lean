import UniformActualClockOuterSyntaxFrame
import UniformFinalAxisRetention
import UniformAxisCachePreparationRetention

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockOuterFrameConstruction
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformFinalClockOuterRetention
noncomputable section
attribute [local irreducible] UniformRecursiveSavingProgram.program

lemma stride_bound(n:ℕ):UniformCacheLowRetention.z n≤UniformJointAllocation.slab constants n:=
 UniformAxisCachePreparationRetention.slab_above_seed_word constants n

/-- Real kernel/diagonal low-prefix frames preserve all actual outer tables,
caches and saved spectrum; register retention follows from literal syntax. -/
theorem low_two {n ticks:ℕ}(hn:0<n){x:Fin n→ℂ}{s u:State}
 (run:BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n) s ticks u)
 (nat:∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z)
 (outputs:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):
 Frame n s u ∧Spectrum n s u:=by
 have slabPositive:=UniformJointAllocation.actual_arithmetic constants n hn
 have tables:=UniformKernelSpectrumStorage.tables_adjacent constants hn
 have fitN:=UniformGlobalCalendarArena.nat_fits constants hn
 have fitS:=UniformGlobalCalendarArena.scalar_fits constants hn
 refine ⟨⟨⟨?_,?_⟩,?_,?_,?_,UniformActualClockOuterSyntaxFrame.bounded_runs run,outputs,roots⟩,?_⟩
 · intro z hz;exact nat z (by have h:=stride_bound n;omega)
 · intro z hz;exact scalar z (by have h:=stride_bound n;omega)
 · intro i
   have priorN:=UniformGlobalCalendarArena.prior_nat constants n i
   have priorS:=UniformGlobalCalendarArena.prior_scalar constants n i
   exact ⟨fun z _ hz=>nat z (by omega),fun z _ hz=>scalar z (by omega)⟩
 · intro j;exact nat _ (by have hj:=j.isLt;omega)
 · intro j;exact nat _ (by have hj:=j.isLt;omega)
 · intro j;exact scalar _ (UniformKernelSpectrumStorage.cell_below_source constants hn j)

/-- The actual all-axis prefix supplies the same minimal outer frame while
leaving the common numerical source unchanged. -/
theorem axis {n ticks:ℕ}{hn:0<n}{x:Fin n→ℂ}{s u:State}
 (run:BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n) s ticks u)
 (f:UniformFinalAxisRetention.Frame hn s u):Frame n s u∧Spectrum n s u:=by
 have tables:=UniformKernelSpectrumStorage.tables_adjacent constants hn
 have slabPositive:=UniformJointAllocation.actual_arithmetic constants n hn
 refine ⟨⟨⟨?_,?_⟩,f.cache,?_,?_,UniformActualClockOuterSyntaxFrame.bounded_runs run,f.outputs,f.roots⟩,?_⟩
 · intro z hz;exact f.natLow z (hz.trans_le (stride_bound n))
 · intro z hz;exact f.scalarLow z (hz.trans_le (stride_bound n))
 · intro j;exact f.natHigh _ (by omega) (by have hj:=j.isLt;omega)
 · intro j;exact f.natHigh _ (by omega) (by have hj:=j.isLt;omega)
 · intro j;exact f.scalarHigh _ (Nat.le_add_right _ _)

lemma Spectrum.trans {n:ℕ}{s v u:State}(a:Spectrum n s v)(b:Spectrum n v u):Spectrum n s u:=
 fun j=>(b j).trans (a j)
lemma Spectrum.refl(n:ℕ)(s:State):Spectrum n s s:=fun _=>rfl
lemma Spectrum.withPC {n pc:ℕ}{s u:State}(h:Spectrum n s u):Spectrum n s (UniformTensorMonomialMachine.setPC u pc):=h
end
end ExactFourierCircuits.UniformActualClockOuterFrameConstruction
