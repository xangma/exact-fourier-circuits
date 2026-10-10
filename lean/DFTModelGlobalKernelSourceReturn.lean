import DFTModelGlobalKernelSourcePayload
import DFTModelGlobalKernelSourceLoopFrame
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open DFTModelAdmissibilityControl
noncomputable section

structure Return {F n : ℕ} (c : Context F) (x : Fin n→ℂ)
 (s s0 u u0 : State) (ticks : ℕ) : Prop where
 actual : BoundedExecution (UniformGlobalInverseReturn.programFor W) n x c.inverse.layout.B (setPC s 0) ticks u
 baseline : BoundedExecution (UniformGlobalInverseReturn.programFor W) n (fun _=>0) c.inverse.layout.B (setPC s0 0) ticks u0
 matched : StateMatch u u0
 pc : u.pc=219
 values : ∀r,r<W→∀j:Fin c.inverse.layout.total,
  u.scalarHeap (c.inverse.destination+r*c.inverse.layout.total+j.val)=some
   (returnedValues c s r ((UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
     (c.physicalVolume.trans c.inverseVolume)).symm j).val)
 values0 : ∀r,r<W→∀j:Fin c.inverse.layout.total,
  u0.scalarHeap (c.inverse.destination+r*c.inverse.layout.total+j.val)=some
   (returnedValues c s0 r ((UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
     (c.physicalVolume.trans c.inverseVolume)).symm j).val)
 cheap : ticks≤213*c.inverse.layout.total+W*(16*c.inverse.layout.total+12)+
  (12*W+20)*(states c).length+48
 outputs : u.outputs=s.outputs
 outputs0 : u0.outputs=s0.outputs
 roots : u.rootOrders=s.rootOrders
 roots0 : u0.rootOrders=s0.rootOrders

/-- The true existing15-header setup follows the entire closed child loop.
All41 scatters and the real137/25 inverse packing are then executed. -/
theorem return_execution {F n i K loopTicks : ℕ} (c : Context F)
 (v v0 : ℕ→Fin c.packing.volume→Scalar) (x : Fin n→ℂ)
 (s s0 a a0 t t0 : State) (prepTicks : ℕ) {trace : List ℕ}
 (prep : Preparation (i:=i) c v v0 x s s0 a a0 prepTicks)
 (h : DFTModelGlobalSectorLoop.Result n c.inverse.layout.B F c.gather.buffer c.gather.directory K
  c.loop.volume (states c) (states c) (UniformConditionalKernelLayout.packed c v)
  (UniformConditionalKernelLayout.packed c v0) x (setPC a 0) (setPC a0 0) t t0 loopTicks 9 trace)
 (code : 220≤c.inverse.layout.B) : ∃u u0 ticks,Return c x t t0 u u0 ticks := by
 have table : UniformAllSectorTransposeMachine.Table c.scatter (setPC t 0) := by
  intro j hj;rw[c.scatterDirectory,c.scatterBuffer];exact h.table j hj
 have table0 : UniformAllSectorTransposeMachine.Table c.scatter (setPC t0 0) := by
  intro j hj
  rcases table j hj with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨(congrFun h.matched.natHeap _).trans h0,(congrFun h.matched.natHeap _).trans h1,
    (congrFun h.matched.natHeap _).trans h2,(congrFun h.matched.natHeap _).trans h3,
    (congrFun h.matched.natHeap _).trans h4⟩
 have source := completed_sources c h
 have cacheBelow : c.packing.suffix≤F := by rw[←c.inverseSuffix];exact c.cacheBelow
 have banks : UniformGlobalRolePackingMachine.Banks c.packing c.physical (setPC t 0) := by
  refine ⟨?_,?_,?_⟩
  · apply UniformConditionalSectorReturn.rows_prefix c.physical 0 c.packing.rows F a (setPC t 0) prep.actual.banks.1
    · have bound:=c.inverse.layout.rowsBelow
      rw[c.inverseRows,←c.inverseLength] at bound
      simpa only[Nat.zero_add] using bound.trans c.cacheBelow
    · exact h.frame.nat
  · exact UniformConditionalSectorReturn.widths_prefix _ _ _ _ prep.actual.banks.2.1
     (fun ax hx=>(c.widthsBelow ax hx).trans cacheBelow) h.frame.nat
  · exact UniformConditionalSectorReturn.permutations_prefix _ _ _ _ prep.actual.banks.2.2
     (fun ax hx=>(c.permutationsBelow ax hx).trans cacheBelow) h.frame.nat
 have banks0 : UniformGlobalRolePackingMachine.Banks c.packing c.physical (setPC t0 0) := by
  refine ⟨UniformGlobalInverseReturn.rows_same_heap _ _ _ _ _ banks.1 h.matched.natHeap,?_,?_⟩
  · intro ax hx j;exact (congrFun h.matched.natHeap _).trans (banks.2.1 ax hx j)
  · intro ax hx j;exact (congrFun h.matched.natHeap _).trans (banks.2.2 ax hx j)
 have args : UniformGlobalInverseReturn.Args c.inverse c.scatter.directory (setPC t 0) :=
  UniformConditionalSectorReturn.args_transfer c.inverse a (setPC t 0) prep.actual.inverse
   (fun j lo hi=>DFTModelGlobalKernelSourceLoopFrame.execution_nat h.actual j
     (Or.inr ⟨by omega,by omega,by omega⟩))
 have args0 : UniformGlobalInverseReturn.Args c.inverse c.scatter.directory (setPC t0 0) := by
  constructor <;>change t0.natReg _=_ <;>rw[h.matched.natReg]
  all_goals first|exact args.volume|exact args.source|exact args.directory|exact args.axes|exact args.rows|
   exact args.suffix|exact args.stack|exact args.inverse|exact args.temporary|exact args.destination
 have count : t.natReg 464=(states c).length :=
  (DFTModelGlobalKernelSourceLoopFrame.execution_nat h.actual 464 (Or.inl rfl)).trans prep.actual.count
 have count0 : t0.natReg 464=(states c).length := by rw[h.matched.natReg];exact count
 have rows : UniformSectorPackingMachine.Rows c.physical 0 c.inverse.layout.rows (setPC t 0) := by
  rw[c.inverseRows];exact banks.1
 have rows0 : UniformSectorPackingMachine.Rows c.physical 0 c.inverse.layout.rows (setPC t0 0) := by
  rw[c.inverseRows];exact banks0.1
 have positive : 0<W := DFTModelGlobalSectorLoop.roles_positive
 obtain ⟨u,ticks,run,cheap,up,values,_outside,out,roots⟩:=UniformGlobalInverseReturn.execution c.inverse c.physical
  c.inverseLength (c.physicalVolume.trans c.inverseVolume) c.scatter c.scatterB c.scatterVolume c.scatterSource
  (returnedValues c t) x (setPC t 0) args count table source.1 rows banks.2.1 banks.2.2
  (by simpa only[c.inverseSuffix] using c.widthsBelow)
  (by simpa only[c.inverseSuffix] using c.permutationsBelow) positive code rfl
  (changePC_bound _ _ _ h.actual.final_bound (by omega))
 obtain ⟨u0,ticks0,run0,_cheap0,_up0,values0,_outside0,out0,roots0⟩:=UniformGlobalInverseReturn.execution c.inverse c.physical
  c.inverseLength (c.physicalVolume.trans c.inverseVolume) c.scatter c.scatterB c.scatterVolume c.scatterSource
  (returnedValues c t0) (fun _ : Fin n=>0) (setPC t0 0) args0 count0 table0 source.2 rows0 banks0.2.1 banks0.2.2
  (by simpa only[c.inverseSuffix] using c.widthsBelow)
  (by simpa only[c.inverseSuffix] using c.permutationsBelow) positive code rfl
  (changePC_bound _ _ _ h.baseline.final_bound (by omega))
 obtain ⟨z,zrun,matched⟩:=boundedExecution_match (y:=fun _ : Fin n=>0) run (h.matched.withPC 0)
 obtain ⟨eqTicks,eqState⟩:=zrun.executes.deterministic run0.executes
 subst ticks0;subst z
 exact ⟨u,u0,ticks,run,run0,matched,up,values,values0,cheap,out,out0,roots,roots0⟩
end
end ExactFourierCircuits.DFTModelGlobalKernelSource
