import DFTModelGlobalKernelJoinWork
import DFTModelGlobalKernelJoinCells
import DFTModelGlobalKernelJoinPeak
import DFTModelGlobalKernelJoinFrame
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open UniformMachine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarSource DFTModelSavingResidualBoolean DFTModelAdmissibilityControl
noncomputable section
attribute [local irreducible] DFTModelGlobalKernelAssembly.program Code.run

structure Specification {F : ℕ} (c : KS.Context F) (K : ℕ) (bank : Tape Tagged.T)
 (s s0 z z0 : State) (ticks : ℕ) : Prop where
 valid : (run DFTModelGlobalKernelAssembly.program (input c bank)).valid
 length : (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2.len=KS.W*c.packing.volume
 boolean : Boolean (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2
 work : (run DFTModelGlobalKernelAssembly.program (input c bank)).work≤
  (K+DFTModelGlobalSectorBilling.preparationFactor+10000)*ticks
 peak : (run DFTModelGlobalKernelAssembly.program (input c bank)).peak≤
  20*(KS.W+DFTModelSavingPeak.wholeCoeff+1)*(c.packing.volume+(axes c).length+1)^2
 cells : ∀r : Fin KS.W,∀j : Fin c.inverse.layout.total,∃out out0,
  z.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+j.val)=some out ∧
  z0.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+j.val)=some out0 ∧
  (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2.look
   (r.val*c.inverse.layout.total+j.val) Tagged.blank=encodePaired out out0
 conductor : ∀j,5920≤j→j<5940→z.natReg j=s.natReg j ∧z0.natReg j=s0.natReg j
 startup : ∀j,100≤j→j<107→z.natReg j=s.natReg j ∧z0.natReg j=s0.natReg j
 outputs : z.outputs=s.outputs ∧z0.outputs=s0.outputs ∧z.rootOrders=s.rootOrders ∧z0.rootOrders=s0.rootOrders

theorem of_result {F n i K prepTicks loopTicks returnTicks N : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (hn : 0<N)
 (shape : UniformSectorPacking.radices (axes c)=List.ofFn (UniformSelectedCRT.radices N))
 (bank : Tape Tagged.T) (entry : Entry c bank v v0) (length : bank.len=KS.W*c.packing.volume) :
 Specification c K bank s s0 z z0 (prepTicks+(loopTicks+(returnTicks+1)+1)) := by
 have checked:=whole_peak c bank v v0 entry length
 exact ⟨checked.1,checked.2.1,checked.2.2.1,whole_work c h hn shape bank entry,
  checked.2.2.2.trans (peak_polynomial c),whole_cells c h bank entry,
  conductor_frame c h,startup_frame c h,DFTModelGlobalKernelSource.Result.outputs c h⟩

/-- Closed whole-kernel source join: the original packing/all-gathers, SAME
closed child once per sector, and original all-scatter/inverse return are
constructed internally. One typed assembly returns both paired channels,
with its entire bill paid by these exact native ticks. Entry is the original
address bank; geometry, constants and finite room remain ordinary caller data. -/
theorem execution {F n i K N : ℕ} (c : KS.Context F) (v v0 : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (ready : UniformConditionalKernelLayout.Ready c i v s)
 (source0 : UniformGlobalRolePackingMachine.Source c.packing v0 s0)
 (hi : i<(KS.states c).length)
 (code : DFTModelGlobalKernelSource.child.length+614≤c.inverse.layout.B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K) (pc : s.pc=0) (wb : WordBound c.metadata.B s)
 (hn : 0<N)
 (shape : UniformSectorPacking.radices (axes c)=List.ofFn (UniformSelectedCRT.radices N))
 (bank : Tape Tagged.T) (entry : Entry c bank v v0) (length : bank.len=KS.W*c.packing.volume) :
 ∃a a0 t t0 z z0 prepTicks loopTicks returnTicks trace,
 DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace ∧
 Specification c K bank s s0 z z0 (prepTicks+(loopTicks+(returnTicks+1)+1)) := by
 obtain ⟨a,a0,t,t0,z,z0,prepTicks,loopTicks,returnTicks,trace,result⟩:=
  DFTModelGlobalKernelSource.execution c v v0 x s s0 same ready source0 hi code cap pc wb
 exact ⟨a,a0,t,t0,z,z0,prepTicks,loopTicks,returnTicks,trace,result,
  of_result c result hn shape bank entry length⟩

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin
