import DFTModelSavingNativeRootData

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeRoot
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine DFTModelAdmissibilityControl DFTModelAffine
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] P.program P.threshold R.reserve DFTModelSavingProgram.program

/-- Finite root: real allocation, binary base, terminal branch and charged
halt. Billing uses those same source witnesses and their actual duration. -/
theorem small_execution (n B k A F K : ℕ) (x : Fin n→ℂ) (s s0 : State)
    (input input0 : Fin W→Fin (2^k)→Scalar)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 4120=k)
    (base : s.natReg 4121=A) (size : s.natReg 4122=2^k) (frontier : s.natReg 4123=F)
    (dp : s.natReg 4151=0) (small : k<P.threshold)
    (data : Present A W (2^k) input s) (data0 : Present A W (2^k) input0 s0)
    (heapBase : 3≤A) (extent : A+W*2^k≤F)
    (code : P.program.length≤B)
    (room : F+34*(k+1)+R.reserve*(k+1)*2^k≤B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 ticks output output0,Result n B k A F K x s s0 u u0 ticks input input0 output output0 := by
  have fb:F≤B:=by omega
  have reserve:R.reserve≤B:=UniformRecursiveSmallBody.reserve_le
    (show F+R.reserve*(k+1)*2^k≤B from by omega)
  have literal:P.threshold≤B:=UniformRecursiveReserve.threshold_fit.trans reserve
  have count:W≤B:=by
    have h:=Nat.mul_le_mul_left W (show 1≤2^k from Nat.two_pow_pos k)
    simp only [Nat.mul_one] at h
    omega
  obtain ⟨u,u0,t,t0,actual,zero,matched,up,up0,out,out0,ef,ef0,fr,fr0,con,con0,
    _ud,_ud0,_uf,_uf0,_root,_child,compiled⟩:=DFTModelSavingNativeSmall.execution
      n B k A F 0 x s s0 input input0 same pc bits base size frontier dp small data data0 heapBase
      constants bound code literal count (extent.trans fb) (by omega)
  simp only [ite_true] at actual zero up up0
  let output:Fin W→Fin (2^k)→Scalar:=fun i=>UniformBinaryBatchCMachine.transformed k (input i)
  let output0:Fin W→Fin (2^k)→Scalar:=fun i=>UniformBinaryBatchCMachine.transformed k (input0 i)
  refine ⟨u,u0,10+UniformRecursiveSmallBase.baseTicks W k+1,output,output0,?_⟩
  refine {
    actual:=actual.executes (halt n B x u up actual.final_bound),
    baseline:=zero.executes (halt n B (fun _=>0) u0 up0 zero.final_bound),matched:=matched,
    pc:=up,pc0:=up0,data:=out,data0:=out0,
    values:=fun i=>UniformBinaryTensorCoordinates.applyAxes_tensor k (input i),
    values0:=fun i=>UniformBinaryTensorCoordinates.applyAxes_tensor k (input0 i),
    natHeap:=?_,natHeap0:=?_,scalarHeap:=?_,scalarHeap0:=?_,constants:=con,constants0:=con0,
    roots:=fr.roots.trans ef.roots,roots0:=fr0.roots.trans ef0.roots,
    outputs:=fr.outputs.trans ef.outputs,outputs0:=fr0.outputs.trans ef0.outputs,
    compiled:=compiled,work:=?_}
  · intro z _;rw [fr.natHeap,ef.natHeap]
  · intro z _;rw [fr0.natHeap,ef0.natHeap]
  · intro z _ away;exact (fr.scalarHeap z away).trans (congrFun ef.scalarHeap z)
  · intro z _ away;exact (fr0.scalarHeap z away).trans (congrFun ef0.scalarHeap z)
  · have factor:33≤K:=by have h:=DFTModelSavingCost.factor_marker;omega
    have work:(run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).work≤
        33*(4+UniformRecursiveSmallBase.baseTicks W k):=
      DFTModelSavingNativeSmallBilling.native_work input input0 small
    exact work.trans
      ((Nat.mul_le_mul_right _ factor).trans (Nat.mul_le_mul_left K (by omega)))

end
end ExactFourierCircuits.DFTModelSavingNativeRoot
