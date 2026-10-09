import UniformProducedAllAxisGeometry
import UniformKernelDiagonalTensorAction
import Mathlib.Data.List.Forall2
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, Proposition 4.2 proof and tensor identity (4.5), PDF p. 20 (`prop:tensor-fourier`, `eq:tensor-multiply`).

This implementation-only alignment ties each lane-zero diagonal coefficient to the same ordered physical axis record used by the common-C kernel. It prevents a separately chosen diagonal from supplying the desired global action.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedAllAxisAlignment
open UniformSectorPacking UniformPhysicalTensorCoefficient
open UniformActualGlobalTickContext
open UniformAllAxisSeedPreparation
noncomputable section

def semanticAxis (a:UniformSectorPacking.Axis) (d:Fin a.widths.sum→ℂ):UniformTensorMonomialMachine.Axis:=
 ⟨a.widths.sum,by have h:=a.radix_two;omega,Equiv.refl _,d,0,0⟩
lemma axes_length (ps:List UniformSectorPacking.Axis)
 (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ):
 (UniformPhysicalTensorCoefficient.axes ps d).length=ps.length:=by
 induction ps with
 | nil=>rfl
 | cons a ps ih=>
  simpa only[UniformPhysicalTensorCoefficient.axes,List.length_cons] using
   congrArg Nat.succ (ih (fun i=>d i.succ))
lemma axes_get (ps:List UniformSectorPacking.Axis)
 (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ) (i:Fin ps.length):
 (UniformPhysicalTensorCoefficient.axes ps d).get (finCongr (axes_length ps d).symm i)=semanticAxis (ps.get i) (d i):=by
 induction ps with
 | nil=>exact Fin.elim0 i
 | cons a ps ih=>
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · exact ih (fun i=>d i.succ) j

def factors {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n)
 (i:Fin (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).length)
 (j:Fin ((UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).get i).widths.sum):ℂ:=
 f.value (UniformProducedAllAxisGeometry.index f i) 0 (finCongr (UniformProducedAllAxisGeometry.shape f i) j)

/-- Canonical produced entries use exactly the lane0 factors attached to the
same actual printed physical axes. This discharges the generic Aligned input. -/
theorem aligned {n:ℕ} (hn:0<n) (f:UniformProducedAllAxisGeometry.Family n):
 UniformKernelDiagonalTensorAction.Aligned
  (UniformActualGlobalTickContext.kernel hn (UniformProducedAllAxisGeometry.geometry f))
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f))
  (factors f):=by
 let ps:=UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical
 let d:=factors f
 change List.Forall₂ CoefficientEq
  (UniformGlobalDiagonalRowsMachine.axes 0 _ _ 0 (UniformJointDiagonalContext.entries n f.pool f.value))
  (UniformPhysicalTensorCoefficient.axes ps d)
 apply entry_axes
 apply List.forall₂_of_length_eq_of_get
 · rw[axes_length]
   simp only[UniformJointDiagonalContext.entries,List.length_ofFn]
   exact (UniformProducedAllAxisGeometry.axes_length f).symm
 · intro j hj hk
   let i:Fin ps.length:=⟨j,by rw[←axes_length ps d];exact hk⟩
   have equal:(⟨j,hk⟩:Fin (UniformPhysicalTensorCoefficient.axes ps d).length)=
    finCongr (axes_length ps d).symm i:=Fin.ext rfl
   rw[equal,axes_get]
   have shape:=UniformProducedAllAxisGeometry.shape f i
   have entryEq:(UniformJointDiagonalContext.entries n f.pool f.value).get ⟨j,hj⟩=
    (⟨radix n (UniformProducedAllAxisGeometry.index f i),
      UniformSelectedCRT.radix_pos n (UniformProducedAllAxisGeometry.index f i),
      f.pool (UniformProducedAllAxisGeometry.index f i),f.value (UniformProducedAllAxisGeometry.index f i)⟩:
      UniformGlobalDiagonalRowsMachine.Entry):=by
    simp only[UniformJointDiagonalContext.entries,List.get_eq_getElem,List.getElem_ofFn]
    rfl
   rw[entryEq]
   change ∃h:radix n (UniformProducedAllAxisGeometry.index f i)=(ps.get i).widths.sum,
    ∀z:Fin (radix n (UniformProducedAllAxisGeometry.index f i)),
     f.value (UniformProducedAllAxisGeometry.index f i) 0 z=d i (finCongr h z)
   refine ⟨shape.symm,?_⟩
   intro z
   change _=f.value (UniformProducedAllAxisGeometry.index f i) 0
    (finCongr shape (finCongr shape.symm z))
   rw[show finCongr shape (finCongr shape.symm z)=z from Fin.ext rfl]
end
end ExactFourierCircuits.UniformProducedAllAxisAlignment
