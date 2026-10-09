import UniformFinalAxisSuffix
import UniformKernelSpectrumStorage
import UniformClockCacheInputsRetention
import UniformAxisCacheLoopState

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisRetention
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformJointAllocation (slab)
open UniformFinalAxisSuffix
noncomputable section

structure Frame {n:ℕ}(hn:0<n)(s u:State):Prop where
 natLow:∀z,z<slab constants n→u.natHeap z=s.natHeap z
 natHigh:∀z,UniformKernelSpectrumStorage.alphaBase constants n≤z→z<5*slab constants n→u.natHeap z=s.natHeap z
 scalarLow:∀z,z<slab constants n→u.scalarHeap z=s.scalarHeap z
 scalarHigh:∀z,UniformKernelSpectrumStorage.base constants n≤z→u.scalarHeap z=s.scalarHeap z
 cache:∀i:Fin (axisCount n),UniformAxisCachePhysical.Heaps constants n i s u
 registers:∀q,UniformFourierAxisPrepareHead.Protected q→q≠5922→q≠5923→q≠5924→q≠5925→u.natReg q=s.natReg q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma frame {n g:ℕ}{hn:0<n}{j:Fin (axisCount n)}{treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event}
 {x:Fin n→ℂ}{s v u:State}{actual:UniformFourierAxisCommonResult.Result constants n g j treeEvents x s v}
 (out:Output hn j treeEvents x s v actual u):Frame hn s u:=by
 have shape:=UniformFourierAxisWorkspace.axis_geometry constants n j
 have dir:=UniformFourierAxisGeometry.axis_directory_before constants n j
 have endFit:=UniformFourierAxisWorkspace.axis_fit constants hn j
 have natBefore:=UniformKernelSpectrumStorage.nat_merged_before constants hn j
 have scalarBefore:=UniformKernelSpectrumStorage.merged_before constants hn j
 have boundaryBefore:=UniformKernelSpectrumStorage.boundary_before constants hn j
 have positive:=UniformFourierAxisGeometry.geometry constants hn j
 have selectedBelow:(UniformFourierAxisWorkspace.axis constants n j).selected≤(UniformFourierAxisWorkspace.axis constants n j).endNat:=by omega
 have slabPositive:0<slab constants n:=by
  have send:(UniformFourierAxisWorkspace.axis constants n j).endScalar=
   (UniformFourierAxisWorkspace.axis constants n j).pool+9*radix n j:=rfl
  have r:=positive.radix
  omega
 refine ⟨?_,?_,?_,?_,?_,out.registers,out.outputs,out.roots⟩
 · intro z hz
   exact out.natOutside z (by omega) (by omega) (by omega)
 · intro z lo hi
   exact out.natOutside z (Or.inr (natBefore.trans lo)) (Or.inr (dir.trans (selectedBelow.trans (natBefore.trans lo)))) (Or.inl (hi.trans_le (Nat.le_add_right _ _)))
 · intro z hz
   exact out.scalarOutside z (Or.inl hz) (by have h:=positive.boundaryMerged;omega)
 · intro z lo
   exact out.scalarOutside z (by omega) (by omega)
 · intro i
   have before:=UniformFourierAxisWorkspace.caches_before constants n i j
   have lower:(slab constants n+2*axisCount n)≤(UniformJointCacheAllocation.axis constants n i).tasks:=by
    change slab constants n+2*UniformJointCacheAllocation.ell n≤_
    dsimp only[UniformJointCacheAllocation.axis,UniformJointCacheAllocation.axisBank,
     UniformJointCacheAllocation.natStart]
    omega
   have scalarLower:UniformJointCacheAllocation.scalarStart constants n≤(UniformJointCacheAllocation.axis constants n i).pool:=by
    dsimp only[UniformJointCacheAllocation.axis,UniformJointCacheAllocation.axisBank]
    omega
   have boundary:=UniformFourierAxisWorkspace.boundary_before_caches constants n j
   constructor
   · intro z lo hi
     exact out.natOutside z (by omega) (by have hj:=j.isLt;omega) (by omega)
   · intro z lo hi
     exact out.scalarOutside z (by omega) (by omega)

lemma Frame.refl {n:ℕ}(hn:0<n)(s:State):Frame hn s s:=
 ⟨fun _ _=>rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
  fun i=>UniformAxisCachePhysical.Heaps.refl constants n i s,fun _ _ _ _ _ _=>rfl,rfl,rfl⟩
lemma Frame.trans {n:ℕ}{hn:0<n}{s t u:State}(a:Frame hn s t)(b:Frame hn t u):Frame hn s u:=
 ⟨fun z h=>(b.natLow z h).trans (a.natLow z h),
  fun z lo hi=>(b.natHigh z lo hi).trans (a.natHigh z lo hi),
  fun z h=>(b.scalarLow z h).trans (a.scalarLow z h),
  fun z h=>(b.scalarHigh z h).trans (a.scalarHigh z h),
  fun i=>(a.cache i).trans (b.cache i),
  fun q h a' b' c' d'=>(b.registers q h a' b' c' d').trans (a.registers q h a' b' c' d'),
  b.outputs.trans a.outputs,b.roots.trans a.roots⟩

lemma Frame.inputs {n:ℕ}{hn:0<n}{x:Fin n→ℂ}{s u:State}(h:Frame hn s u)
 (input:UniformAxisCacheInputs.Inputs n x s):UniformAxisCacheInputs.Inputs n x u:=
 UniformClockCacheInputsRetention.inputs constants hn x s u input h.natLow h.scalarLow
  (fun q lo hi=>h.registers q (by unfold UniformFourierAxisPrepareHead.Protected;omega)
   (by omega) (by omega) (by omega) (by omega)) h.outputs h.roots

lemma Frame.all {n:ℕ}{hn:0<n}{s u:State}(h:Frame hn s u)
 (all:UniformAxisCacheLoopState.All constants n hn (axisCount n) s):
 UniformAxisCacheLoopState.All constants n hn (axisCount n) u:=
 fun i hi=>UniformAxisCacheContents.transport (all i hi) (h.cache i)

end
end ExactFourierCircuits.UniformFinalAxisRetention
