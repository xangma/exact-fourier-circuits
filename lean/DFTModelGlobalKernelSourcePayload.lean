import DFTModelGlobalKernelSourcePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformSectorPayloadBridge (Cover location location_spec payload payloadFin zero)
noncomputable section

/-- Read only the already executed complete child heap. No output action is
assumed: `present` is extracted from the genuine closed-loop result. -/
lemma payload_at {B F A E : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : DFTModelGlobalSectorLoop.Geometry W B F reserve A E xs) (cover : Cover xs g.volume)
 (s : State) (present : ∀i,∀hi:i<xs.length,∃out : Fin W→Fin (2^(xs[i]'hi).pairs)→Scalar,
  UniformFixedNetworkShearChildMachine.Present (A+W*(xs[i]'hi).start) W (2^(xs[i]'hi).pairs) out s)
 (i : ℕ) (hi : i<xs.length) (r t : ℕ) (hr : r<W) (ht : t<(xs[i]'hi).width) :
 s.scalarHeap (A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t)=
  some (payload cover W A s r ((xs[i]'hi).start+t)) := by
 have bound : (xs[i]'hi).start+t<g.volume := by have:=g.fits i hi;omega
 let j : Fin g.volume:=⟨(xs[i]'hi).start+t,bound⟩
 have selected : location cover j=⟨i,hi⟩ := UniformSectorPayloadBridge.interval_unique
  g.ordered (location cover j) ⟨i,hi⟩ j.val (location_spec cover j)
  ⟨by dsimp[j];omega,by dsimp[j];omega⟩
 obtain ⟨out,cells⟩:=present i hi
 have cell:=cells ⟨r,hr⟩ ⟨t,by rw[←g.pow i hi];exact ht⟩
 have someCell : (s.scalarHeap (A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t)).isSome=true := by
  rw[g.pow i hi];rw[cell];rfl
 rw[payload,dite_eq_left bound]
 change _=some (payloadFin cover W A s r j)
 unfold payloadFin
 simpa only[selected,j,Nat.add_sub_cancel_left] using UniformSectorPayloadBridge.getD_present _ someCell

theorem cover {F : ℕ} (c : Context F) : Cover (states c) c.loop.volume :=
 UniformSectorPayloadBridge.actual_cover c.physical c.loop.volume
  (c.physicalVolume.trans (c.inverseVolume.trans c.loopVolume.symm))
def returnedValues {F : ℕ} (c : Context F) (s : State) : ℕ→ℕ→Scalar :=
 payload (cover c) W c.gather.buffer s

lemma completed_sources {F n K ticks : ℕ} (c : Context F)
 {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ} {s s0 u u0 : State} {trace : List ℕ}
 (h : DFTModelGlobalSectorLoop.Result n c.inverse.layout.B F c.gather.buffer c.gather.directory K
  c.loop.volume (states c) (states c) v v0 x s s0 u u0 ticks 9 trace) :
 UniformAllSectorTransposeMachine.Source c.scatter (returnedValues c u) u ∧
 UniformAllSectorTransposeMachine.Source c.scatter (returnedValues c u0) u0 := by
 have pa : ∀i,∀hi:i<(states c).length,∃out : Fin W→Fin (2^((states c)[i]'hi).pairs)→Scalar,
  UniformFixedNetworkShearChildMachine.Present
   (c.gather.buffer+W*((states c)[i]'hi).start) W (2^((states c)[i]'hi).pairs) out u := by
  intro i hi;obtain ⟨a,a0,p,p0,_⟩:=h.completed i hi hi;exact ⟨a,p⟩
 have pz : ∀i,∀hi:i<(states c).length,∃out : Fin W→Fin (2^((states c)[i]'hi).pairs)→Scalar,
  UniformFixedNetworkShearChildMachine.Present
   (c.gather.buffer+W*((states c)[i]'hi).start) W (2^((states c)[i]'hi).pairs) out u0 := by
  intro i hi;obtain ⟨a,a0,p,p0,_⟩:=h.completed i hi hi;exact ⟨a0,p0⟩
 constructor
 all_goals
  intro i hi r hr t ht
  change t<((states c)[i]'hi).width at ht
  simp only[UniformSectorTransposeMachine.sourceAddress,
   UniformAllSectorTransposeMachine.Geometry.local,ite_true,c.scatterBuffer,
   UniformAllSectorTransposeMachine.slice]
 · exact payload_at (loop_geometry c) (cover c) u pa i hi r t hr ht
 · exact payload_at (loop_geometry c) (cover c) u0 pz i hi r t hr ht
end
end ExactFourierCircuits.DFTModelGlobalKernelSource
