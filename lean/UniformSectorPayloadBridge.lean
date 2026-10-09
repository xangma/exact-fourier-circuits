import UniformConditionalSectorLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPayloadBridge
open UniformMachine UniformTensorMonomialMachine
open UniformConditionalSectorLoop (Geometry Completed)
noncomputable section

def Cover (xs:List UniformSectorPacking.BlockState) (V:ℕ):Prop:=
 ∀j:Fin V,∃i:Fin xs.length,(xs[i.val]'i.isLt).start ≤ j.val ∧
  j.val < (xs[i.val]'i.isLt).start+(xs[i.val]'i.isLt).width
def location {xs:List UniformSectorPacking.BlockState} {V:ℕ} (cover:Cover xs V) (j:Fin V):Fin xs.length:=
 Classical.choose (cover j)
lemma location_spec {xs:List UniformSectorPacking.BlockState} {V:ℕ} (cover:Cover xs V) (j:Fin V):
 (xs[(location cover j).val]'(location cover j).isLt).start ≤ j.val ∧
 j.val < (xs[(location cover j).val]'(location cover j).isLt).start+
  (xs[(location cover j).val]'(location cover j).isLt).width:=Classical.choose_spec (cover j)

def zero:Scalar:=⟨0,false⟩
/-- A description of the already returned physical tagged heap, used only in
proofs. Every actual movement remains the charged41/137/25 machine execution. -/
def payloadFin {xs:List UniformSectorPacking.BlockState} {V:ℕ} (cover:Cover xs V)
 (W A:ℕ) (s:State) (r:ℕ) (j:Fin V):Scalar:=
 let i:=location cover j
 let st:=xs[i.val]'i.isLt
 (s.scalarHeap (A+W*st.start+r*st.width+(j.val-st.start))).getD zero
def payload {xs:List UniformSectorPacking.BlockState} {V:ℕ} (cover:Cover xs V)
 (W A:ℕ) (s:State) (r j:ℕ):Scalar:=if h:j < V then payloadFin cover W A s r ⟨j,h⟩ else zero
lemma interval_unique {xs:List UniformSectorPacking.BlockState}
 (ordered:UniformAllSectorPaddingMachine.Ordered xs) (i j:Fin xs.length) (z:ℕ)
 (left:(xs[i.val]'i.isLt).start ≤ z ∧z < (xs[i.val]'i.isLt).start+(xs[i.val]'i.isLt).width)
 (right:(xs[j.val]'j.isLt).start ≤ z ∧z < (xs[j.val]'j.isLt).start+(xs[j.val]'j.isLt).width):i=j:=by
 apply Fin.ext
 by_contra ne
 rcases lt_or_gt_of_ne ne with lo|hi
 · have:=ordered i.val j.val i.isLt j.isLt lo;omega
 · have:=ordered j.val i.val j.isLt i.isLt hi;omega
lemma getD_present (q:Option Scalar) (present:q.isSome=true):q=some (q.getD zero):=by
 cases q <;>simp_all

/-- Actual complete sector outputs determine a single packed payload,
including the exact dependency tags chosen by the executed recursive child. -/
lemma payload_at {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (cover:Cover xs g.volume)
 (v:ℕ → ℕ → Scalar) (s:State) (done:Completed W A xs v xs.length s)
 (i:ℕ) (hi:i < xs.length) (r t:ℕ) (hr:r < W) (ht:t < (xs[i]'hi).width):
 s.scalarHeap (A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t)=
  some (payload cover W A s r ((xs[i]'hi).start+t)):=by
 have bound:(xs[i]'hi).start+t < g.volume:=by have:=g.fits i hi;omega
 let j:Fin g.volume:=⟨(xs[i]'hi).start+t,bound⟩
 have selected:location cover j=⟨i,hi⟩:=interval_unique g.ordered (location cover j) ⟨i,hi⟩ j.val
  (location_spec cover j) ⟨by dsimp[j];omega,by dsimp[j];omega⟩
 have present:(s.scalarHeap (A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t)).isSome=true:=
  (done i hi hi r hr ⟨t,by rw[←g.pow i hi];exact ht⟩).1
 rw[payload,dite_eq_left bound]
 change _=some (payloadFin cover W A s r j)
 unfold payloadFin
 simpa only[selected,j,Nat.add_sub_cancel_left] using getD_present _ present
lemma actual_cover (as:List UniformSectorPackingMachine.PhysicalAxis) (V:ℕ)
 (volume:UniformSectorPackingMachine.physicalVolume as=V):
 Cover (UniformProducedSectorChildABI.states as) V:=by
 intro j
 have geom:(UniformSectorPacking.radices (UniformSectorPackingMachine.physicalAxes as)).prod=V:=volume
 obtain ⟨i,hi,t,ht,equal⟩:=UniformGlobalInverseReturn.sector_cover (UniformSectorPackingMachine.physicalAxes as)
  (finCongr geom.symm j)
 have width:t < ((UniformProducedSectorChildABI.states as)[i]'hi).width:=ht
 refine ⟨⟨i,hi⟩,?_,?_⟩
 · change ((UniformProducedSectorChildABI.states as)[i]'hi).start ≤ j.val
   change ((UniformProducedSectorChildABI.states as)[i]'hi).start+t=j.val at equal
   omega
 · change j.val < ((UniformProducedSectorChildABI.states as)[i]'hi).start+((UniformProducedSectorChildABI.states as)[i]'hi).width
   change ((UniformProducedSectorChildABI.states as)[i]'hi).start+t=j.val at equal
   omega
lemma inverse_source {W B F reserve A E:ℕ} {as:List UniformSectorPackingMachine.PhysicalAxis}
 (g:Geometry W B F reserve A E (UniformProducedSectorChildABI.states as))
 (volume:UniformSectorPackingMachine.physicalVolume as=g.volume)
 (transpose:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (buffer:transpose.buffer=A) (v:ℕ → ℕ → Scalar) (s:State)
 (done:Completed W A (UniformProducedSectorChildABI.states as) v (UniformProducedSectorChildABI.states as).length s):
 UniformAllSectorTransposeMachine.Source transpose (payload (actual_cover as g.volume volume) W A s) s:=by
 intro i hi r hr t ht
 simpa only[UniformSectorTransposeMachine.sourceAddress,UniformAllSectorTransposeMachine.Geometry.local,
  ite_true,buffer,UniformAllSectorTransposeMachine.slice] using
  payload_at g (actual_cover as g.volume volume) v s done i hi r t hr ht
end
end ExactFourierCircuits.UniformSectorPayloadBridge
