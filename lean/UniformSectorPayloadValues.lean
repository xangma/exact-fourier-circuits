import UniformConditionalKernelExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPayloadValues
open UniformMachine UniformConditionalSectorLoop
open UniformSectorPayloadBridge
noncomputable section

/-- The returned tag description has the actual numeric physical Cq value
for each genuine five-word sector. This follows from the executed heap. -/
lemma payload_value_at {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (cover:Cover xs g.volume) (v:ℕ → ℕ → Scalar)
 (s:State) (done:Completed W A xs v xs.length s) (i:ℕ) (hi:i < xs.length)
 (r:ℕ) (hr:r < W) (t:Fin (2^(xs[i]'hi).pairs)):
 (payload cover W A s r ((xs[i]'hi).start+t.val)).value=
  (UniformBinaryTensorCoordinates.physicalMatrix (xs[i]'hi).pairs).mulVec
   (fun z=>(v r ((xs[i]'hi).start+z.val)).value) t:=by
 have ht:t.val < (xs[i]'hi).width:=by rw[g.pow i hi];exact t.isLt
 have stored:=payload_at g cover v s done i hi r t.val hr ht
 have numeric:=(done i hi hi r hr t).2
 rw[stored] at numeric
 exact Option.some.inj numeric

/-- The operator here is defined by the literal generated sector records and
numeric binary matrices, with no selected child action or host permutation. -/
def packedValue {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (cover:Cover xs g.volume) (v:ℕ → ℕ → Scalar)
 (r:ℕ) (j:Fin g.volume):ℂ:=
 let i:=location cover j
 let st:=xs[i.val]'i.isLt
 let t:Fin (2^st.pairs):=⟨j.val-st.start,by
  have h:=location_spec cover j
  rw[←g.pow i.val i.isLt]
  dsimp[i,st] at *
  omega⟩
 (UniformBinaryTensorCoordinates.physicalMatrix st.pairs).mulVec
  (fun z=>(v r (st.start+z.val)).value) t
lemma payload_value {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (cover:Cover xs g.volume) (v:ℕ → ℕ → Scalar)
 (s:State) (done:Completed W A xs v xs.length s) (r:ℕ) (hr:r < W) (j:Fin g.volume):
 (payload cover W A s r j.val).value=packedValue g cover v r j:=by
 let i:=location cover j
 have h:=location_spec cover j
 let t:Fin (2^(xs[i.val]'i.isLt).pairs):=⟨j.val-(xs[i.val]'i.isLt).start,by
  rw[←g.pow i.val i.isLt];dsimp[i];omega⟩
 have equal:(xs[i.val]'i.isLt).start+t.val=j.val:=by dsimp[t,i];omega
 have value:=payload_value_at g cover v s done i.val i.isLt r hr t
 rw[equal] at value
 exact value
lemma native_numeric {W B F reserve A E V:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (cover:Cover xs g.volume) (v:ℕ → ℕ → Scalar)
 (mid u:State) (done:Completed W A xs v xs.length mid) (destination:ℕ)
 (p:Fin V ≃ Fin g.volume)
 (stored:∀r,r < W → ∀j:Fin V,u.scalarHeap (destination+r*V+j.val)=some (payload cover W A mid r (p j).val)):
 ∀r,r < W → ∀j:Fin V,(u.scalarHeap (destination+r*V+j.val)).map Scalar.value=
  some (packedValue g cover v r (p j)):=by
 intro r hr j
 rw[stored r hr j,Option.map_some,payload_value g cover v mid done r hr (p j)]
end
end ExactFourierCircuits.UniformSectorPayloadValues
