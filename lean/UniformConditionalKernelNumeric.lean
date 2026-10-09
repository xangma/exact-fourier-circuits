import UniformSectorNumericTensorBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalKernelNumeric
open UniformMachine UniformSectorPacking UniformSectorTensor
open UniformConditionalKernelLayout (Context Ready packed movementCost programFor)
noncomputable section
lemma inverse_address (as:List UniformSectorPackingMachine.PhysicalAxis) (L:UniformSectorPackingMachine.Layout)
 (h:UniformSectorPackingMachine.physicalVolume as=L.total)
 (j:Fin (UniformSectorPackingMachine.physicalVolume as)):
 ((UniformSectorPackingMachine.physicalUnpacking as L h).symm (finCongr h j)).val=
  (packingPermutation (UniformSectorPackingMachine.physicalAxes as) j).val:=by
 change (finCongr h (packingPermutation (UniformSectorPackingMachine.physicalAxes as)
  ((finCongr h).symm (finCongr h j)))).val=_
 rw[Equiv.symm_apply_apply]
 rfl
lemma packed_input {W F reserve:ℕ} (c:Context W F reserve)
 (v:ℕ → Fin c.packing.volume → Scalar) (r:ℕ)
 (j:Fin (UniformSectorPackingMachine.physicalVolume c.physical)):
 (packed c v r j.val).value=(v r (finCongr c.physicalVolume
  (unpackingPermutation (UniformSectorPackingMachine.physicalAxes c.physical) j))).value:=by
 have bound:j.val < c.packing.volume:=by rw[←c.physicalVolume];exact j.isLt
 unfold packed UniformGlobalPackingChildPreparation.packedValues
 rw[dite_eq_left bound]
 have same:(⟨j.val,bound⟩:Fin c.packing.volume)=finCongr c.physicalVolume j:=Fin.ext rfl
 rw[same]
 simp only[UniformGlobalRolePackingMachine.permutation,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- This is the concrete numerical operator of the entire fixed operational
kernel, including actual physical packing and both transposes. RootBody is
still explicitly required, so this is not an unconditional whole-DFT claim. -/
theorem execution {W F reserve n ordinal:ℕ} (child:Program) (c:Context W F reserve)
 (cost:ℕ → ℕ) (v:ℕ → Fin c.packing.volume → Scalar) (x:Fin n → ℂ) (s:State)
 (ready:Ready c ordinal v s) (hi:ordinal < (UniformProducedSectorChildABI.states c.physical).length)
 (root:UniformConditionalSectorLoop.RootBody child W n c.inverse.layout.B F reserve cost x)
 (positive:0 < W) (code:child.length+614 ≤ c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x c.metadata.B s ticks u ∧
 ticks ≤ movementCost c+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states c.physical)+
  213*c.inverse.layout.total+W*(16*c.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states c.physical).length+57 ∧u.pc=child.length+613 ∧
 (∀r,r < W → ∀j:Fin (UniformSectorPackingMachine.physicalVolume c.physical),
  (u.scalarHeap (c.inverse.destination+r*(UniformSectorPackingMachine.physicalVolume c.physical)+j.val)).map Scalar.value=
  some ((originalTensor (UniformSectorPackingMachine.physicalAxes c.physical)).mulVec
   (fun k=>(v r (finCongr c.physicalVolume k)).value) j)) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 obtain ⟨mid,u,ticks,done,run,cheap,up,stored,outputs,roots⟩:=
  UniformConditionalKernelExecution.execution child c cost v x s ready hi root positive code pc wb
 let axes:=UniformSectorPackingMachine.physicalAxes c.physical
 let cover:=UniformSectorPayloadBridge.actual_cover c.physical c.loop.volume
  ((c.physicalVolume.trans c.inverseVolume).trans c.loopVolume.symm)
 have volume:UniformSectorPackingMachine.physicalVolume c.physical=c.inverse.layout.total:=
  c.physicalVolume.trans c.inverseVolume
 have stores:∀r,r < W → ∀j:Fin (radices axes).prod,
  u.scalarHeap (c.inverse.destination+r*(radices axes).prod+j.val)=
   some (UniformSectorPayloadBridge.payload cover W c.gather.buffer mid r (packingPermutation axes j).val):=by
  intro r hr j
  have actual:=stored r hr (finCongr volume j)
  rw[inverse_address c.physical c.inverse.layout volume j] at actual
  simpa only[finCongr_apply,Fin.val_cast,←volume] using actual
 have numeric:=UniformSectorNumericTensorBridge.native_tensor axes c.loop cover (packed c v)
  (fun r k=>(v r (finCongr c.physicalVolume k)).value) mid u done
  (fun r _ j=>packed_input c v r j) c.inverse.destination stores
 exact ⟨u,ticks,run,cheap,up,numeric,outputs,roots⟩
end
end ExactFourierCircuits.UniformConditionalKernelNumeric
