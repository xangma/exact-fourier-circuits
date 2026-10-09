import UniformLocalRequestPlan
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestControl
open UniformMachine UniformTensorMonomialMachine UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestDriver UniformLocalCacheSlotConductorMachine
noncomputable section

structure Control (constants:UniformJointAllocation.Constants)(n:ℕ)(j:Fin (axisCount n))
 (qs:List Request)(R T i:ℕ)(s:State):Prop where
 live:Live (controller constants n j qs i) (UniformJointCacheWorkspace.inverse n)
  (R+7*i) (T+i) i qs.length s
 bank:UniformLocalRectangleWorkspaceHeaders.Bank n s
 selected:s.natReg 6167=directoryBase n+2*j.val
 axis:s.natReg 6906=j.val

lemma Control.withPC {constants n j qs R T i s}(h:Control constants n j qs R T i s)(pc:ℕ):
 Control constants n j qs R T i (setPC s pc):=⟨h.live.withPC pc,h.bank,h.selected,h.axis⟩

lemma Control.retained {constants n j qs R T i s u}(h:Control constants n j qs R T i s)
 (low:∀q,6160≤q→q≤6179→u.natReg q=s.natReg q)
 (high:∀q,6400≤q→u.natReg q=s.natReg q):Control constants n j qs R T i u:=by
 refine ⟨?_,fun f=>(high _ (by have:=f.isLt;omega)).trans (h.bank f),
  (low _ (by omega) (by omega)).trans h.selected,(high _ (by omega)).trans h.axis⟩
 constructor
 all_goals first
  | exact (low _ (by omega) (by omega)).trans h.live.pool
  | exact (low _ (by omega) (by omega)).trans h.live.permutation
  | exact (low _ (by omega) (by omega)).trans h.live.widths
  | exact (low _ (by omega) (by omega)).trans h.live.markers
  | exact (low _ (by omega) (by omega)).trans h.live.axis
  | exact (low _ (by omega) (by omega)).trans h.live.abi
  | exact (low _ (by omega) (by omega)).trans h.live.lowRow
  | exact (low _ (by omega) (by omega)).trans h.live.control
  | exact (low _ (by omega) (by omega)).trans h.live.inverse
  | exact (low _ (by omega) (by omega)).trans h.live.mu
  | exact (low _ (by omega) (by omega)).trans h.live.conjugateMu
  | exact (low _ (by omega) (by omega)).trans h.live.pointer
  | exact (low _ (by omega) (by omega)).trans h.live.timePointer
  | exact (low _ (by omega) (by omega)).trans h.live.index
  | exact (low _ (by omega) (by omega)).trans h.live.count

lemma boot (constants:UniformJointAllocation.Constants){n:ℕ}(j:Fin (axisCount n))
 (qs:List Request)(R T:ℕ)(s:State)
 (h:UniformLocalRequestCursorMachine.Cursor (radix n j) R qs.length T
  (UniformJointCacheAllocation.axis constants n j).control
  (UniformJointCacheAllocation.axis constants n j).pool (UniformJointCacheWorkspace.stride n) s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (selected:s.natReg 6167=directoryBase n+2*j.val)(axis:s.natReg 6906=j.val):
 Control constants n j qs R T 0 s:=by
 refine ⟨?_,bank,selected,axis⟩
 simpa only [controller,UniformLocalRequestPlan.prefix_zero,Nat.mul_zero,Nat.add_zero] using
  UniformLocalRequestDriver.boot_live constants j (requestAt qs 0).row R qs.length T (requestAt qs 0).time s h

/-- The next request uses the real measured factor/partition end registers
returned by the inner1336 loop. There is no host cursor update. -/
lemma advance {constants n j qs R T i B ticks}{x:Fin n→ℂ}{s u:State}
 (h:Control constants n j qs R T i s)(more:i<qs.length)
 (measured:Cursor.Control (controller constants n j qs i)
  (slotCount n (qs[i]'more).row) s)
 (run:BoundedExecution UniformLocalRequestAdvanceMachine.program n x B s ticks u)
 (copied:∀p∈UniformLocalRequestAdvanceMachine.copies,u.natReg p.1=s.natReg p.2)
 (pointer:u.natReg 6173=s.natReg 6173+7)(index:u.natReg 6174=s.natReg 6174+1)
 (time:u.natReg 6161=s.natReg 6161+1):Control constants n j qs R T (i+1) u:=by
 have fixed (q:ℕ)(notWritten:q∉UniformLocalRequestFrames.advanceWrites):u.natReg q=s.natReg q:=
  UniformLocalRequestFrames.advance_nat run q notWritten
 refine ⟨?_,fun f=>(UniformLocalRequestFrames.advance_high run _ (by have:=f.isLt;omega)).trans (h.bank f),
  (fixed _ (by decide)).trans h.selected,(UniformLocalRequestFrames.advance_high run _ (by omega)).trans h.axis⟩
 constructor
 · have value:=measured.args 6128 (by omega) (by omega)
   have actual: u.natReg 6160=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).pool:=
    (copied (6160,6128) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · have value:=measured.args 6133 (by omega) (by omega)
   have actual: u.natReg 6162=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).cachePermutation:=
    (copied (6162,6133) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · have value:=measured.args 6134 (by omega) (by omega)
   have actual: u.natReg 6163=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).cacheWidths:=
    (copied (6163,6134) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · have value:=measured.args 6135 (by omega) (by omega)
   have actual: u.natReg 6164=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).cacheMarkers:=
    (copied (6164,6135) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · have value:=measured.args 6136 (by omega) (by omega)
   have actual: u.natReg 6165=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).cacheAxis:=
    (copied (6165,6136) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · have value:=measured.args 6137 (by omega) (by omega)
   have actual: u.natReg 6166=(Cursor.shifted (controller constants n j qs i)
    (slotCount n (qs[i]'more).row)).cacheDirectory:=
    (copied (6166,6137) (by decide)).trans value
   convert actual using 1
   dsimp only [controller,UniformCanonicalCacheSlotGeometry.context,UniformJointCacheAllocation.slot,
    Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters]
   rw [prefix_step n qs i more];simp only [UniformJointCacheAllocation.axis_radix];ring
 · exact (fixed _ (by decide)).trans h.live.lowRow
 · exact (fixed _ (by decide)).trans h.live.control
 · exact (fixed _ (by decide)).trans h.live.inverse
 · exact (fixed _ (by decide)).trans h.live.mu
 · exact (fixed _ (by decide)).trans h.live.conjugateMu
 · rw [pointer,h.live.pointer];omega
 · rw [time,h.live.timePointer];omega
 · exact index.trans (congrArg (·+1) h.live.index)
 · exact (fixed _ (by decide)).trans h.live.count
end
end ExactFourierCircuits.UniformLocalRequestControl
