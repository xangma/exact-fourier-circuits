import UniformLocalRequestFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestDriver
open UniformMachine UniformTensorMonomialMachine UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformCanonicalCacheSlotGeometry UniformLocalRectangleCacheBindings
open UniformLocalCacheSlotHeaderMachine
noncomputable section

/-- Only the live memory cursors are recorded. They contain no prepared value,
generated row, factor/action certificate or initialized lower producer header. -/
structure Live (c:Parameters)(I D T index count:ℕ)(s:State):Prop where
 pool:s.natReg 6160=c.pool
 permutation:s.natReg 6162=c.cachePermutation
 widths:s.natReg 6163=c.cacheWidths
 markers:s.natReg 6164=c.cacheMarkers
 axis:s.natReg 6165=c.cacheAxis
 abi:s.natReg 6166=c.cacheDirectory
 lowRow:s.natReg 6168=c.rectangle
 control:s.natReg 6169=c.slot
 inverse:s.natReg 6170=I
 mu:s.natReg 6171=c.mu
 conjugateMu:s.natReg 6172=c.conjugateMu
 pointer:s.natReg 6173=D
 timePointer:s.natReg 6161=T
 index:s.natReg 6174=index
 count:s.natReg 6179=count

lemma Live.withPC {c I D T index count s}(h:Live c I D T index count s)(pc:ℕ):
 Live c I D T index count (setPC s pc):=
 ⟨h.pool,h.permutation,h.widths,h.markers,h.axis,h.abi,h.lowRow,h.control,h.inverse,
 h.mu,h.conjugateMu,h.pointer,h.timePointer,h.index,h.count⟩

lemma bank_read {n:ℕ}{s:State}(h:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (r:ℕ)(lo:6400≤r)(hi:r<6432):s.natReg r=(r-6400+1)*UniformJointCacheWorkspace.stride n:=by
 have value:=h ⟨r-6400,by omega⟩
 simpa only [Nat.add_sub_of_le lo] using value

/-- The original67-produced workspace bank and the measured cursors discharge
every ordinary source register of the44-op context installer. -/
lemma driver (constants:UniformJointAllocation.Constants){n:ℕ}(j:Fin (axisCount n))(q:Row)
 (k time D T index count H:ℕ)(s:State)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (live:Live (context constants n j q k time) (UniformJointCacheWorkspace.inverse n) D T index count s)
 (selected:s.natReg 6167=directoryBase n+2*j.val)
 (timeHigh:H≤T)(timeCell:s.natHeap T=some time):
 Driver j (context constants n j q k time) (UniformJointCacheWorkspace.inverse n) H s:=by
 refine ⟨?_,selected,rfl,?_,?_,rfl⟩
 · intro p hp lo
   simp only [UniformLocalCacheContextMachine.copies,List.mem_cons,List.not_mem_nil,or_false] at hp
   rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals try omega
   · change s.natReg 6407=(8:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨7,by decide⟩
   · change s.natReg 6408=(9:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨8,by decide⟩
   · change s.natReg 6409=(10:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨9,by decide⟩
   · change s.natReg 6410=(11:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨10,by decide⟩
   · change s.natReg 6417=(18:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨17,by decide⟩
   · change s.natReg 6418=(19:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨18,by decide⟩
   · change s.natReg 6419=(20:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨19,by decide⟩
   · change s.natReg 6420=(21:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨20,by decide⟩
   · change s.natReg 6404=(5:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨4,by decide⟩
   · change s.natReg 6410=(11:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨10,by decide⟩
   · exact live.lowRow
   · exact live.control
   · change s.natReg 6422=(23:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨22,by decide⟩
   · change s.natReg 6423=(24:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨23,by decide⟩
   · change s.natReg 6424=(25:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨24,by decide⟩
   · change s.natReg 6425=(26:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨25,by decide⟩
   · change s.natReg 6426=(27:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨26,by decide⟩
   · change s.natReg 6427=(28:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨27,by decide⟩
   · change s.natReg 6428=(29:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨28,by decide⟩
   · change s.natReg 6429=(30:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨29,by decide⟩
   · change s.natReg 6430=(31:ℕ)*UniformJointCacheWorkspace.stride n
     exact bank ⟨30,by decide⟩
   · exact live.pool
   · exact live.mu
   · exact live.conjugateMu
   · exact live.permutation
   · exact live.widths
   · exact live.markers
   · exact live.axis
   · exact live.abi
   · exact live.inverse
 · rw [live.timePointer];exact timeHigh
 · rw [live.timePointer];exact timeCell

lemma boot_live (constants:UniformJointAllocation.Constants){n:ℕ}(j:Fin (axisCount n))(q:Row)
 (R M T time:ℕ)(s:State)
 (h:UniformLocalRequestCursorMachine.Cursor (radix n j) R M T
  (UniformJointCacheAllocation.axis constants n j).control
  (UniformJointCacheAllocation.axis constants n j).pool (UniformJointCacheWorkspace.stride n) s):
 Live (context constants n j q 0 time) (UniformJointCacheWorkspace.inverse n) R T 0 M s:=by
 constructor
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.pool
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.permutation
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.widths
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.markers
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.axis
 · simpa only [context,UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis_radix,
    Nat.mul_zero,Nat.add_zero] using h.abi
 · exact h.lowRow
 · exact h.control
 · exact h.inverse
 · exact h.mu
 · exact h.conjugateMu
 · exact h.pointer
 · exact h.timePointer
 · exact h.index
 · exact h.count
end
end ExactFourierCircuits.UniformLocalRequestDriver
