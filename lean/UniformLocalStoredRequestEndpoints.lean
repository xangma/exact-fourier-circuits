import UniformLocalStoredRequestRegisterFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl
noncomputable section

/-- These are measured final registers of the actual request loop. The ordinal
is the sum of the produced finite phase counts; register6128 is a pool end. -/
structure Endpoints (constants:Constants)(n:ℕ)(j:Fin (axisCount n))
 (qs:List Request)(R T:ℕ)(s:State):Prop where
 pool:s.natReg 6160=(UniformJointCacheAllocation.axis constants n j).pool+
  9*radix n j*slotPrefix n qs qs.length
 permutation:s.natReg 6162=(UniformJointCacheAllocation.axis constants n j).control+
  (3*radix n j+11)*slotPrefix n qs qs.length
 widths:s.natReg 6163=s.natReg 6162+radix n j
 markers:s.natReg 6164=s.natReg 6162+2*radix n j
 physicalAxis:s.natReg 6165=s.natReg 6162+3*radix n j
 abi:s.natReg 6166=s.natReg 6162+3*radix n j+4
 pointer:s.natReg 6173=R+7*qs.length
 timePointer:s.natReg 6161=T+qs.length
 index:s.natReg 6174=qs.length
 count:s.natReg 6179=qs.length

lemma Ready.endpoints {constants n j qs R T g x s}
 (h:@Ready constants n j qs R T g x qs.length s):Endpoints constants n j qs R T s:=by
 have c:=h.control.live
 have pool:s.natReg 6160=(UniformJointCacheAllocation.axis constants n j).pool+
  9*radix n j*slotPrefix n qs qs.length:=c.pool
 have permutation:s.natReg 6162=(UniformJointCacheAllocation.axis constants n j).control+
  (3*radix n j+11)*slotPrefix n qs qs.length:=c.permutation
 refine ⟨pool,permutation,?_,?_,?_,?_,c.pointer,c.timePointer,c.index,c.count⟩
 all_goals rw[permutation]
 · exact c.widths
 · exact c.markers
 · exact c.axis
 · exact c.abi

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
