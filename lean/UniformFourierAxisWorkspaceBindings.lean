import UniformFourierAxisWorkspaceHeader
import UniformJointDiagonalHeaderInstallation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisWorkspaceBindings
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformJointAllocation UniformJointCacheAllocation
namespace WS
export UniformFourierAxisWorkspace (axis natPrefix axisBank natAmount)
end WS
noncomputable section

lemma arguments(c:Constants)(n:ℕ)(j:Fin (ell n))(s:State)
 (radix:s.natReg 6800=UniformAllAxisSeedPreparation.radix n j)
 (natFrontier:s.natReg 5924=UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val)
 (scalarFrontier:s.natReg 5925=UniformGlobalCalendarArena.scalarBase c n+
  9*UniformAllAxisSeedPreparation.prefixSum n j.val)
 (N S:ℕ)(result:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j) N S s):
 UniformFourierAxisWorkspaceHeader.Args (UniformAllAxisSeedPreparation.radix n j)
  (UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val)
  (UniformGlobalCalendarArena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val) S s:=by
 exact ⟨radix,natFrontier,scalarFrontier,result.pool,result.endScalar⟩

lemma word_fit(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (WS.axis c n j).endNat ≤ envelope c n ∧(WS.axis c n j).endScalar ≤ envelope c n ∧80 ≤ envelope c n:=by
 have ends:=UniformFourierAxisWorkspace.axis_fit c hn j
 have large:=fixed_large c
 unfold envelope
 omega

/-- The genuine final62 allocator observation and fresh outer cursors feed
all28 ordinary header instructions. All desired addresses are conclusions. -/
theorem execution(c:Constants){n start:ℕ}(hn:0<n)(j:Fin (ell n))
 (program:Program)(x:Fin n→ℂ)(s:State)
 (radix:s.natReg 6800=UniformAllAxisSeedPreparation.radix n j)
 (natFrontier:s.natReg 5924=UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val)
 (scalarFrontier:s.natReg 5925=UniformGlobalCalendarArena.scalarBase c n+
  9*UniformAllAxisSeedPreparation.prefixSum n j.val)
 (N S:ℕ)(result:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j) N S s)
 (code:BlockAt UniformFourierAxisWorkspaceHeader.block program start)(pc:s.pc=start)
 (extent:start+28 ≤ envelope c n)(wb:WordBound (envelope c n) s):
 BoundedRuns program n x (envelope c n) s 28 (applyBlock UniformFourierAxisWorkspaceHeader.block s) ∧
 UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val)
  (UniformGlobalCalendarArena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val)
  (applyBlock UniformFourierAxisWorkspaceHeader.block s):=by
 have fit:=word_fit c hn j
 have ar:=arguments c n j s radix natFrontier scalarFrontier N S result
 have pos:=UniformGlobalLocalPreparation.radix_pos n j
 have natFit:UniformGlobalCalendarArena.natBase c n+WS.natPrefix n j.val+
  WS.natAmount (UniformAllAxisSeedPreparation.radix n j) ≤ envelope c n:=by
  simpa only [WS.axis,(UniformFourierAxisWorkspace.axis_ends _ _ _).1] using fit.1
 have scalarFit:UniformGlobalCalendarArena.scalarBase c n+
  9*UniformAllAxisSeedPreparation.prefixSum n j.val+9*UniformAllAxisSeedPreparation.radix n j ≤ envelope c n:=by
  simpa only [WS.axis,(UniformFourierAxisWorkspace.axis_ends _ _ _).2] using fit.2.1
 exact UniformFourierAxisWorkspaceHeader.execution program x s ar pos natFit scalarFit fit.2.2 code pc extent wb
end
end ExactFourierCircuits.UniformFourierAxisWorkspaceBindings
