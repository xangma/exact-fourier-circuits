import UniformSeedConjugatePreparation
set_option autoImplicit false
namespace SeedConjugateFixtures
open ExactFourierCircuits UniformMachine UniformSeedConjugatePreparation
noncomputable section

theorem literal_length : program.length=466 := program_length

theorem selected_runtimes : UniformReciprocalMachine.completeRuntime 1+40+148=629 ∧
    UniformReciprocalMachine.completeRuntime 2+80+148=944 ∧
    UniformReciprocalMachine.completeRuntime 4+160+148=1613 := by decide

theorem actual_n1 (x : Fin 1→ℂ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata 1 s) (ho:UniformInitialPreparation.Operands 1 x s)
    (hr:UniformAllAxisSeedPreparation.Retained 1 (UniformAllAxisSeedPreparation.axisCount 1) s)
    (hp:s.pc=0) (hj:s.natReg 110=(lastAxis 1).val) (hs:WordBound (3^19) s) : ∃u,
    BoundedExecution program 1 x (3^19) s
      (UniformReciprocalMachine.completeRuntime (radix 1 (lastAxis 1))+40*radix 1 (lastAxis 1)+148) u ∧
    ConjugateCompact (radix 1 (lastAxis 1)) (destination 1) u ∧
    UniformAllAxisSeedPreparation.Retained 1 (UniformAllAxisSeedPreparation.axisCount 1) u ∧ Frame 1 s u := by
  obtain ⟨u,hu,_,hc,_,_,hr',hf,_⟩:=execution (by decide : 0<1) x (lastAxis 1) s hm ho hr hp hj hs
  exact ⟨u,hu,hc,hr',hf⟩

theorem actual_n4 (x : Fin 4→ℂ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata 4 s) (ho:UniformInitialPreparation.Operands 4 x s)
    (hr:UniformAllAxisSeedPreparation.Retained 4 (UniformAllAxisSeedPreparation.axisCount 4) s)
    (hp:s.pc=0) (hj:s.natReg 110=(lastAxis 4).val) (hs:WordBound (6^19) s) : ∃u,
    BoundedExecution program 4 x (6^19) s
      (UniformReciprocalMachine.completeRuntime (radix 4 (lastAxis 4))+40*radix 4 (lastAxis 4)+148) u ∧
    ConjugateCompact (radix 4 (lastAxis 4)) (destination 4) u ∧
    UniformAllAxisSeedPreparation.Retained 4 (UniformAllAxisSeedPreparation.axisCount 4) u ∧ Frame 4 s u := by
  obtain ⟨u,hu,_,hc,_,_,hr',hf,_⟩:=execution (by decide : 0<4) x (lastAxis 4) s hm ho hr hp hj hs
  exact ⟨u,hu,hc,hr',hf⟩

theorem nonreal_lane4 (q : Fin 5) (j : Fin 4) :
    UniformLocalSeedTableMachine.seedValue (axisRoot 4) q j.val=
      starRingEnd ℂ (UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta 4) q j.val) :=
  seedValue_conjugate 4 (by decide) q j

theorem selected_root4 : axisRoot 4=starRingEnd ℂ (OAI.ExactFourier.zeta 4) :=
  UniformConjugateLocalPreparation.axisRoot_conjugate 4

end
end SeedConjugateFixtures
