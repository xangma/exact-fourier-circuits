import UniformJointCacheWorkspace
import UniformCacheRetentionBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCachePhaseEnds
open UniformJointCacheWorkspace UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRectangleDescriptors UniformCacheRetentionRegions

/-- Every actual2308 reusable producer ends below33z. This is a physical
allocation calculation; no generated bank or execution is a premise. -/
lemma ends {n H : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) (high : 33*stride n ≤ H) :
 PhaseEnds (original n q)
  (UniformLocalRectanglePhaseBanks.nextParameters n j q (original n q) (work n))
  (conjugate n) (control n) (disabled n q) H := by
 let c:=original n q
 let K:=c.exponent
 let N:=c.width
 let t:=UniformRadixTwoDAG.count K
 let V:=UniformConvolutionDAG.total K
 let G:=c.gates
 let u:=stride n
 obtain ⟨linear,_,_,ord,rows⟩:=arithmetic hn j q g
 change 100*(K+N+t+V+q.a+q.e+G+1)+1000 ≤ u at linear
 change G*(G+1) ≤ u at ord
 change 6*G*(8*K+7) ≤ u at rows
 change 33*u ≤ H at high
 constructor
 · constructor
   · change 2*u+3*t ≤ H;omega
   · change 3*u+5*V ≤ H;omega
   · change 4*u+5*G ≤ H;omega
   · change 5*u+q.e+1+G ≤ H;omega
   · change 6*u+G*(G+1) ≤ H;omega
   · change 7*u+G+2 ≤ H;omega
   · change 8*u+6*G*(8*K+7) ≤ H;omega
   · change 9*u+2*G*(8*K+7) ≤ H;nlinarith only [rows,high]
   · change 10*u+12 ≤ H;omega
   · change 11*u+3*(8*K+7) ≤ H;omega
 · constructor
   · change 2*u+6*N ≤ H;omega
   · dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
     change 3*u+N+t+5*N+4+1 ≤ H;omega
   · change 4*u+7*N+1 ≤ H;omega
   · change 5*u+7*N ≤ H;omega
   · change 6*u+6 ≤ H;omega
 · constructor
   · change 13*u+3*t ≤ H;omega
   · change 14*u+5*V ≤ H;omega
   · change 15*u+5*G ≤ H;omega
   · change 16*u+q.e+1+G ≤ H;omega
 · constructor
   · change 8*u+6*N ≤ H;omega
   · dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
     change 9*u+N+t+5*N+4+1 ≤ H;omega
   · change 10*u+7*N+1 ≤ H;omega
   · change 11*u+7*N ≤ H;omega
 · have fit:=phase_fit hn j q g
   change 17*u+55*UniformLocalReplayAssembly.phasePrefix (8*K+6) 6 ≤ H
   change 55*UniformLocalReplayAssembly.phasePrefix (8*K+6) 6 ≤ u at fit
   omega
 · constructor
   · change 18*u+6*G*(8*K+7) ≤ H;omega
   · change 19*u+2*G*(8*K+7) ≤ H;nlinarith only [rows,high]
   · change 20*u+12 ≤ H;omega
   · change 21*u+3*(8*K+7) ≤ H;omega

lemma slab_ends (constants : Constants) {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 PhaseEnds (original n q)
  (UniformLocalRectanglePhaseBanks.nextParameters n j q (original n q) (work n))
  (conjugate n) (control n) (disabled n q) (slab constants n) := by
 have high : 33*stride n ≤ slab constants n := by
  have h:=all_reused_below_cache constants n
  change 32*stride n+stride n ≤ slab constants n at h
  omega
 exact ends hn j q g high
end ExactFourierCircuits.UniformCanonicalCachePhaseEnds
