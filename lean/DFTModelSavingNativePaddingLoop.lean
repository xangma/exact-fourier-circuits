import DFTModelSavingNativePaddingLoopResult

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingLoop
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
open UniformRecursivePaddingArrays (values action)
open DFTModelSavingNativePaddingControl (parent_match metadata_match)
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.residual DFTModelCacheRecords.unit

/-- Internal chronological composition. The concrete role theorem discharges
`roles` at the public padding entry; it is not an action or output premise. -/
theorem loop (n B U R A F q w r stack depth stackTop saved index prior : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (handler : Handler DFTModelSavingRecords.Port)
    (L : List (Fin R)) (visit : UniformRecursiveResidualDirectionLoop.Visit R index L)
    (roles : ∀(role : Fin R)(prior : ℕ)(a a0 : State)
      (X X0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar),
      StateMatch a a0→a.pc=P.address .paddingPatch→
      Parent (q*(w+1)+r) q A F r stack depth a→
      Metadata F U saved role.val R a→a.natReg 4175=role.val→
      Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data a→
      Present A R (2^(q*(w+1)+r)) X a→Present A R (2^(q*(w+1)+r)) X0 a0→
      UniformBinaryCStageMachine.Constants a→WordBound B a→
      ∃b b0 ticks Y Y0, DFTModelSavingNativePaddingRole.Result n B U R A F q w r
        stack depth stackTop saved R cost x role I handler a a0 b b0 ticks X X0 Y Y0)
    (s s0 : State) (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .paddingTest)
    (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (metadata : Metadata F U saved index R s)
    (printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (present0 : Present A R (2^(q*(w+1)+r)) f0 s0)
    (low : 6≤F) (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u u0 ticks g g0 outPrior,
      Result n B U R A F q w r stack depth stackTop saved cost x L I handler index prior
        s s0 u u0 ticks outPrior f f0 g g0  :=  by
  induction visit generalizing s s0 f f0 prior with
  | done=>
    obtain ⟨a, test, ap, pa, ma, _, _, tf⟩ := DFTModelSavingNativePaddingControl.test
      n B (q*(w+1)+r) q A F r stack depth U saved R R x s pc parent metadata low bound code
    obtain ⟨a0, test0, ap0, pa0, ma0, _, _, tf0⟩ := DFTModelSavingNativePaddingControl.test
      n B (q*(w+1)+r) q A F r stack depth U saved R R (fun _=>0) s0
      (same.pc.trans pc) (parent_match same parent) (metadata_match same metadata) low
      (same.wordBound bound) code
    have ap':a.pc=P.address .paddingFinish := by simpa only [Nat.lt_irrefl, ite_false] using ap
    have ap0':a0.pc=P.address .paddingFinish := by simpa only [Nat.lt_irrefl, ite_false] using ap0
    obtain ⟨u, finish, up, cursor, pu, _, ff⟩ := DFTModelSavingNativePaddingControl.finish
      n B (q*(w+1)+r) q A F r stack depth U saved R R x a ap' pa ma low test.final_bound code
    obtain ⟨u0, finish0, _, _, pu0, _, ff0⟩ := DFTModelSavingNativePaddingControl.finish
      n B (q*(w+1)+r) q A F r stack depth U saved R R (fun _=>0) a0 ap0' pa0 ma0 low test0.final_bound code
    refine ⟨u, u0, 6+4, f, f0, prior, ?_⟩
    refine {
      run := test.trans finish, zeroRun := test0.trans finish0,
      matched := DFTModelSavingNativeControl.paired_runs (test.trans finish) (test0.trans finish0) same,
      pc := up, cursor := cursor, parent := pu, zeroParent := pu0,
      printed := ?_, present := ?_, zeroPresent := ?_, nat := ?_, zeroNat := ?_, scalar := ?_, zeroScalar := ?_,
      constants := ?_, zeroConstants := ?_, roots := ff.roots.trans tf.roots,
      zeroRoots := ff0.roots.trans tf0.roots, outputs := ff.outputs.trans tf.outputs,
      zeroOutputs := ff0.outputs.trans tf0.outputs, time := by simp, value := rfl, values := rfl, zeroValues := rfl}
    · intro j hj;rw [ff.natHeap _ (by simp), tf.natHeap _ (by simp)];exact printed j hj
    · intro i z;rw [ff.scalarHeap, tf.scalarHeap];exact present i z
    · intro i z;rw [ff0.scalarHeap, tf0.scalarHeap];exact present0 i z
    · intro z _ _ _ _ _;rw [ff.natHeap _ (by simp), tf.natHeap _ (by simp)]
    · intro z _ _ _ _ _;rw [ff0.natHeap _ (by simp), tf0.natHeap _ (by simp)]
    · intro z _ _;rw [ff.scalarHeap, tf.scalarHeap]
    · intro z _ _;rw [ff0.scalarHeap, tf0.scalarHeap]
    · unfold UniformBinaryCStageMachine.Constants at constants ⊢
      rw [ff.scalarHeap, tf.scalarHeap];exact constants
    · have c0 := DFTModelSavingNativeEntry.constants_match same constants
      unfold UniformBinaryCStageMachine.Constants at c0 ⊢
      rw [ff0.scalarHeap, tf0.scalarHeap];exact c0
  | step j tail visit ih=>
    obtain ⟨a, test, ap, pa, ma, dst, _, tf⟩ := DFTModelSavingNativePaddingControl.test
      n B (q*(w+1)+r) q A F r stack depth U saved j.val R x s pc parent metadata low bound code
    obtain ⟨a0, test0, _, _, _, _, _, tf0⟩ := DFTModelSavingNativePaddingControl.test
      n B (q*(w+1)+r) q A F r stack depth U saved j.val R (fun _=>0) s0
      (same.pc.trans pc) (parent_match same parent) (metadata_match same metadata) low
      (same.wordBound bound) code
    have ap':a.pc=P.address .paddingPatch := by simpa only [j.isLt, ite_true] using ap
    have matched := DFTModelSavingNativeControl.paired_runs test test0 same
    have printA:Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data a := by
      intro z hz;rw [tf.natHeap _ (by simp)];exact printed z hz
    have dataA:Present A R (2^(q*(w+1)+r)) f a := by
      intro i z;rw [tf.scalarHeap];exact present i z
    have dataA0:Present A R (2^(q*(w+1)+r)) f0 a0 := by
      intro i z;rw [tf0.scalarHeap];exact present0 i z
    have ca:UniformBinaryCStageMachine.Constants a := by
      unfold UniformBinaryCStageMachine.Constants at constants ⊢
      rw [tf.scalarHeap];exact constants
    obtain ⟨b, b0, dt, Y, Y0, one⟩ := roles j prior a a0 f f0 matched ap' pa ma dst printA dataA dataA0 ca test.final_bound
    obtain ⟨u, u0, ut, Z, Z0, outPrior, remaining⟩ := ih j.val b b0 Y Y0 one.matched one.pc one.parent
      one.metadata one.printed one.present one.zeroPresent one.constants one.run.final_bound
    refine ⟨u, u0, 6+dt+ut, Z, Z0, outPrior, ?_⟩
    refine {
      run := (test.trans one.run).trans remaining.run,
      zeroRun := (test0.trans one.zeroRun).trans remaining.zeroRun, matched := remaining.matched,
      pc := remaining.pc, cursor := remaining.cursor, parent := remaining.parent, zeroParent := remaining.zeroParent,
      printed := remaining.printed, present := remaining.present, zeroPresent := remaining.zeroPresent,
      nat := ?_, zeroNat := ?_, scalar := ?_, zeroScalar := ?_, constants := remaining.constants,
      zeroConstants := remaining.zeroConstants, roots := remaining.roots.trans (one.roots.trans tf.roots),
      zeroRoots := remaining.zeroRoots.trans (one.zeroRoots.trans tf0.roots),
      outputs := remaining.outputs.trans (one.outputs.trans tf.outputs),
      zeroOutputs := remaining.zeroOutputs.trans (one.zeroOutputs.trans tf0.outputs),
      time := ?_, value := ?_, values := ?_, zeroValues := ?_}
    · intro z hz away a b c
      exact (remaining.nat z hz away a b c).trans ((one.nat z hz away a b c).trans (tf.natHeap z (by simp)))
    · intro z hz away a b c
      exact (remaining.zeroNat z hz away a b c).trans ((one.zeroNat z hz away a b c).trans (tf0.natHeap z (by simp)))
    · intro z hz away
      have outside:z<A+j.val*2^(q*(w+1)+r)∨A+(j.val+1)*2^(q*(w+1)+r)≤z := by
        have mul : (j.val+1)*2^(q*(w+1)+r)≤R*2^(q*(w+1)+r) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
        omega
      exact (remaining.scalar z hz away).trans ((one.scalar z hz outside).trans (congrFun tf.scalarHeap z))
    · intro z hz away
      have outside:z<A+j.val*2^(q*(w+1)+r)∨A+(j.val+1)*2^(q*(w+1)+r)≤z := by
        have mul : (j.val+1)*2^(q*(w+1)+r)≤R*2^(q*(w+1)+r) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
        omega
      exact (remaining.zeroScalar z hz away).trans ((one.zeroScalar z hz outside).trans (congrFun tf0.scalarHeap z))
    · have atime := one.time;have btime := remaining.time
      simp only [List.length_cons, Nat.succ_mul];omega
    · simp only [List.length_cons]
      rw [DFTModelSavingNativePaddingFold.steps_succ, one.value]
      exact remaining.value
    · change values Z=action q w r R tail (UniformRecursivePaddingArrays.applyRole q w r R j (values f))
      rw [←one.values];exact remaining.values
    · change values Z0=action q w r R tail (UniformRecursivePaddingArrays.applyRole q w r R j (values f0))
      rw [←one.zeroValues];exact remaining.zeroValues

end
end ExactFourierCircuits.DFTModelSavingNativePaddingLoop
