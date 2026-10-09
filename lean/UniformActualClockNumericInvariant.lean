import UniformProducedClockTick
import UniformPhysicalClockPrefix
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockNumericInvariant
open UniformMachine UniformSynchronizedLayers
noncomputable section

def Prefix (n H:ℕ) (length:∀i,(localSchedules n i).length≤H)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (t:ℕ) (s:State):Prop:=
 ∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
 (s.scalarHeap (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n+j.val)).map Scalar.value=
 some ((UniformPhysicalClockPrefix.prefixProduct n H length t).mulVec (fun k=>(v r k).value) j)

lemma initial {n H:ℕ} (length:∀i,(localSchedules n i).length≤H)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State)
 (source:UniformActualClockEntry.Source n v s):Prefix n H length v 0 s:=by
 intro r hr j
 rw[source r hr j,Option.map_some,UniformPhysicalClockPrefix.zero,Matrix.one_mulVec]

lemma transport {n H t:ℕ} (length:∀i,(localSchedules n i).length≤H)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s u:State)
 (ready:Prefix n H length v t s)
 (source:∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
  u.scalarHeap (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n+j.val)=
  s.scalarHeap (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n+j.val)):
 Prefix n H length v t u:=by
 intro r hr j;rw[source r hr j];exact ready r hr j

/-- The actual tagged output from one kernel step satisfies the next physical
matrix prefix; no artificial Scalar tag is introduced to continue the loop. -/
lemma step {n H:ℕ} (length:∀i,(localSchedules n i).length≤H)
 (v w z:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (t:Fin H) (s u:State)
 (ready:Prefix n H length v t.val s)
 (oldSource:UniformActualClockEntry.Source n w s)
 (newSource:UniformActualClockEntry.Source n z u)
 (numeric:∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
  (z r j).value=(UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (fun k=>(w r k).value) j):
 Prefix n H length v (t.val+1) u:=by
 intro r hr j
 have old: (fun k=>(w r k).value)=
  (UniformPhysicalClockPrefix.prefixProduct n H length t.val).mulVec (fun k=>(v r k).value):=by
  funext k
  have h:=ready r hr k
  rw[oldSource r hr k,Option.map_some] at h
  exact Option.some.inj h
 rw[newSource r hr j,Option.map_some,numeric r hr j,old,
  UniformPhysicalClockPrefix.step_values]

lemma final {n H:ℕ} (length:∀i,(localSchedules n i).length≤H)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State)
 (ready:Prefix n H length v H s):UniformActualClockEntry.Numeric n v s:=by
 intro r hr j
 simpa only[UniformPhysicalClockPrefix.final] using ready r hr j

lemma prepared {n:ℕ} (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State)
 (source:UniformActualClockEntry.Source n v s) (tags:UniformActualClockEntry.Prepared v):
 UniformActualClockEntry.PreparedOutput n s:=by
 intro r hr j
 rw[source r hr j,Option.map_some,tags r hr j]
end
end ExactFourierCircuits.UniformActualClockNumericInvariant
