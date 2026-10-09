import UniformRecursivePreparedRootExecution

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, PDF pp. 11–12; §3.4, prepared-scalar discussion, p. 18.
Determinism identifies any actual halted run with the constructed prepared run. This tag-transport step has no separate paper counterpart; it ensures that later preparation uses the same machine states.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRootExecution
open UniformMachine UniformFixedNetwork
open UniformRecursivePreparedValues
noncomputable section

/-- All active inputs, collectively, are prepared. Unrelated heap cells and
registers may have true dependency tags. This applies to any actual halted run
of the same corrected fixed program, not merely a newly chosen witness. -/
/- Paper: No separate paper lemma: deterministic-state identification transports the prepared invariant to the actual run used by surrounding §3 preparation. It does not select a fresh unrelated terminal state. -/
theorem prepared_of_execution (n B k A F:ℕ)(x:Fin n→ℂ)
 (input:Fin W→Fin (2^k)→Scalar)(s u:State)(ticks:ℕ)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(size:s.natReg 4122=2^k)
 (frontier:s.natReg 4123=F)(dp:s.natReg 4151=0)
 (data:∀i z,s.scalarHeap (A+i.val*2^k+z.val)=some (input i z))
 (heapBase:3≤A)(extent:A+W*2^k≤F)(code:P.program.length≤B)
 (room:F+34*(k+1)+R.reserve*(k+1)*2^k≤B)(square:(2^k)^2≤B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (prepared:Prepared2 input)(run:BoundedExecution P.program n x B s ticks u):
 ∀(i:Fin W)(z:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+z.val)).map Scalar.dependent=some false:=by
 obtain ⟨v,t,exec,_,_,_,_,_,_,_,tags⟩:=execution_prepared n B k A F x input s
  pc bits base size frontier dp data heapBase extent code room square constants bound
 have same:=run.executes.deterministic exec.executes
 rw [same.2]
 exact tags prepared

/-- The collective invariant also supplies actual present prepared outputs. -/
theorem prepared_present_of_execution (n B k A F:ℕ)(x:Fin n→ℂ)
 (input:Fin W→Fin (2^k)→Scalar)(s u:State)(ticks:ℕ)
 (pc:s.pc=0)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)(size:s.natReg 4122=2^k)
 (frontier:s.natReg 4123=F)(dp:s.natReg 4151=0)
 (data:∀i z,s.scalarHeap (A+i.val*2^k+z.val)=some (input i z))
 (heapBase:3≤A)(extent:A+W*2^k≤F)(code:P.program.length≤B)
 (room:F+34*(k+1)+R.reserve*(k+1)*2^k≤B)(square:(2^k)^2≤B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)
 (prepared:Prepared2 input)(run:BoundedExecution P.program n x B s ticks u):
 ∀(i:Fin W)(z:Fin (2^k)),∃v,u.scalarHeap (A+i.val*2^k+z.val)=some v ∧ v.dependent=false:=by
 have tags:=prepared_of_execution n B k A F x input s u ticks pc bits base size frontier dp
  data heapBase extent code room square constants bound prepared run
 intro i z
 cases h:u.scalarHeap (A+i.val*2^k+z.val) with
 | none => have impossible:=tags i z;rw [h] at impossible;cases impossible
 | some v => exact ⟨v,rfl,Option.some.inj (by simpa only [h,Option.map_some] using tags i z)⟩
end
end ExactFourierCircuits.UniformRecursiveRootExecution
