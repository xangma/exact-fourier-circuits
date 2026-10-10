import DFTModelCacheColorInitialization
import DFTModelCacheMatchingNatSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
open UniformMatchingAxisTableMachine (InRange)
noncomputable section
abbrev Rows := @DFTModelCacheMatchingNat.Rows

def sourceState (_r : ℕ) (z : Tape Row.T) : UniformMachine.State  :=
  { UniformMachine.initial with
    natReg := registerValue z.len
    natHeap := fun j => ModelEquivalenceInterpreter.decodeNatCell (DFTModelCacheMatchingNat.heapValue z j)}

theorem initial_represents (r : ℕ) (z : Tape Row.T) :
    Represents (initialValue r z) (sourceState r z)  :=  by
  refine ⟨rfl,?_,?_⟩
  · intro j hj
    change (Tape.tab 824 (registerValue z.len)).look j 0=registerValue z.len j
    change j<824 at hj
    rw [Tape.look_of_lt _ _ hj]
    rfl
  · intro j hj
    change ModelEquivalenceInterpreter.decodeNatCell
      ((Tape.tab (H r z.len) (DFTModelCacheMatchingNat.heapValue z)).look j (0,0))=_
    change j<H r z.len at hj
    rw [Tape.look_of_lt _ _ hj]
    rfl

theorem initialized_represents (r : ℕ) (z : Tape Row.T) :
    Represents (run initializeProgram (r,z)).val (sourceState r z)  :=  by
  rw [initialize_value];exact initial_represents r z

theorem source_header (r : ℕ) (z : Tape Row.T) :
    UniformGreedyColorMachine.Header z.len 0 (C z.len) (U z.len) (sourceState r z)  :=  by
  constructor <;> simp [sourceState,registerValue]

theorem source_edges {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) : UniformGreedyColorMachine.Edges E 0 (sourceState r z)  :=  by
  intro i
  have hi:i.val<z.len  :=  rows.length.symm ▸ i.isLt
  have left :=  (rows.endpoints i).1
  have right :=  (rows.endpoints i).2
  have divleft:(3*i.val)/3=i.val  :=  by omega
  have divright:(3*i.val+1)/3=i.val  :=  by omega
  simp only [sourceState,DFTModelCacheMatchingNat.heapValue,DFTModelCacheMatchingNat.endpointValue,ModelEquivalenceInterpreter.decodeNatCell,
    Nat.zero_add,show 3*i.val<3*z.len from by omega,
    show 3*i.val+1<3*z.len from by omega,ite_true,
    show 3*i.val%3=0 from by omega,show (3*i.val+1)%3=1 from by omega,
    divleft,divright,ite_false,
    Nat.one_ne_zero,left,right]
  exact ⟨trivial,trivial⟩

theorem register_bound (r M j : ℕ) : registerValue M j≤B r M  :=  by
  unfold registerValue B C U
  split_ifs <;> omega

theorem endpoint_bound {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) (hr : InRange r E)
    (j : ℕ) (hj : j<3*z.len) : DFTModelCacheMatchingNat.endpointValue z j≤r  :=  by
  have index:j/3<M  :=  by rw [←rows.length];omega
  have ends := rows.endpoints ⟨j/3,index⟩
  have range := hr ⟨j/3,index⟩
  dsimp only at ends range
  unfold DFTModelCacheMatchingNat.endpointValue
  split_ifs
  · rw [ends.1];exact Nat.le_of_lt range.1
  · rw [ends.2];exact Nat.le_of_lt range.2
  · exact Nat.zero_le _

theorem source_wordBound {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) (hr : InRange r E) :
    UniformMachine.WordBound (B r z.len) (sourceState r z)  :=  by
  refine ⟨Nat.zero_le _,register_bound r z.len,?_,?_,?_,?_⟩
  · intro j value present
    change ModelEquivalenceInterpreter.decodeNatCell (DFTModelCacheMatchingNat.heapValue z j)=some value at present
    by_cases hj:j<3*z.len
    · have hv := endpoint_bound r z E rows hr j hj
      simp only [DFTModelCacheMatchingNat.heapValue,hj,ite_true,ModelEquivalenceInterpreter.decodeNatCell,
        Nat.one_ne_zero,ite_false,Option.some.injEq] at present
      subst value
      unfold B U
      exact ⟨by omega,by omega⟩
    · simp only [DFTModelCacheMatchingNat.heapValue,hj,ite_false,ModelEquivalenceInterpreter.decodeNatCell,ite_true] at present
      cases present
  · intro _ _ impossible;cases impossible
  · intro _ _ impossible;cases impossible
  · intro _ impossible;cases impossible

/-- Native51 starts from the charged fresh initializer. No color, fuel,
prepared heap, or degree certificate is an execution input. -/
theorem native_execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hr : InRange r E) : ∃t u,
    t≤UniformGreedyColorMachine.runtimeBudget z.len ∧
    UniformMachine.BoundedExecution UniformGreedyColorMachine.program n x
      (B r z.len) (sourceState r z) t u ∧ u.pc=50 ∧
    UniformGreedyColorMachine.Colors E (C z.len) M u := by
  obtain ⟨t,u,time,actual,pc,_,colors,_,_,_,_⟩ :=
    UniformGreedyColorMachine.execution M 0 (C z.len) (U z.len) (B r z.len) n x
      (sourceState r z) E (by simpa only [rows.length] using source_header r z)
      rfl (source_edges r z E rows)
      (by unfold B;omega) (by unfold C;rw [rows.length];omega)
      (by unfold C U;rw [rows.length];omega) (by unfold B U;omega)
      (source_wordBound r z E rows hr)
  exact ⟨t,u,by simpa only [rows.length] using time,actual,pc,colors⟩

end
end ExactFourierCircuits.DFTModelCacheColor
