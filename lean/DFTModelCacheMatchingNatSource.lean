import DFTModelCacheMatchingNatInitialization
import DFTModelCacheMatchingNatFits

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl UniformMatchingAxisTableMachine
noncomputable section

/-- The selected row tape supplies only actual endpoints. Its coefficient field
is not copied or constrained by this Nat-only client. -/
structure Rows {M : ℕ} (E : Fin M→UniformColoring.Edge) (z : Tape Row.T) : Prop where
  length : z.len=M
  endpoints : ∀i : Fin M,(z.look i.val (0,(0,0))).1=(E i).left ∧
    (z.look i.val (0,(0,0))).2.1=(E i).right

def sourceState (r : ℕ) (z : Tape Row.T) : UniformMachine.State  :=
  { UniformMachine.initial with
    natReg := registerValue r z.len
    natHeap := fun j => ModelEquivalenceInterpreter.decodeNatCell (heapValue z j)}

theorem initial_represents (r : ℕ) (z : Tape Row.T) :
    Represents (initialValue r z) (sourceState r z)  :=  by
  refine ⟨rfl,?_,?_⟩
  · intro j hj
    change (Tape.tab 862 (registerValue r z.len)).look j 0=registerValue r z.len j
    change j<862 at hj
    rw [Tape.look_of_lt _ _ hj]
    rfl
  · intro j hj
    change ModelEquivalenceInterpreter.decodeNatCell
      ((Tape.tab (heapSize r z.len) (heapValue z)).look j (0,0))=_
    change j<heapSize r z.len at hj
    rw [Tape.look_of_lt _ _ hj]
    rfl

theorem initialized_represents (r : ℕ) (z : Tape Row.T) :
    Represents (run initializeProgram (r,z)).val (sourceState r z)  :=  by
  rw [initialize_value];exact initial_represents r z

theorem source_header (r : ℕ) (z : Tape Row.T) :
    Header r z.len 0 (P z.len) (W r z.len) (U r z.len) (A r z.len) (sourceState r z)  :=  by
  constructor <;> simp [sourceState,registerValue]

theorem source_edges {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) : Edges E 0 (sourceState r z)  :=  by
  intro i
  have hi:i.val<z.len  :=  rows.length.symm ▸ i.isLt
  have left :=  (rows.endpoints i).1
  have right :=  (rows.endpoints i).2
  have divleft:(3*i.val)/3=i.val  :=  by omega
  have divright:(3*i.val+1)/3=i.val  :=  by omega
  simp only [sourceState,heapValue,endpointValue,ModelEquivalenceInterpreter.decodeNatCell,
    Nat.zero_add,show 3*i.val<3*z.len from by omega,
    show 3*i.val+1<3*z.len from by omega,ite_true,
    show 3*i.val%3=0 from by omega,show (3*i.val+1)%3=1 from by omega,
    divleft,divright,ite_false,
    Nat.one_ne_zero,left,right]
  exact ⟨trivial,trivial⟩

theorem register_bound (r M j : ℕ) : registerValue r M j≤wordBound r M  :=  by
  unfold registerValue wordBound A U W P
  split_ifs <;> omega

theorem endpoint_bound {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) (hr : InRange r E)
    (j : ℕ) (hj : j<3*z.len) : endpointValue z j≤r  :=  by
  have index:j/3<M  :=  by rw [←rows.length];omega
  have ends := rows.endpoints ⟨j/3,index⟩
  have range := hr ⟨j/3,index⟩
  dsimp only at ends range
  unfold endpointValue
  split_ifs
  · rw [ends.1];exact Nat.le_of_lt range.1
  · rw [ends.2];exact Nat.le_of_lt range.2
  · exact Nat.zero_le _

theorem source_wordBound {M : ℕ} (r : ℕ) (z : Tape Row.T)
    (E : Fin M→UniformColoring.Edge) (rows : Rows E z) (hr : InRange r E) :
    UniformMachine.WordBound (wordBound r z.len) (sourceState r z)  :=  by
  refine ⟨Nat.zero_le _,register_bound r z.len,?_,?_,?_,?_⟩
  · intro j value present
    change ModelEquivalenceInterpreter.decodeNatCell (heapValue z j)=some value at present
    by_cases hj:j<3*z.len
    · have hv := endpoint_bound r z E rows hr j hj
      simp only [heapValue,hj,ite_true,ModelEquivalenceInterpreter.decodeNatCell,
        Nat.one_ne_zero,ite_false,Option.some.injEq] at present
      subst value
      unfold wordBound A U W P
      exact ⟨by omega,by omega⟩
    · simp only [heapValue,hj,ite_false,ModelEquivalenceInterpreter.decodeNatCell,ite_true] at present
      cases present
  · intro _ _ impossible;cases impossible
  · intro _ _ impossible;cases impossible
  · intro _ impossible;cases impossible

/-- The SAME literal native Matching55 run starts from the charged initializer's
endpoint projection, and produces the ordered pairs followed by ascending unused
indices. No permutation is an input to this theorem. -/
theorem native_execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hm : Matching E) (hr : InRange r E) : ∃u,
    UniformMachine.BoundedExecution UniformMatchingAxisTableMachine.program n x
      (wordBound r z.len) (sourceState r z) (runtime r M) u ∧
    u.pc=54 ∧ Bank (P z.len) (ordered r E) u ∧
    Bank (W r z.len) (widths r M) u ∧ AxisRow (A r z.len) r M (W r z.len) (P z.len) u  :=  by
  obtain ⟨u,actual,pc,_,permutation,widths,_,axis,_,_,_⟩ :=
    UniformMatchingAxisTableMachine.execution r M 0 (P z.len) (W r z.len)
      (U r z.len) (A r z.len) (wordBound r z.len) n x E (sourceState r z)
      (by simpa only [rows.length] using source_header r z) rfl
      (source_edges r z E rows) hm hr
      (by simp only [P,rows.length];omega) (by unfold W;omega)
      (by unfold U;omega) (by unfold A;omega)
      (by unfold wordBound;omega) (by unfold wordBound;omega)
      (source_wordBound r z E rows hr)
  exact ⟨u,actual,pc,permutation,widths,axis⟩

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
