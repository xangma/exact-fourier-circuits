import DFTModelCacheColorPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorRebase
open UniformColoring
noncomputable section

def shiftEdge (A : ℕ) (e : Edge) : Edge :=
 ⟨A+e.left,A+e.right,fun h=>e.different (Nat.add_left_cancel h)⟩
def shiftedEdges {M : ℕ} (A : ℕ) (E : Fin M→Edge) : Fin M→Edge := fun i=>shiftEdge A (E i)

theorem conflict_shift (A : ℕ) (e f : Edge) :
 Conflict (shiftEdge A e) (shiftEdge A f) ↔ Conflict e f := by
 simp only [Conflict,Incident,shiftEdge,Nat.add_left_cancel_iff]

theorem earlier_shift {M : ℕ} (A : ℕ) (E : Fin M→Edge) (i : Fin M) (c : ℕ→ℕ) :
 earlierColors (shiftedEdges A E) i c=earlierColors E i c := by
 unfold earlierColors earlierNeighbors
 congr 1
 ext j
 simp only [Finset.mem_filter,Finset.mem_univ,true_and,shiftedEdges,conflict_shift]

/-- Translation by the same base is injective and preserves the chronological
indexed graph, hence every greedy choice including exhausted sentinel 11. -/
theorem greedy_shift {M : ℕ} (A : ℕ) (E : Fin M→Edge) (K j : ℕ) :
 greedy (shiftedEdges A E) K j=greedy E K j := by
 induction j with
 | zero=>rfl
 | succ j ih=>
   by_cases h:j<M
   · rw [greedy_next _ K j h,greedy_next _ K j h,ih,earlier_shift]
   · simp only [greedy,h,dite_false,ih]

theorem coloring_shift {M : ℕ} (A : ℕ) (E : Fin M→Edge) (d : ℕ) (i : Fin M) :
 coloring (shiftedEdges A E) d i=coloring E d i := by
 unfold coloring
 rw [greedy_shift]

/-- Degree can be transported back from physical to local coordinates without
any array allocation proportional to the physical base. -/
theorem degree_unshift {M : ℕ} (A : ℕ) (E : Fin M→Edge) (d : ℕ)
 (physical : DegreeBound (shiftedEdges A E) d) : DegreeBound E d := by
 intro v
 have same:incidentEdges (shiftedEdges A E) (A+v)=incidentEdges E v := by
  unfold incidentEdges
  apply Finset.filter_congr
  intro i _
  change Incident (shiftEdge A (E i)) (A+v) ↔ Incident (E i) v
  simp only [Incident,shiftEdge,Nat.add_left_cancel_iff]
 have bound:=physical (A+v)
 rw [same] at bound
 exact bound

end
end ExactFourierCircuits.DFTModelCacheColorRebase
