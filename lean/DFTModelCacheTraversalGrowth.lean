import DFTModelCacheTraversalModel

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage UniformWorkspacePlanner
noncomputable section

structure Growth (r o i : ℕ) (s : ListState) : Prop where
  stack : s.tasks.length ≤ i+1
  nodes : s.nodes.length ≤ i
  rectangles : s.rectangles.length ≤ i*r^2
  tasks : ∀t ∈ s.tasks,t.width ≤ r  ∧  t.offset+t.width ≤ o+r  ∧  t.parent ≤ i  ∧  t.side ≤ 1

theorem children_length (t : Task) (id : ℕ) : (children t id).length ≤ 2 := by
  unfold children
  split <;> simp

theorem currentRows_bound (t : Task) : (currentRows t).length ≤ t.width^2 := by
  have h:=congrArg List.length (task_decomposition t 0)
  have hb:=ofPlan_rectangles_length (UniformBalancedToeplitz.plan t.width) t.offset
  rw [List.length_append] at h
  omega

theorem advance_growth (r o i : ℕ) (s : ListState) (h : Growth r o i s) :
    Growth r o (i+1) (advance s) := by
  cases s with
  | mk tasks ns rs =>
    cases tasks with
    | nil =>
      refine ⟨by simp [advance],
        by simpa [advance] using h.nodes.trans (Nat.le_succ _),?_,?_⟩
      · change rs.length ≤ (i+1)*r^2
        exact h.rectangles.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
      · intro t ht
        simp [advance] at ht
    | cons t ts =>
      have ht:=h.tasks t (by simp)
      have nr:(currentRows t).length ≤ r^2 :=
        (currentRows_bound t).trans (Nat.pow_le_pow_left ht.1 2)
      have cl:=children_length t ns.length
      refine ⟨?_,?_,?_,?_⟩
      · change (children t ns.length++ts).length ≤ i+1+1
        rw [List.length_append]
        have hs:=h.stack
        change ts.length+1 ≤ i+1 at hs
        omega
      · change (ns++[nodeEncode ⟨t,7*rs.length⟩]).length ≤ i+1
        simp only [List.length_append,List.length_singleton]
        exact Nat.add_le_add_right h.nodes 1
      · change (rs++currentRows t).length ≤ (i+1)*r^2
        rw [List.length_append,Nat.add_mul,Nat.one_mul]
        exact Nat.add_le_add h.rectangles nr
      · intro u hu
        change u ∈ children t ns.length++ts at hu
        rcases List.mem_append.mp hu with hc|hu
        · have bound:=children_bound t ns.length u hc
          exact ⟨bound.1.trans ht.1,bound.2.1.trans ht.2.1,
            by rw [bound.2.2.1];exact h.nodes.trans (Nat.le_succ _),bound.2.2.2⟩
        · have old:=h.tasks u (List.mem_cons_of_mem t hu)
          exact ⟨old.1,old.2.1,old.2.2.1.trans (Nat.le_succ _),old.2.2.2⟩

theorem execute_growth (r o i : ℕ) : Growth r o i (execute i (initial r o)) := by
  induction i with
  | zero =>
    refine ⟨by simp [execute,initial],by simp [execute,initial],by simp [execute,initial],?_⟩
    intro t ht
    simp only [execute,initial,List.mem_singleton] at ht
    subst t
    simp
  | succ i ih =>
    have eq:execute (i+1) (initial r o)=advance (execute i (initial r o)) := by
      have general : ∀j s,execute (j+1) s=advance (execute j s) := by
        intro j
        induction j with
        | zero => intro s;rfl
        | succ j hj => intro s;exact hj (advance s)
      exact general i _
    rw [eq]
    exact advance_growth r o i _ ih

end
end ExactFourierCircuits.DFTModelCacheTraversal
