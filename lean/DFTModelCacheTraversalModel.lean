import DFTModelCacheTraversalTape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage UniformWorkspacePlanner
open UniformLocalRectangleDescriptors (Row emittedCount)
noncomputable section

abbrev Task4 : Ty := p w (p w (p w w))
abbrev Record7 : Ty := p w (p w (p w (p w (p w (p w w)))))
def taskEncode (t : Task) : Task4.T := (t.width,(t.offset,(t.parent,t.side)))
def rectangleEncode (q : Row) : Record7.T :=
  (q.width,(q.offset,(q.a,(q.e,(q.split,(q.i0,q.j0))))))
def nodeEncode (q : Visit) : Record7.T :=
  (q.task.width,(q.task.offset,(selected q.task.width,
    (q.task.parent,(q.task.side,(q.rectangleBase,emittedCount q.task.width))))))

structure ListState where
  tasks : List Task
  nodes : List Record7.T
  rectangles : List Row

/-- List reference for the charged stack update. It is not an input to the code. -/
def advance (s : ListState) : ListState :=
  match s.tasks with
  | [] => s
  | t::ts =>
    ⟨children t s.nodes.length++ts,
      s.nodes++[nodeEncode ⟨t,7*s.rectangles.length⟩],s.rectangles++currentRows t⟩

def execute : ℕ → ListState → ListState
  | 0,s => s
  | f+1,s => execute f (advance s)

def initial (r o : ℕ) : ListState := ⟨[⟨r,o,0,0⟩],[],[]⟩

theorem walk_nil (fuel k c : ℕ) : walk fuel k c []=([],[]) := by
  cases fuel <;> rfl

theorem execute_walk (fuel : ℕ) (tasks : List Task) (ns : List Record7.T) (rs : List Row) :
    execute fuel ⟨tasks,ns,rs⟩=
      ⟨(walk fuel ns.length (7*rs.length) tasks).2,
        ns++(walk fuel ns.length (7*rs.length) tasks).1.map nodeEncode,
        rs++visitedRows (walk fuel ns.length (7*rs.length) tasks).1⟩ := by
  induction fuel generalizing tasks ns rs with
  | zero => simp [execute,walk,visitedRows]
  | succ fuel ih =>
    cases tasks with
    | nil =>
      rw [execute]
      change execute fuel ⟨[],ns,rs⟩=_
      rw [ih]
      simp [walk,walk_nil,visitedRows]
    | cons t ts =>
      rw [execute]
      change execute fuel
        ⟨children t ns.length++ts,ns++[nodeEncode ⟨t,7*rs.length⟩],rs++currentRows t⟩=_
      rw [ih]
      simp only [walk,List.length_append,List.length_singleton,currentRows_length,
        Nat.mul_add,List.map_cons,visitedRows,List.flatten_cons,List.append_assoc,
        List.singleton_append]

theorem initial_walk (r o : ℕ) :
    execute (2*r+1) (initial r o)=
      ⟨[],(walk (2*r+1) 0 0 [⟨r,o,0,0⟩]).1.map nodeEncode,
        (ofPlan (UniformBalancedToeplitz.plan r) o).rectangles⟩ := by
  have done:=walk_finished (2*r+1) 0 0 [⟨r,o,0,0⟩] (by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      using taskWeight_root r o)
  rw [initial,execute_walk]
  simp only [List.length_nil,Nat.mul_zero,List.nil_append,done,root_walk_rows]

theorem initial_nodes_bound (r o : ℕ) :
    (execute (2*r+1) (initial r o)).nodes.length≤2*r+1 := by
  rw [initial_walk]
  simpa only [List.length_map] using walk_length (2*r+1) 0 0 [⟨r,o,0,0⟩]

theorem initial_rectangles_bound (r o : ℕ) :
    (execute (2*r+1) (initial r o)).rectangles.length≤r^2 := by
  rw [initial_walk]
  exact ofPlan_rectangles_length _ _

end
end ExactFourierCircuits.DFTModelCacheTraversal
