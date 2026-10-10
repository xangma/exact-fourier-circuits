import DFTModelCacheTraversalValidity
import DFTModelCacheDescriptorNode

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage UniformWorkspacePlanner
noncomputable section

abbrev Input : Ty := p w w
abbrev Output : Ty := p (Ty.a Record7) (Ty.a Record7)
def head : Prog false StateT Task4 :=
  .comp (.fork (.atom .fst) (.atom (.lit 0))) (.atom .look)
def headArg : Prog false StateT (p w w) :=
  .comp head (.fork (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
def attach : Prog false StateT FrameT :=
  .fork (.atom .id) (.fork head (.comp headArg DFTModelCacheDescriptor.node))
def step : Prog false StateT StateT :=
  .ifz (.comp (.atom .fst) (.atom .len)) (.atom .id) (.comp attach finish)
def root : Prog false Input Task4 :=
  .fork (.atom .fst) (.fork (.atom .snd) (.fork (.atom (.lit 0)) (.atom (.lit 0))))
def zeroRecord {s : Ty} : Prog false s Record7 :=
  .fork (.atom (.lit 0))
    (.fork (.atom (.lit 0))
      (.fork (.atom (.lit 0))
        (.fork (.atom (.lit 0))
          (.fork (.atom (.lit 0))
            (.fork (.atom (.lit 0)) (.atom (.lit 0)))))))
def emptyRecords : Prog false Input (Ty.a Record7) := .tab (.atom (.lit 0)) zeroRecord
def start : Prog false Input StateT :=
  .fork (.comp root (singleton Task4)) (.fork emptyRecords emptyRecords)
def count : Prog false Input w := integer .add
  (integer .mul (.atom (.lit 2)) (.atom .fst)) (.atom (.lit 1))
def body : Prog false (p Input (p w StateT)) StateT :=
  .comp (.comp (.atom .snd) (.atom .snd)) step
/-- A single closed fixed-fuel stack machine, from raw runtime width and offset. -/
def whole : Prog false Input StateT := .loop count start body
def program : Prog false Input Output := .comp whole (.atom .snd)

attribute [local irreducible] DFTModelCacheDescriptor.node finish singleton Bill.tab

theorem head_value (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run head (encode ⟨t::ts,ns,rs⟩)).val=taskEncode t := rfl

theorem attach_value (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run attach (encode ⟨t::ts,ns,rs⟩)).val=frame ⟨t::ts,ns,rs⟩ t := by
  change (encode ⟨t::ts,ns,rs⟩,((run head (encode ⟨t::ts,ns,rs⟩)).val,
    (run DFTModelCacheDescriptor.node (run headArg (encode ⟨t::ts,ns,rs⟩)).val).val))=_
  rw [head_value]
  have args:(run headArg (encode ⟨t::ts,ns,rs⟩)).val=(t.width,t.offset) := rfl
  rw [args,DFTModelCacheDescriptor.node_value]
  rfl

theorem step_value (s : ListState) : (run step (encode s)).val=encode (advance s) := by
  cases s with
  | mk tasks ns rs =>
    cases tasks with
    | nil =>
      rw [step,ifz_value]
      rfl
    | cons t ts =>
      rw [step,ifz_value]
      change (if (t::ts).length=0 then encode ⟨t::ts,ns,rs⟩ else
        (run finish (run attach (encode ⟨t::ts,ns,rs⟩)).val).val)=_
      rw [ite_eq_right (by simp : (t::ts).length≠0),attach_value,finish_value]

theorem emptyRecords_value (r o : ℕ) : (run emptyRecords (r,o)).val=ofList [] := by
  change (Bill.tab 0 Record7.blank (fun j=>run (zeroRecord (s:=p Input w)) ((r,o),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  refine tape_ext (Tape.tab 0 (fun j=>(run (zeroRecord (s:=p Input w)) ((r,o),j)).val))
    (ofList []) Record7.blank rfl ?_
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

theorem start_value (r o : ℕ) : (run start (r,o)).val=encode (initial r o) := by
  change ((run (singleton Task4) (r,(o,(0,0)))).val,
    ((run emptyRecords (r,o)).val,(run emptyRecords (r,o)).val))=_
  rw [singleton_run,emptyRecords_value]
  refine Prod.ext ?_ rfl
  refine tape_ext (Tape.tab 1 (fun _=>(r,(o,(0,0)))))
    (ofList [taskEncode ⟨r,o,0,0⟩]) Task4.blank rfl ?_
  intro j hj
  have hz:j=0 := by change j<1 at hj;omega
  subst j
  rfl

theorem count_value (r o : ℕ) : (run count (r,o)).val=2*r+1 := rfl

def ticks (r o j : ℕ) : Bill StateT.T :=
  Bill.steps (run start (r,o)).val (fun i s=>run body ((r,o),(i,s))) j

theorem execute_succ_right (j : ℕ) (s : ListState) :
    execute (j+1) s=advance (execute j s) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => exact ih (advance s)

theorem ticks_value (r o j : ℕ) : (ticks r o j).val=encode (execute j (initial r o)) := by
  induction j with
  | zero => exact start_value r o
  | succ j ih =>
    change (run step (ticks r o j).val).val=_
    rw [ih,step_value,←execute_succ_right]

theorem loop_value {s t : Ty} (n : Prog false s w) (init : Prog false s t)
    (b : Prog false (p s (p w t)) t) (x : s.T) :
    (run (.loop n init b) x).val=
      (Bill.steps (run init x).val (fun i a=>run b (x,(i,a))) (run n x).val).val := rfl

attribute [local irreducible] step start body count

theorem whole_value (r o : ℕ) :
    (run whole (r,o)).val=encode (execute (2*r+1) (initial r o)) := by
  rw [whole,loop_value,count_value]
  exact ticks_value r o (2*r+1)

/-- Exact native preorder node directory and every native ragged rectangle. -/
theorem program_value (r o : ℕ) :
    (run program (r,o)).val=
      (ofList ((walk (2*r+1) 0 0 [⟨r,o,0,0⟩]).1.map nodeEncode),
        ofList (((ofPlan (UniformBalancedToeplitz.plan r) o).rectangles).map rectangleEncode)) := by
  change (run whole (r,o)).val.2=_
  rw [whole_value,initial_walk]
  rfl

theorem program_lengths (r o : ℕ) :
    (run program (r,o)).val.1.len≤2*r+1 ∧ (run program (r,o)).val.2.len≤r^2 := by
  rw [program_value]
  exact ⟨by simpa only [ofList,List.length_map] using walk_length (2*r+1) 0 0 [⟨r,o,0,0⟩],
    by simpa only [ofList,List.length_map] using ofPlan_rectangles_length (UniformBalancedToeplitz.plan r) o⟩

end
end ExactFourierCircuits.DFTModelCacheTraversal
