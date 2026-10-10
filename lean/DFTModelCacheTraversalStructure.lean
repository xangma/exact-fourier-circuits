import DFTModelCacheTraversalModel

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage UniformWorkspacePlanner
open UniformLocalRectangleDescriptors (Row emittedCount)
noncomputable section

abbrev StateT : Ty := p (Ty.a Task4) (p (Ty.a Record7) (Ty.a Record7))
abbrev FrameT : Ty := p StateT (p Task4 (p w (Ty.a Record7)))
def encode (s : ListState) : StateT.T :=
  (ofList (s.tasks.map taskEncode),(ofList s.nodes,ofList (s.rectangles.map rectangleEncode)))

def frameStack : Prog false FrameT (Ty.a Task4) := .comp (.atom .fst) (.atom .fst)
def frameNodes : Prog false FrameT (Ty.a Record7) := .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def frameRows : Prog false FrameT (Ty.a Record7) := .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def frameTask : Prog false FrameT Task4 := .comp (.atom .snd) (.atom .fst)
def frameSelected : Prog false FrameT w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def frameNewRows : Prog false FrameT (Ty.a Record7) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def frameWidth : Prog false FrameT w := .comp frameTask (.atom .fst)
def frameOffset : Prog false FrameT w := .comp frameTask (.comp (.atom .snd) (.atom .fst))
def frameParent : Prog false FrameT w := .comp frameTask (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def frameSide : Prog false FrameT w := .comp frameTask (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def frameId : Prog false FrameT w := .comp frameNodes (.atom .len)
def frameSplit : Prog false FrameT w := integer .div frameWidth (.atom (.lit 2))

def childLeft : Prog false FrameT Task4 :=
  .fork frameSplit (.fork frameOffset (.fork frameId (.atom (.lit 0))))
def childRight : Prog false FrameT Task4 :=
  .fork (integer .sub frameWidth frameSplit)
    (.fork (integer .add frameOffset frameSplit) (.fork frameId (.atom (.lit 1))))
def childrenCell : Prog false (p FrameT w) Task4 :=
  .ifz (.atom .snd) (.comp (.atom .fst) childLeft) (.comp (.atom .fst) childRight)
def emptyChildren : Prog false FrameT (Ty.a Task4) := .tab (.atom (.lit 0)) childrenCell
def twoChildren : Prog false FrameT (Ty.a Task4) := .tab (.atom (.lit 2)) childrenCell
def frameChildren : Prog false FrameT (Ty.a Task4) :=
  .ifz (integer .lt frameWidth (.atom (.lit 2)))
    (.ifz frameSelected emptyChildren twoChildren) emptyChildren

def tailLength : Prog false (Ty.a Task4) w := integer .sub (.atom .len) (.atom (.lit 1))
def tailCell : Prog false (p (Ty.a Task4) w) Task4 :=
  .comp (.fork (.atom .fst) (integer .add (.atom .snd) (.atom (.lit 1)))) (.atom .look)
def tail : Prog false (Ty.a Task4) (Ty.a Task4) := .tab tailLength tailCell

def nextStack : Prog false FrameT (Ty.a Task4) :=
  .comp (.fork frameChildren (.comp frameStack tail)) (append Task4)
def nextNode : Prog false FrameT Record7 :=
  .fork frameWidth (.fork frameOffset (.fork frameSelected (.fork frameParent
    (.fork frameSide (.fork (integer .mul (.atom (.lit 7)) (.comp frameRows (.atom .len)))
      (.comp frameNewRows (.atom .len)))))))
def nextNodes : Prog false FrameT (Ty.a Record7) :=
  .comp (.fork frameNodes (.comp nextNode (singleton Record7))) (append Record7)
def nextRows : Prog false FrameT (Ty.a Record7) :=
  .comp (.fork frameRows frameNewRows) (append Record7)
def finish : Prog false FrameT StateT := .fork nextStack (.fork nextNodes nextRows)

def frame (s : ListState) (t : Task) : FrameT.T :=
  (encode s,(taskEncode t,(selected t.width,ofList ((currentRows t).map rectangleEncode))))

attribute [local irreducible] append singleton Bill.tab

theorem ifz_value {s t : Ty} (q : Prog false s w) (f g : Prog false s t) (x : s.T) :
    (run (.ifz q f g) x).val=if (run q x).val=0 then (run f x).val else (run g x).val := by
  change (if (run q x).val=0 then run f x else run g x).val=_
  split_ifs <;> rfl

theorem emptyChildren_value (x : FrameT.T) :
    (run emptyChildren x).val=ofList [] := by
  change (Bill.tab 0 Task4.blank (fun j=>run childrenCell (x,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  refine tape_ext (Tape.tab 0 (fun j=>(run childrenCell (x,j)).val)) (ofList []) Task4.blank rfl ?_
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

theorem frameChildren_choice (s : ListState) (t : Task) :
    (run frameChildren (frame s t)).val=
      if t.width<2 ∨selected t.width=0 then ofList [] else
        (run twoChildren (frame s t)).val := by
  rw [frameChildren,ifz_value]
  have cmp : (run (integer .lt frameWidth (.atom (.lit 2))) (frame s t)).val=
      if t.width<2 then 1 else 0 := rfl
  rw [cmp]
  by_cases hv:t.width<2
  · simp only [hv,ite_true,Nat.one_ne_zero,ite_false,true_or,emptyChildren_value]
  · simp only [hv,ite_false,ite_true,false_or]
    rw [ifz_value]
    have sel : (run frameSelected (frame s t)).val=selected t.width := rfl
    rw [sel]
    by_cases hs:selected t.width=0 <;> simp only [hs,ite_true,ite_false,emptyChildren_value]

theorem frameChildren_value (s : ListState) (t : Task) :
    (run frameChildren (frame s t)).val=ofList ((children t s.nodes.length).map taskEncode) := by
  rw [frameChildren_choice]
  by_cases h:t.width<2 ∨selected t.width=0
  · simp only [h,ite_true,children,List.map_nil]
  · simp only [h,ite_false,children,List.map_cons,List.map_nil]
    rw [twoChildren]
    change (Bill.tab 2 Task4.blank (fun j=>run childrenCell (frame s t,j))).val=_
    rw [ModelEquivalenceInterpreter.tab_value]
    refine tape_ext (Tape.tab 2 (fun j=>(run childrenCell (frame s t,j)).val))
      (ofList [taskEncode ⟨t.width/2,t.offset,s.nodes.length,0⟩,
        taskEncode ⟨t.width-t.width/2,t.offset+t.width/2,s.nodes.length,1⟩]) Task4.blank rfl ?_
    intro j hj
    change j<2 at hj
    have cases:j=0∨j=1 := by omega
    rcases cases with rfl|rfl <;>
      simp [Tape.look,Tape.tab,ofList,childrenCell,childLeft,childRight,frameSplit,integer,
        frameWidth,frameOffset,frameTask,frameId,frameNodes,frame,encode,taskEncode,
        run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem tail_value (t : Tape Task4.T) :
    (run tail t).val=Tape.tab (t.len-1) (fun j=>t.look (j+1) Task4.blank) := by
  change (Bill.tab (t.len-1) Task4.blank (fun j=>run tailCell (t,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem tail_list (t : Task) (ts : List Task) :
    (run tail (ofList ((t::ts).map taskEncode))).val=ofList (ts.map taskEncode) := by
  rw [tail_value]
  apply tape_ext _ _ Task4.blank (by simp [Tape.tab,ofList])
  intro j hj
  rw [Tape.look_of_lt _ _ hj]
  change (ofList ((t::ts).map taskEncode)).look (j+1) Task4.blank=
    (ofList (ts.map taskEncode)).look j Task4.blank
  rw [ofList_look,ofList_look]
  simp

theorem nextNode_value (s : ListState) (t : Task) :
    (run nextNode (frame s t)).val=nodeEncode ⟨t,7*s.rectangles.length⟩ := by
  change (t.width,(t.offset,(selected t.width,(t.parent,(t.side,
    (7*(s.rectangles.map rectangleEncode).length,((currentRows t).map rectangleEncode).length))))))=_
  simp only [List.length_map,currentRows_length]
  rfl

theorem nextStack_value (t : Task) (ts : List Task) (ns : List Record7.T) (rs : List Row) :
    (run nextStack (frame ⟨t::ts,ns,rs⟩ t)).val=
      ofList ((children t ns.length++ts).map taskEncode) := by
  change (run (append Task4) ((run frameChildren (frame ⟨t::ts,ns,rs⟩ t)).val,
    (run tail (ofList ((t::ts).map taskEncode))).val)).val=_
  rw [frameChildren_value,tail_list,append_value,append_lists,List.map_append]

theorem nextNodes_value (s : ListState) (t : Task) :
    (run nextNodes (frame s t)).val=ofList (s.nodes++[nodeEncode ⟨t,7*s.rectangles.length⟩]) := by
  change (run (append Record7) (ofList s.nodes,
    (run (singleton Record7) (run nextNode (frame s t)).val).val)).val=_
  rw [nextNode_value,singleton_run,append_value]
  change appendValue Record7 (ofList s.nodes) (Tape.tab 1 (fun _=>nodeEncode ⟨t,7*s.rectangles.length⟩))=_
  have one:Tape.tab 1 (fun _=>nodeEncode ⟨t,7*s.rectangles.length⟩)=
      ofList [nodeEncode ⟨t,7*s.rectangles.length⟩] := by
    refine tape_ext (Tape.tab 1 (fun _=>nodeEncode ⟨t,7*s.rectangles.length⟩))
      (ofList [nodeEncode ⟨t,7*s.rectangles.length⟩]) Record7.blank rfl ?_
    intro j hj
    have hj0:j=0 := by change j<1 at hj;omega
    subst j
    rfl
  rw [one,append_lists]

theorem nextRows_value (s : ListState) (t : Task) :
    (run nextRows (frame s t)).val=ofList ((s.rectangles++currentRows t).map rectangleEncode) := by
  change (run (append Record7) (ofList (s.rectangles.map rectangleEncode),
    ofList ((currentRows t).map rectangleEncode))).val=_
  rw [append_value,append_lists,List.map_append]

theorem finish_value (t : Task) (ts : List Task) (ns : List Record7.T) (rs : List Row) :
    (run finish (frame ⟨t::ts,ns,rs⟩ t)).val=encode (advance ⟨t::ts,ns,rs⟩) := by
  change ((run nextStack (frame ⟨t::ts,ns,rs⟩ t)).val,
    ((run nextNodes (frame ⟨t::ts,ns,rs⟩ t)).val,
      (run nextRows (frame ⟨t::ts,ns,rs⟩ t)).val))=_
  rw [nextStack_value,nextNodes_value,nextRows_value]
  rfl

end
end ExactFourierCircuits.DFTModelCacheTraversal
