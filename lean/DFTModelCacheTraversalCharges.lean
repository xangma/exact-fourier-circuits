import DFTModelCacheTraversalStructure
import DFTModelCacheTraversalGrowth

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] Bill.tab append singleton

theorem childrenCell_work (x : FrameT.T) (j : ℕ) :
    (run childrenCell (x,j)).work≤150 := by
  simp [childrenCell,childLeft,childRight,frameSplit,integer,frameWidth,frameOffset,
    frameTask,frameId,frameNodes,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  split_ifs <;> norm_num

theorem childrenTable_work (x : FrameT.T) (n : ℕ) :
    (Bill.tab n Task4.blank (fun j=>run childrenCell (x,j))).work≤154*n+2 := by
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum : (∑j∈Finset.range n,(run childrenCell (x,j)).work)≤150*n := by
    calc
      _≤∑_j∈Finset.range n,150 := Finset.sum_le_sum (fun j _=>childrenCell_work x j)
      _=_ := by simp [Nat.mul_comm]
  omega

theorem frameChildren_work (x : FrameT.T) : (run frameChildren x).work≤500 := by
  have h0:=childrenTable_work x 0
  have h2:=childrenTable_work x 2
  simp only [frameChildren,emptyChildren,twoChildren,integer,frameWidth,frameTask,
    frameSelected,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay] at *
  by_cases hv:x.2.1.1<2 <;> by_cases hs:x.2.2.1=0 <;>
    simp only [hv,hs,ite_true,ite_false,Nat.one_ne_zero] <;> omega

theorem tailCell_run (x : Tape Task4.T) (j : ℕ) :
    run tailCell (x,j)=⟨x.look (j+1) Task4.blank,9,j+1,True⟩ := by
  simp [tailCell,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem tail_work (x : Tape Task4.T) : (run tail x).work≤13*x.len+8 := by
  change 5+(Bill.tab (x.len-1) Task4.blank (fun j=>run tailCell (x,j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  change 5+(2+4*(x.len-1)+∑j∈Finset.range (x.len-1),9)+1≤_
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem nextNode_work (x : FrameT.T) : (run nextNode x).work≤100 := by
  simp [nextNode,frameWidth,frameOffset,frameSelected,frameParent,frameSide,frameTask,
    frameRows,frameNewRows,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem ofList_length {α : Type} (xs : List α) : (ofList xs).len=xs.length := rfl

theorem comp_work {s t u : Ty} (f : Prog false s t) (g : Prog false t u) (x : s.T) :
    (run (.comp f g) x).work=(run f x).work+(run g (run f x).val).work+1 := rfl

theorem fork_work {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).work=(run f x).work+(run g x).work+1 := rfl

attribute [local irreducible] frameChildren tail nextNode nextStack nextNodes nextRows

theorem nextStack_work (t : UniformLocalCacheTreeMachine.Task)
    (ts : List UniformLocalCacheTreeMachine.Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run nextStack (frame ⟨t::ts,ns,rs⟩ t)).work≤42*(t::ts).length+600 := by
  let x:=frame ⟨t::ts,ns,rs⟩ t
  have hc:=frameChildren_work x
  have ht:=tail_work (ofList ((t::ts).map taskEncode))
  have ha:=append_work Task4 (run frameChildren x).val
    (run tail (ofList ((t::ts).map taskEncode))).val
  have lc:(run frameChildren x).val.len≤2 := by
    rw [frameChildren_value]
    simpa only [ofList,List.length_map] using children_length t ns.length
  have lt:(run tail (ofList ((t::ts).map taskEncode))).val.len≤(t::ts).length := by
    rw [tail_value]
    simp only [Tape.tab,ofList,List.length_map]
    omega
  rw [nextStack,comp_work,fork_work,comp_work]
  have fv:(run frameStack x).val=ofList ((t::ts).map taskEncode) := rfl
  have fw:(run frameStack x).work=3 := rfl
  rw [fv,fw]
  have value:(run (.fork frameChildren (.comp frameStack tail)) x).val=
    ((run frameChildren x).val,(run tail (ofList ((t::ts).map taskEncode))).val) := rfl
  rw [value]
  dsimp only [x] at *
  rw [ofList_length,List.length_map] at ht
  omega

theorem nextNodes_work (s : ListState) (t : UniformLocalCacheTreeMachine.Task) :
    (run nextNodes (frame s t)).work≤29*s.nodes.length+200 := by
  let x:=frame s t
  have hn:=nextNode_work x
  have ha:=append_work Record7 (ofList s.nodes)
    (run (singleton Record7) (run nextNode x).val).val
  have hs:=singleton_run Record7 (run nextNode x).val
  have lens:(run (singleton Record7) (run nextNode x).val).val.len=1 := by rw [hs];rfl
  rw [nextNodes,comp_work,fork_work,comp_work]
  have fw:(run frameNodes x).work=5 := rfl
  have fv:(run frameNodes x).val=ofList s.nodes := rfl
  have value:(run (.fork frameNodes (.comp nextNode (singleton Record7))) x).val=
      (ofList s.nodes,(run (singleton Record7) (run nextNode x).val).val) := rfl
  rw [fw,value,hs]

  change (run (append Record7) (ofList s.nodes,
    (run (singleton Record7) (run nextNode x).val).val)).work≤
      29*(s.nodes.length+(run (singleton Record7) (run nextNode x).val).val.len)+12 at ha
  rw [lens] at ha
  rw [hs] at ha
  dsimp only [Bill.work,Bill.val,x] at *
  omega

theorem nextRows_work (s : ListState) (t : UniformLocalCacheTreeMachine.Task) :
    (run nextRows (frame s t)).work≤
      29*(s.rectangles.length+(UniformLocalCacheTreeCoverage.currentRows t).length)+24 := by
  have ha:=append_work Record7 (ofList (s.rectangles.map rectangleEncode))
    (ofList ((UniformLocalCacheTreeCoverage.currentRows t).map rectangleEncode))
  rw [nextRows,comp_work,fork_work]
  have fw:(run frameRows (frame s t)).work=5 := rfl
  have gw:(run frameNewRows (frame s t)).work=5 := rfl
  have value:(run (.fork frameRows frameNewRows) (frame s t)).val=
      (ofList (s.rectangles.map rectangleEncode),
        ofList ((UniformLocalCacheTreeCoverage.currentRows t).map rectangleEncode)) := rfl
  rw [fw,gw,value]
  rw [ofList_length,ofList_length,List.length_map,List.length_map] at ha
  omega

theorem finish_work (t : UniformLocalCacheTreeMachine.Task)
    (ts : List UniformLocalCacheTreeMachine.Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run finish (frame ⟨t::ts,ns,rs⟩ t)).work≤
      42*(t::ts).length+29*ns.length+
        29*(rs.length+(UniformLocalCacheTreeCoverage.currentRows t).length)+1000 := by
  have hs:=nextStack_work t ts ns rs
  have hn:=nextNodes_work ⟨t::ts,ns,rs⟩ t
  have hr:=nextRows_work ⟨t::ts,ns,rs⟩ t
  rw [finish,fork_work,fork_work]
  dsimp only [ListState.nodes,ListState.rectangles] at hn hr
  omega

end
end ExactFourierCircuits.DFTModelCacheTraversal
