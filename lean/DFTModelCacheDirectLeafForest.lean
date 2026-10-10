import DFTModelCacheDirectLeafOrientations
import DFTModelCacheSpectrumForestProvenance
import UniformDirectLeafForestModel

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine
noncomputable section

abbrev NodeInput := p DFTModelCacheTraversal.Record7 w
abbrev ForestSeed := p Input DFTModelCacheTraversal.Output
abbrev ForestCell := p ForestSeed w
abbrev ForestOutput := p DFTModelCacheTraversal.Output (Ty.a Orientations)

def nodeArgument : Prog false NodeInput Input :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))) (.atom .snd))
def emptyNode : Prog false NodeInput Orientations :=
  .fork (.tab (.atom (.lit 0)) zeroRecord) (.tab (.atom (.lit 0)) zeroRecord)
def leafNode : Prog false NodeInput Orientations := .comp nodeArgument orientations
def selectedNode : Prog false NodeInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def smallNode : Prog false NodeInput w :=
  integer .lt (.comp (.atom .fst) (.atom .fst)) (.atom (.lit 2))
def node : Prog false NodeInput Orientations :=
  .ifz smallNode (.ifz selectedNode leafNode emptyNode) leafNode
def forestArgument : Prog false Input (p w w) :=
  .fork (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def forestSeed : Prog false Input ForestSeed :=
  .fork (.atom .id) (.comp forestArgument DFTModelCacheTraversal.program)
def forestNodes : Prog false ForestSeed (Ty.a DFTModelCacheTraversal.Record7) :=
  .comp (.atom .snd) (.atom .fst)
def forestCellNode : Prog false ForestCell DFTModelCacheTraversal.Record7 :=
  .comp (.fork (.comp (.atom .fst) forestNodes) (.atom .snd)) (.atom .look)
def forestCellBase : Prog false ForestCell w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
def forestCell : Prog false ForestCell Orientations :=
  .comp (.fork forestCellNode forestCellBase) node
def forestBody : Prog false ForestSeed ForestOutput :=
  .fork (.atom .snd) (.tab (.comp forestNodes (.atom .len)) forestCell)
/-- One genuine raw traversal followed by both leaf orientations for every
returned node. Split nodes yield two empty tapes; width-one leaves are kept. -/
def forest : Prog false Input ForestOutput := .comp forestSeed forestBody

attribute [local irreducible] orientations DFTModelCacheTraversal.program node

def leaf (q : Visit) : Prop := q.task.width<2 ∨ UniformWorkspacePlanner.selected q.task.width=0
instance (q : Visit) : Decidable (leaf q) := inferInstanceAs
  (Decidable (q.task.width<2 ∨ UniformWorkspacePlanner.selected q.task.width=0))
def leafValue (K : ℕ) (q : Visit) : Orientations.T :=
  if leaf q then
    (DFTModelCacheTraversal.ofList ((UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K).map encode),
      DFTModelCacheTraversal.ofList (((UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K).reverse.map
        UniformTransposeDescriptorMachine.Record.transpose).map encode))
  else (DFTModelCacheTraversal.ofList [],DFTModelCacheTraversal.ofList [])

theorem node_run (q : Visit) (K : ℕ) :
    run node (DFTModelCacheTraversal.nodeEncode q,K)=
      if q.task.width<2 then (run orientations (q.task.width,(q.task.offset,K))).pay 20 2
      else if UniformWorkspacePlanner.selected q.task.width=0 then
        (run orientations (q.task.width,(q.task.offset,K))).pay 28 2
      else ⟨(DFTModelCacheTraversal.ofList [],DFTModelCacheTraversal.ofList []),25,2,True⟩ := by
  have empt : run emptyNode (DFTModelCacheTraversal.nodeEncode q,K)=
      ⟨(DFTModelCacheTraversal.ofList [],DFTModelCacheTraversal.ofList []),9,0,True⟩ := by
    have same : run emptyNode (DFTModelCacheTraversal.nodeEncode q,K)=
        ((run empty (q.task.width,(q.task.offset,K))).pass (fun a=>
          (run empty (q.task.width,(q.task.offset,K))).pass (fun b=>Bill.one (a,b)))) := rfl
    rw[same,empty_run];simp[Bill.pass,Bill.one]
  have small : run smallNode (DFTModelCacheTraversal.nodeEncode q,K)=
      ⟨if q.task.width<2 then 1 else 0,7,2,True⟩ := by
    simp [smallNode,integer,DFTModelCacheTraversal.nodeEncode,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
    split_ifs <;> omega
  have sel : run selectedNode (DFTModelCacheTraversal.nodeEncode q,K)=
      ⟨UniformWorkspacePlanner.selected q.task.width,7,0,True⟩ := by
    simp [selectedNode,DFTModelCacheTraversal.nodeEncode,run,Code.run,Atom.run,
      Bill.one,Bill.pass,Bill.pay]
  have prep : run leafNode (DFTModelCacheTraversal.nodeEncode q,K)=
      (run orientations (q.task.width,(q.task.offset,K))).pay 12 0 := by
    simp [leafNode,nodeArgument,DFTModelCacheTraversal.nodeEncode,run,Code.run,Atom.run,
      Bill.one,Bill.pass,Bill.pay]
    omega
  rw[node]
  change ((run smallNode (DFTModelCacheTraversal.nodeEncode q,K)).pass (fun b=>
    if b=0 then run (.ifz selectedNode leafNode emptyNode) (DFTModelCacheTraversal.nodeEncode q,K)
      else run leafNode (DFTModelCacheTraversal.nodeEncode q,K))).pay 1 0=_
  rw[small]
  by_cases hs:q.task.width<2
  · simp [hs,prep,Bill.pass,Bill.pay]
    omega
  · simp only [hs,ite_false]
    change (((⟨0,7,2,True⟩ : Bill ℕ).pass (fun _=>
      ((run selectedNode (DFTModelCacheTraversal.nodeEncode q,K)).pass (fun b=>
        if b=0 then run leafNode (DFTModelCacheTraversal.nodeEncode q,K)
          else run emptyNode (DFTModelCacheTraversal.nodeEncode q,K))).pay 1 0))).pay 1 0=_
    rw[sel,prep,empt]
    by_cases hz:UniformWorkspacePlanner.selected q.task.width=0 <;>
      simp [hz,Bill.pass,Bill.pay]
    omega

theorem node_value (q : Visit) (K : ℕ) :
    (run node (DFTModelCacheTraversal.nodeEncode q,K)).val=leafValue K q := by
  rw[node_run]
  by_cases hs:q.task.width<2 <;> by_cases hz:UniformWorkspacePlanner.selected q.task.width=0 <;>
    simp only [hs,hz,ite_true,ite_false,Bill.pay,leafValue,leaf,or_true,true_or,false_or]
  all_goals exact orientations_value _ _ _

theorem node_valid (q : Visit) (K : ℕ) :
    (run node (DFTModelCacheTraversal.nodeEncode q,K)).valid := by
  rw[node_run]
  split_ifs <;> first | exact orientations_valid _ _ _ | trivial

theorem node_work (q : Visit) (K : ℕ) :
    (run node (DFTModelCacheTraversal.nodeEncode q,K)).work≤1000*(q.task.width+1)^3+28 := by
  rw[node_run]
  have h:=orientations_work q.task.width q.task.offset K
  split_ifs <;> simp only [Bill.pay] <;> omega

theorem node_peak (q : Visit) (K : ℕ) :
    (run node (DFTModelCacheTraversal.nodeEncode q,K)).peak≤q.task.offset+K+2*(q.task.width+1)^2 := by
  rw[node_run]
  have h:=orientations_peak q.task.width q.task.offset K
  split_ifs <;> change _≤_ <;> first | exact max_le h (by nlinarith) | nlinarith

theorem forestCell_run (r o K i : ℕ) (t : DFTModelCacheTraversal.Output.T) :
    run forestCell (((r,(o,K)),t),i)=
      (run node (t.1.look i DFTModelCacheTraversal.Record7.blank,K)).pay 18 0 := by
  simp [forestCell,forestCellNode,forestCellBase,forestNodes,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  omega

theorem forest_run (r o K : ℕ) :
    run forest (r,(o,K))=
      ((run DFTModelCacheTraversal.program (r,o)).pass (fun t=>
        (Bill.tab t.1.len Orientations.blank (fun i=>run forestCell (((r,(o,K)),t),i))).pass
          (fun leaves=>Bill.one (t,leaves)))).pay 16
            (run DFTModelCacheTraversal.program (r,o)).val.1.len := by
  simp [forest,forestSeed,forestArgument,forestBody,forestNodes,
    run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  constructor
  · omega
  · ac_rfl

def visits (r o : ℕ) : List Visit := (walk (2*r+1) 0 0 [⟨r,o,0,0⟩]).1

theorem node_at (r o i : ℕ) (hi : i < (visits r o).length) :
    (run DFTModelCacheTraversal.program (r,o)).val.1.look i DFTModelCacheTraversal.Record7.blank=
      DFTModelCacheTraversal.nodeEncode ((visits r o)[i]'hi) := by
  rw[DFTModelCacheTraversal.program_value]
  change (DFTModelCacheTraversal.ofList ((visits r o).map DFTModelCacheTraversal.nodeEncode)).look i _=_
  have hm : i<(DFTModelCacheTraversal.ofList ((visits r o).map DFTModelCacheTraversal.nodeEncode)).len := by
    simpa[DFTModelCacheTraversal.ofList] using hi
  rw[Tape.look_of_lt _ _ hm]
  simp only[DFTModelCacheTraversal.ofList,List.getElem_map]

theorem node_produced (r o : ℕ)
    (i : Fin (run DFTModelCacheTraversal.program (r,o)).val.1.len) :
    ∃q,q∈visits r o ∧
      (run DFTModelCacheTraversal.program (r,o)).val.1.pos i=DFTModelCacheTraversal.nodeEncode q := by
  have len : (run DFTModelCacheTraversal.program (r,o)).val.1.len=(visits r o).length := by
    simpa [DFTModelCacheTraversal.ofList,visits] using
      congrArg (fun t=>t.1.len) (DFTModelCacheTraversal.program_value r o)
  have hi : i.val<(visits r o).length := by rw[←len];exact i.isLt
  refine ⟨(visits r o)[i.val]'hi,List.getElem_mem hi,?_⟩
  have eq:=node_at r o i.val hi
  rwa[Tape.look_of_lt _ _ i.isLt] at eq

theorem forest_value (r o K : ℕ) :
    (run forest (r,(o,K))).val=
      ((run DFTModelCacheTraversal.program (r,o)).val,
        DFTModelCacheTraversal.ofList ((visits r o).map (leafValue K))) := by
  rw[forest_run]
  change (_, (Bill.tab _ Orientations.blank _).val)=_
  rw[ModelEquivalenceInterpreter.tab_value]
  congr 1
  apply DFTModelCacheTraversal.tape_ext _ _ Orientations.blank ?_ ?_
  · simpa only [Tape.tab,DFTModelCacheTraversal.ofList,List.length_map,visits] using
      congrArg (fun t=>t.1.len) (DFTModelCacheTraversal.program_value r o)
  intro i hi
  have hlen:i<(visits r o).length := by
    have len : (run DFTModelCacheTraversal.program (r,o)).val.1.len=(visits r o).length := by
      simpa [DFTModelCacheTraversal.ofList,visits] using
        congrArg (fun t=>t.1.len) (DFTModelCacheTraversal.program_value r o)
    change i<(run DFTModelCacheTraversal.program (r,o)).val.1.len at hi
    omega
  rw[Tape.look_of_lt _ _ hi]
  change (run forestCell (((r,(o,K)),(run DFTModelCacheTraversal.program (r,o)).val),i)).val=_
  rw[forestCell_run]
  change (run node ((run DFTModelCacheTraversal.program (r,o)).val.1.look i
    DFTModelCacheTraversal.Record7.blank,K)).val=_
  rw[node_at r o i hlen,node_value]
  have hm:i<(DFTModelCacheTraversal.ofList ((visits r o).map (leafValue K))).len := by
    simpa [DFTModelCacheTraversal.ofList] using hlen
  rw[Tape.look_of_lt _ _ hm]
  simp only [DFTModelCacheTraversal.ofList,List.getElem_map]

end
end ExactFourierCircuits.DFTModelCacheDirectLeaf
