import DFTModelCacheRectanglePreparationSource
import DFTModelCacheDescriptorNodeBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDescriptor (Row7 rowEncode)
noncomputable section
attribute [local irreducible] program DFTModelCacheDescriptor.node

abbrev NodeInput := p w (p (p w w) (p w sc))
abbrev NodeResult := p w (Ty.a Row7)
abbrev NodeSeed := p NodeInput NodeResult
abbrev NodeCell := p NodeSeed w
abbrev NodeOutput := p w (Ty.a Output)

def nodeSeed : Prog false NodeInput NodeSeed :=
  .fork (.atom .id) (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelCacheDescriptor.node)
def producedRows : Prog false NodeSeed (Ty.a Row7) := .comp (.atom .snd) (.atom .snd)
def nodeLength : Prog false NodeSeed w := .comp producedRows (.atom .len)
def nodeRow : Prog false NodeCell Row7 :=
  .comp (.fork (.comp (.atom .fst) producedRows) (.atom .snd)) (.atom .look)
def nodeRadix : Prog false NodeCell w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def nodeMaster : Prog false NodeCell (p w sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
def nodeArgument : Prog false NodeCell Input :=
  .fork (.fork nodeRadix nodeRow) nodeMaster
def nodeCell : Prog false NodeCell Output := .comp nodeArgument program
def nodeBanks : Prog false NodeSeed (Ty.a Output) := .tab nodeLength nodeCell
def nodeBody : Prog false NodeSeed NodeOutput :=
  .fork (.comp (.atom .snd) (.atom .fst)) nodeBanks
def nodeProgram : Prog false NodeInput NodeOutput := .comp nodeSeed nodeBody

theorem nodeCell_run (r v o D i : ℕ) (z : ℂ) (nd : NodeResult.T) :
    run nodeCell (((r,((v,o),(D,z))),nd),i)=
      (run program ((r,nd.2.look i Row7.blank),(D,z))).pay 24 0 := by
  simp [nodeCell,nodeArgument,nodeRadix,nodeRow,nodeMaster,producedRows,
    run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem nodeProgram_run (r v o D : ℕ) (z : ℂ) :
    run nodeProgram (r,((v,o),(D,z)))=
      ((run DFTModelCacheDescriptor.node (v,o)).pass (fun nd=>
        (Bill.tab nd.2.len Output.blank (fun i=>
          run nodeCell (((r,((v,o),(D,z))),nd),i))).pass
            (fun banks=>Bill.one (nd.1,banks)))).pay 16
              (run DFTModelCacheDescriptor.node (v,o)).val.2.len := by
  simp [nodeProgram,nodeSeed,nodeBody,nodeBanks,nodeLength,producedRows,
    run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] nodeProgram

theorem nodeProgram_length (r v o D : ℕ) (z : ℂ) :
    (run nodeProgram (r,((v,o),(D,z)))).val.2.len=
      (run DFTModelCacheDescriptor.node (v,o)).val.2.len := by
  rw [nodeProgram_run]
  exact congrArg Tape.len (ModelEquivalenceInterpreter.tab_value _ _ _)

/-- The combined producer executes the descriptor printer once and prepares
every returned row internally. No row tape, cutoff, FFT size or bank is given. -/
theorem nodeProgram_specification (r v o D : ℕ) (vr : v≤r)
    (i : Fin (run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.len) :
    ∃q,ProducedRow r q ∧
      (run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.pos i=
        (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).val := by
  have hi : i.val<(run DFTModelCacheDescriptor.node (v,o)).val.2.len := by
    have length:=nodeProgram_length r v o D (OAI.ExactFourier.zeta D)
    omega
  obtain ⟨q,source,eq⟩:=node_produced r v o vr ⟨i.val,hi⟩
  refine ⟨q,source,?_⟩
  have tab:=ModelEquivalenceInterpreter.tab_value
    (run DFTModelCacheDescriptor.node (v,o)).val.2.len Output.blank
    (fun k=>run nodeCell (((r,((v,o),(D,OAI.ExactFourier.zeta D))),
      (run DFTModelCacheDescriptor.node (v,o)).val),k))
  have bank : (run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2=
      Tape.tab (run DFTModelCacheDescriptor.node (v,o)).val.2.len (fun k=>
        (run nodeCell (((r,((v,o),(D,OAI.ExactFourier.zeta D))),
          (run DFTModelCacheDescriptor.node (v,o)).val),k)).val) := by
    rw [nodeProgram_run]
    exact tab
  have cell:=congrArg (fun t:Tape Output.T=>t.look i.val Output.blank) bank
  rw [Tape.look_of_lt _ _ i.isLt] at cell
  refine cell.trans ?_
  have read:=Tape.look_of_lt
    (Tape.tab (run DFTModelCacheDescriptor.node (v,o)).val.2.len (fun k=>
      (run nodeCell (((r,((v,o),(D,OAI.ExactFourier.zeta D))),
        (run DFTModelCacheDescriptor.node (v,o)).val),k)).val)) Output.blank hi
  rw [read]
  change (run nodeCell (((r,((v,o),(D,OAI.ExactFourier.zeta D))),
    (run DFTModelCacheDescriptor.node (v,o)).val),i.val)).val=_
  rw [nodeCell_run,Tape.look_of_lt _ _ hi,eq]
  rfl

theorem nodeProgram_valid (r v o D : ℕ) (vr : v≤r) (master : Master r D) :
    (run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).valid := by
  rw [nodeProgram_run]
  refine ⟨DFTModelCacheDescriptor.node_valid v o,?_,trivial⟩
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).mpr
  intro i hi
  obtain ⟨q,source,eq⟩:=node_produced r v o vr ⟨i,hi⟩
  rw [nodeCell_run,Tape.look_of_lt _ _ hi,eq]
  exact program_valid source master

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
