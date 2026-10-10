import DFTModelCacheDescriptorSearch
import DFTModelCacheDescriptorRows

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- E (adc7f), §§3.1–3.5, pp.13–18. A real node computes the exhaustive
native cutoff once, then prints every ragged rectangle in native order.
The complete preorder forest is assembled by the separate traversal producer. -/
def emptyRows : Prog false RowsInput (Ty.a Row7) := .tab (.atom (.lit 0)) rowCell

def nodeRows : Prog false RowsInput (Ty.a Row7) :=
  .ifz (nat .lt (.comp (.atom .fst) (.atom .fst)) (.atom (.lit 2)))
    (.ifz (.atom .snd) emptyRows rectangleRows) emptyRows

def nodeSeed : Prog false (p w w) RowsInput :=
  .fork (.atom .id) (.comp (.atom .fst) selected)

def node : Prog false (p w w) (p w (Ty.a Row7)) :=
  .comp nodeSeed (.fork (.atom .snd) nodeRows)

attribute [local irreducible] selected rectangleRows rowCell

theorem emptyRows_value (v o b : ℕ) :
    (run emptyRows ((v,o),b)).val=listTape ([] : List Row7.T) := by
  change (Bill.tab 0 Row7.blank (fun h=>run rowCell (((v,o),b),h))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply tape_ext
  · rfl
  intro i
  exact Fin.elim0 i

theorem nodeRows_value (v o b : ℕ) :
    (run nodeRows ((v,o),b)).val=
      listTape ((if v<2 ∨ b=0 then [] else UniformLocalRectangleDescriptors.rows v o b).map rowEncode) := by
  have hem:=emptyRows_value v o b
  have hr:=rectangleRows_value v o b
  dsimp only [run] at hem hr
  rw [nodeRows]
  dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  split_ifs <;> simp_all
  all_goals omega

theorem nodeSeed_value (v o : ℕ) :
    (run nodeSeed (v,o)).val=((v,o),UniformWorkspacePlanner.selected v) := by
  change ((v,o),(run selected v).val)=_
  rw [selected_value]

theorem node_value (v o : ℕ) :
    (run node (v,o)).val=
      (UniformWorkspacePlanner.selected v,
        listTape ((UniformLocalCacheTreeCoverage.currentRows
          (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)).map rowEncode)) := by
  change ((run nodeSeed (v,o)).val.2,(run nodeRows (run nodeSeed (v,o)).val).val)=_
  rw [nodeSeed_value,nodeRows_value]
  rfl

end
end ExactFourierCircuits.DFTModelCacheDescriptor
