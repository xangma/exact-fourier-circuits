import DFTModelCacheCalendarPrefix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming
open DFTModelCacheTraversal (ofList rectangleEncode tape_ext)
noncomputable section
attribute [local irreducible] prefixProgram Bill.tab

abbrev SequenceInput : Ty := p w (Ty.a Row7)
abbrev EventCellInput : Ty := p SequenceInput w
abbrev Output : Ty := p w (Ty.a Event9)
def cellRows : Prog false EventCellInput (Ty.a Row7) := .comp (.atom .fst) (.atom .snd)
def cellStart : Prog false EventCellInput w := .comp (.atom .fst) (.atom .fst)
def cellRow : Prog false EventCellInput Row7 := .comp (.fork cellRows (.atom .snd)) (.atom .look)
def cellPrefix : Prog false EventCellInput w := .comp (.fork cellRows (.atom .snd)) prefixProgram
def eventCell : Prog false EventCellInput Event9 :=
  .fork (nat .add cellStart cellPrefix) (.fork (.atom (.lit 1)) cellRow)
def sequenceCount : Prog false SequenceInput w := .comp (.atom .snd) (.atom .len)
def sequenceTotal : Prog false SequenceInput w :=
  .comp (.fork (.atom .snd) sequenceCount) prefixProgram
def eventTable : Prog false SequenceInput (Ty.a Event9) := .tab sequenceCount eventCell
def sequence : Prog false SequenceInput Output := .fork sequenceTotal eventTable

theorem eventCell_run (start : ℕ) (L : List Row) (j : ℕ) (hj:j<L.length) :
    run eventCell ((start,ofList (L.map rectangleEncode)),j)=
      ⟨(start+(run prefixProgram (ofList (L.map rectangleEncode),j)).val,(1,rectangleEncode L[j])),
       (run prefixProgram (ofList (L.map rectangleEncode),j)).work+22,
       max (max (run prefixProgram (ofList (L.map rectangleEncode),j)).peak
         (start+(run prefixProgram (ofList (L.map rectangleEncode),j)).val)) 1,
       (run prefixProgram (ofList (L.map rectangleEncode),j)).valid⟩ := by
  have get:(ofList (L.map rectangleEncode)).look j Row7.blank=rectangleEncode L[j] := by
    simp [ofList,Tape.look,hj]
  simp [eventCell,nat,cellStart,cellPrefix,cellRow,cellRows,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,get]
  omega

attribute [local irreducible] eventCell eventTable sequenceTotal

theorem sequenceRows_get (start : ℕ) (L : List Row) (j : ℕ) (hj:j<L.length) :
    (sequenceRows start L)[j]'(by rw [sequenceRows_length];exact hj)=
      ⟨start+rectanglesDuration (L.take j),.rectangle L[j]⟩ := by
  induction L generalizing start j with
  | nil => simp at hj
  | cons q L ih =>
    cases j with
    | zero => simp [sequenceRows,rectanglesDuration]
    | succ j =>
      simp only [List.length_cons,Nat.succ_lt_succ_iff] at hj
      simp only [sequenceRows,List.getElem_cons_succ,List.take_succ_cons]
      rw [ih _ j hj]
      simp [rectanglesDuration,Nat.add_assoc]

theorem eventTable_value (start : ℕ) (L : List Row) :
    (run eventTable (start,ofList (L.map rectangleEncode))).val=
      ofList ((sequenceRows start L).map eventEncode) := by
  rw [eventTable]
  change (Bill.tab (L.map rectangleEncode).length Event9.blank
    (fun j=>run eventCell ((start,ofList (L.map rectangleEncode)),j))).val=_
  rw [List.length_map,ModelEquivalenceInterpreter.tab_value]
  refine tape_ext
    (Tape.tab L.length (fun j=>(run eventCell ((start,ofList (L.map rectangleEncode)),j)).val))
    (ofList ((sequenceRows start L).map eventEncode)) Event9.blank
    (by simp [Tape.tab,ofList,sequenceRows_length]) ?_
  intro j hj
  change j<L.length at hj
  rw [Tape.look_of_lt _ _ hj]
  change (run eventCell ((start,ofList (L.map rectangleEncode)),j)).val=
    (ofList ((sequenceRows start L).map eventEncode)).look j Event9.blank
  rw [eventCell_run start L j hj,prefix_value L j (by omega)]
  rw [DFTModelCacheTraversal.ofList_look]
  rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [sequenceRows_length];exact hj)]
  simp only [Option.map_some,Option.getD_some]
  rw [sequenceRows_get start L j hj]
  rfl

theorem sequenceTotal_run (start : ℕ) (L : List Row) :
    run sequenceTotal (start,ofList (L.map rectangleEncode))=
      (run prefixProgram (ofList (L.map rectangleEncode),L.length)).pay 6 L.length := by
  rw [sequenceTotal]
  change ((run (.fork (.atom .snd) sequenceCount) (start,ofList (L.map rectangleEncode))).pass
    (fun z=>run prefixProgram z)).pay 1 0=_
  have h:run (.fork (.atom .snd) sequenceCount) (start,ofList (L.map rectangleEncode))=
      ⟨(ofList (L.map rectangleEncode),L.length),5,L.length,True⟩ := by
    simp [sequenceCount,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,ofList]
  rw [h]
  simp only [Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;> omega

theorem sequence_value (start : ℕ) (L : List Row) :
    (run sequence (start,ofList (L.map rectangleEncode))).val=
      (rectanglesDuration L,ofList ((sequenceRows start L).map eventEncode)) := by
  change ((run sequenceTotal (start,ofList (L.map rectangleEncode))).val,
    (run eventTable (start,ofList (L.map rectangleEncode))).val)=_
  rw [eventTable_value,sequenceTotal_run]
  change ((run prefixProgram (ofList (L.map rectangleEncode),L.length)).val,_)=_
  rw [prefix_value L L.length le_rfl,List.take_length]

theorem eventTable_valid (start : ℕ) (L : List Row) :
    (run eventTable (start,ofList (L.map rectangleEncode))).valid := by
  rw [eventTable]
  simp only [run,Code.run,sequenceCount,Atom.run,Bill.one,Bill.pass,Bill.pay,
    ofList,List.length_map,true_and,Bill.word]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j hj
  change (run eventCell ((start,ofList (L.map rectangleEncode)),j)).valid
  rw [eventCell_run start L j hj]
  exact prefix_valid L j (by omega)

theorem sequence_valid (start : ℕ) (L : List Row) :
    (run sequence (start,ofList (L.map rectangleEncode))).valid := by
  have total:(run sequenceTotal (start,ofList (L.map rectangleEncode))).valid := by
    rw [sequenceTotal_run]
    exact prefix_valid L L.length le_rfl
  simpa only [sequence,run,Code.run,Bill.pass,Bill.pay,Bill.one,and_true] using
    And.intro total (eventTable_valid start L)

end
end ExactFourierCircuits.DFTModelCacheCalendar
