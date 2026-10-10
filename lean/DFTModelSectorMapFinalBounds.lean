import DFTModelSectorMapFinal

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
open DFTModelResidualCore
noncomputable section

theorem candidate_work (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run candidate (tables V d b m pk hi pw ca,j)).work ≤ 200 := by
 simp only [candidate,nearest,prefixBits,prefixPower,chunk,withinChunk,chunkStart,
 finalMarkers,finalPacked,finalHighs,finalPowers,finalCarry,finalB,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:hi.look (pk.look (j/b) 0%pw.look (j%b+1) 0) 0=0 <;> norm_num [Ty.blank,h]

theorem candidate_valid (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run candidate (tables V d b m pk hi pw ca,j)).valid := by
 simp only [candidate,nearest,prefixBits,prefixPower,chunk,withinChunk,chunkStart,
 finalMarkers,finalPacked,finalHighs,finalPowers,finalCarry,finalB,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:hi.look (pk.look (j/b) 0%pw.look (j%b+1) 0) 0=0 <;> simp [Ty.blank,h]

theorem checkCandidate_work (V j b c : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run checkCandidate ((tables V d b m pk hi pw ca,j),c)).work ≤ 150 := by
 simp only [checkCandidate,checkStart,checkEnd,selectedCell,selectedJ,blankCell,
 selectedStart,selectedWidth,selectedRow,finalDirectory,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases hc:c=0 <;> by_cases hs:j<(d.look (c-1) (0,0)).1 <;>
 by_cases he:j<(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2 <;>
 norm_num [Row,Ty.blank,hc,hs,he]

theorem checkCandidate_valid (V j b c : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run checkCandidate ((tables V d b m pk hi pw ca,j),c)).valid := by
 simp only [checkCandidate,checkStart,checkEnd,selectedCell,selectedJ,blankCell,
 selectedStart,selectedWidth,selectedRow,finalDirectory,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases hc:c=0 <;> by_cases hs:j<(d.look (c-1) (0,0)).1 <;>
 by_cases he:j<(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2 <;>
 simp [Row,Ty.blank,hc,hs,he]

theorem bind_work {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) (x : a.T) :
 (run (.comp (.fork (.atom .id) f) g) x).work=
 (run f x).work+(run g (x,(run f x).val)).work+3 := by
 simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay];omega

theorem bind_valid {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) (x : a.T) :
 (run (.comp (.fork (.atom .id) f) g) x).valid ↔
 (run f x).valid ∧ (run g (x,(run f x).val)).valid := by
 simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] candidate checkCandidate

theorem finalCell_work (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalCell (tables V d b m pk hi pw ca,j)).work ≤ 353 := by
 rw [finalCell,bind_work]
 have a:=candidate_work V j b d m pk hi pw ca
 have z:=checkCandidate_work V j b (run candidate (tables V d b m pk hi pw ca,j)).val d m pk hi pw ca
 omega

theorem finalCell_valid (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalCell (tables V d b m pk hi pw ca,j)).valid := by
 rw [finalCell,bind_valid]
 exact ⟨candidate_valid _ _ _ _ _ _ _ _ _,checkCandidate_valid _ _ _ _ _ _ _ _ _ _⟩

attribute [local irreducible] finalCell

theorem finalMap_work (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalMap (tables V d b m pk hi pw ca)).work ≤ 357*V+6 := by
 change 3+(Bill.tab V Cell.blank (fun j=>run finalCell (tables V d b m pk hi pw ca,j))).work+1 ≤ _
 rw [ModelEquivalenceInterpreter.tab_work]
 have hs:(∑j∈Finset.range V,(run finalCell (tables V d b m pk hi pw ca,j)).work)≤V*353:=by
  calc
   _ ≤ ∑_j∈Finset.range V,353:=Finset.sum_le_sum (fun j _=>finalCell_work _ _ _ _ _ _ _ _ _)
   _ = _:=by simp
 omega

theorem finalMap_valid (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalMap (tables V d b m pk hi pw ca)).valid := by
 change (True ∧ True) ∧ (Bill.tab V Cell.blank (fun j=>run finalCell (tables V d b m pk hi pw ca,j))).valid
 exact ⟨⟨trivial,trivial⟩,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>finalCell_valid _ _ _ _ _ _ _ _ _)⟩

end
end ExactFourierCircuits.DFTModelSectorMap
