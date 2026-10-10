import DFTModelSectorMapBounds
import DFTModelSectorMapSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section

attribute [local irreducible] sparse DFTModelSectorMapBits.pack DFTModelSectorMapBits.highTable
 DFTModelSectorMapCarry.program DFTModelSectorMapParameters.program powers finalMap
 startBits startMarks startPack startHighs startPowers startCarry finish

theorem sparse_bound {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (j : ℕ) :
 (marks V d).look j 0≤d.len := by
 by_cases hj:j<V
 · by_cases hz:(marks V d).look j 0=0
   · rw [hz];exact Nat.zero_le _
   · obtain ⟨i,hi,_,_,eq⟩:=sparse_origin g j hj hz
     change (marks V d).look j 0=i+1 at eq
     rw [eq];exact Nat.succ_le_of_lt hi
 · have hm:(marks V d).len=V:=sparse_length V d
   simp [Tape.look,hm,hj]

theorem carry_bound {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (c : ℕ) :
 (carryTable V d).look c 0≤d.len := by
 by_cases hc:c<V/DFTModelSectorMapParameters.blockBits V+1
 · exact (DFTModelSectorMapCarry.program_cut _ _ d g.starts_ordered c hc).2.1
 · have hl:(carryTable V d).len=V/DFTModelSectorMapParameters.blockBits V+1:=
    DFTModelSectorMapCarry.program_length _ _ d
   simp [Tape.look,hl,hc]

theorem chosen_bound {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (j : ℕ) :
 chosen (DFTModelSectorMapParameters.blockBits V) j (marks V d) (packedTable V d)
 (highTable V) (powerTable V) (carryTable V d)≤d.len := by
 unfold chosen
 dsimp only
 split
 · exact carry_bound g _
 · exact sparse_bound g _

theorem candidate_peak (V j b B : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ)
 (hj:j<V)
 (prefBound:pk.look (j/b) 0%pw.look (j%b+1) 0≤B)
 (high:hi.look (pk.look (j/b) 0%pw.look (j%b+1) 0) 0≤j%b+1) :
 (run candidate (tables V d b m pk hi pw ca,j)).peak ≤ max (V+1) B := by
 have hd:=Nat.div_le_self j b
 have hm:=Nat.mod_le j b
 have decomp:j%b+(j/b)*b=j:=by simpa only [Nat.mul_comm] using Nat.mod_add_div j b
 have hs: (j/b)*b+(hi.look (pk.look (j/b) 0%pw.look (j%b+1) 0) 0-1)≤j:=by omega
 simp only [candidate,nearest,prefixBits,prefixPower,chunk,withinChunk,chunkStart,
 finalMarkers,finalPacked,finalHighs,finalPowers,finalCarry,finalB,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:hi.look (pk.look (j/b) 0%pw.look (j%b+1) 0) 0=0 <;>
 simp only [Ty.blank,h,↓reduceIte,max_zero,zero_max] <;> omega

theorem checkCandidate_peak (V j b c : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run checkCandidate ((tables V d b m pk hi pw ca,j),c)).peak≤
 max 1 (max c (max j ((d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2))) := by
 have hs:=Nat.sub_le c 1
 have hj:=Nat.sub_le j (d.look (c-1) (0,0)).1
 simp only [checkCandidate,checkStart,checkEnd,selectedCell,selectedJ,blankCell,
 selectedStart,selectedWidth,selectedRow,finalDirectory,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases hc:c=0 <;> by_cases ha:j<(d.look (c-1) (0,0)).1 <;>
 by_cases he:j<(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2 <;>
 simp [Row,Ty.blank,hc,ha,he] <;> omega

theorem bind_peak {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) (x : a.T) :
 (run (.comp (.fork (.atom .id) f) g) x).peak=
 max (run f x).peak (run g (x,(run f x).val)).peak := by
 simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] candidate checkCandidate

theorem finalCell_peak {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V)
 (j : ℕ) (hj:j<V) :
 (run finalCell (tables V d (DFTModelSectorMapParameters.blockBits V) (marks V d)
  (packedTable V d) (highTable V) (powerTable V) (carryTable V d),j)).peak≤6*(V+1) := by
 let b:=DFTModelSectorMapParameters.blockBits V
 have bp:0<b:=DFTModelSectorMapParameters.blockBits_pos V
 have chunk:j/b<V/b+1:=by have:=Nat.div_le_div_right (c:=b) hj.le;omega
 have rem:j%b<b:=Nat.mod_lt _ bp
 have pp:(powerTable V).look (j%b+1) 0=2^(j%b+1):=powers_lookup b _ (by omega)
 have prefBound:(packedTable V d).look (j/b) 0%(powerTable V).look (j%b+1) 0≤2^b:=by
  rw [pp]
  exact le_trans (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)))
   (Nat.pow_le_pow_right (by decide) (by omega))
 have nearest:=DFTModelSectorMapBits.produced_prefix_nearest b V (marks V d) (j/b) (j%b) chunk rem
 have hhigh:(highTable V).look ((packedTable V d).look (j/b) 0%(powerTable V).look (j%b+1) 0) 0≤j%b+1:=by
  rw [pp]
  change (run DFTModelSectorMapBits.highTable b).val.look
   ((run DFTModelSectorMapBits.pack (b,(V,marks V d))).val.look (j/b) 0%2^(j%b+1)) 0≤_
  rcases nearest with ⟨hz,_⟩|⟨i,hi,eq,_,_⟩
  · rw [hz];exact Nat.zero_le _
  · rw [eq];exact Nat.succ_le_of_lt hi
 have first:=candidate_peak V j b (2^b) d (marks V d) (packedTable V d) (highTable V) (powerTable V) (carryTable V d) hj prefBound hhigh
 let c:=chosen b j (marks V d) (packedTable V d) (highTable V) (powerTable V) (carryTable V d)
 have cb:c≤V:=(chosen_bound g j).trans count
 have fit:(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2≤V:=by
  by_cases hc:c-1<d.len
  · exact g.fit _ hc
  · simp [Tape.look,hc]
 have second:=checkCandidate_peak V j b c d (marks V d) (packedTable V d) (highTable V) (powerTable V) (carryTable V d)
 rw [finalCell,bind_peak,candidate_value]
 have pw:2^b≤6*(V+1):=DFTModelSectorMapParameters.blockBits_pow V
 exact max_le (first.trans (by omega)) (second.trans (by omega))

attribute [local irreducible] finalCell

theorem finalMap_peak {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V) :
 (run finalMap (tables V d (DFTModelSectorMapParameters.blockBits V) (marks V d)
  (packedTable V d) (highTable V) (powerTable V) (carryTable V d))).peak≤6*(V+1) := by
 rw [finalMap,tab_run]
 change max (Bill.tab V Cell.blank (fun j=>run finalCell
  (tables V d (DFTModelSectorMapParameters.blockBits V) (marks V d)
   (packedTable V d) (highTable V) (powerTable V) (carryTable V d),j))).peak 0≤_
 rw [ModelEquivalenceInterpreter.tab_peak]
 apply max_le (max_le (by omega) ?_) (by omega)
 apply Finset.sup_le
 intro j hj
 exact finalCell_peak g count j (Finset.mem_range.mp hj)


theorem program_peak {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V) :
 (run program (V,d)).peak≤6*(V+1) := by
 have p:=DFTModelSectorMapParameters.program_peak V
 have s:=sparse_peak V d
 have pk:=DFTModelSectorMapParameters.pack_peak_linear V (marks V d)
 have hi:=DFTModelSectorMapParameters.highTable_peak_linear V
 have pw:=powers_peak (DFTModelSectorMapParameters.blockBits V)
 have pb:=DFTModelSectorMapParameters.blockBits_pow V
 have ca:=DFTModelSectorMapCarry.program_peak (DFTModelSectorMapParameters.blockBits V) V d
  (DFTModelSectorMapParameters.blockBits_pos V) g.starts_ordered
 have f:=finalMap_peak g count
 unfold program
 rw [bind,bind_peak,startBits_run]
 dsimp only [Bill.pay]
 rw [DFTModelSectorMapParameters.program_value]
 rw [bind,bind_peak,startMarks_run]
 dsimp only [Bill.pay]
 rw [bind,bind_peak,startPack_run]
 dsimp only [Bill.pay]
 rw [bind,bind_peak,startHighs_run]
 dsimp only [Bill.pay]
 rw [bind,bind_peak,startPowers_run]
 dsimp only [Bill.pay]
 rw [bind,bind_peak,startCarry_run]
 dsimp only [Bill.pay]
 rw [finish_run]
 dsimp only [Bill.pay]
 dsimp only [marks,packedTable,highTable,powerTable,carryTable] at pk f ⊢
 simp only [max_zero]
 omega

/-- The supplied directory is ordinary input; no supplied direct map is used. -/
theorem specification {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V) :
 (run program (V,d)).valid ∧ (run program (V,d)).val.len=V ∧
 (run program (V,d)).work≤2000*(V+1) ∧ (run program (V,d)).peak≤6*(V+1) :=
 ⟨program_valid g,program_length V d,program_work_linear g count,program_peak g count⟩

end
end ExactFourierCircuits.DFTModelSectorMap
