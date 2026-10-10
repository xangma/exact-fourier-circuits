import DFTModelSectorMaterializationSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMaterialization
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] program cell joinedTape joined DFTModelSectorMap.program

def MapBounds (V M : ℕ) (m : Tape DFTModelSectorMap.Cell.T) : Prop :=
 ∀j,j<V→(m.look j (0,(0,0))).1≤M ∧
 (m.look j (0,(0,0))).2.1≤V ∧ (m.look j (0,(0,0))).2.2≤V

theorem program_valid (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (program t) (W,(V,(m,(patches,old))))).valid := by
 rw [program_run]
 change (Bill.tab _ _ _).valid
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro j _
 rw [cell_run]
 exact DFTModelSectorMap.reader_valid t V j m patches old

theorem program_work (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (program t) (W,(V,(m,(patches,old))))).work≤110*(W*V)+12 := by
 rw [program_run]
 change (Bill.tab _ _ _).work+8≤_
 rw [ModelEquivalenceInterpreter.tab_work]
 have h:(∑j∈Finset.range (W*V),(run (cell t) ((W,(V,(m,(patches,old)))),j)).work)≤106*(W*V):=by
  calc
   _ ≤ ∑_j∈Finset.range (W*V),106:=by
    apply Finset.sum_le_sum
    intro j _
    rw [cell_run]
    have r:=DFTModelSectorMap.reader_work t V j m patches old
    change (run (DFTModelSectorMap.reader t) ((V,(m,(patches,old))),j)).work+6≤106
    omega
   _ = _:=by simp [Nat.mul_comm]
 omega

theorem program_peak (t : Ty) (W V M : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) (bounds:MapBounds V M m) :
 (run (program t) (W,(V,(m,(patches,old))))).peak≤2*(W*V)+M+V+2 := by
 rw [program_run]
 change max (Bill.tab _ _ _).peak (W*V)≤_
 rw [ModelEquivalenceInterpreter.tab_peak]
 apply max_le (max_le (by omega) ?_) (by omega)
 apply Finset.sup_le
 intro j hj
 have hj':j<W*V:=Finset.mem_range.mp hj
 have vp:0<V:=by
  by_contra z
  have vz:V=0:=by omega
  rw [vz] at hj'
  simp at hj'
 have rem:j%V<V:=Nat.mod_lt j vp
 obtain ⟨mb,wb,ob⟩:=bounds (j%V) rem
 have hd: (j/V)*V≤j:=Nat.div_mul_le_self j V
 have role:j/V<W:=by nlinarith
 have product:(j/V)*(m.look (j%V) (0,(0,0))).2.1≤W*V:=Nat.mul_le_mul role.le wb
 rw [cell_run]
 have r:=DFTModelSectorMap.reader_peak t V j m patches old
 simp only [DFTModelSectorMap.Cell,Ty.blank] at r
 change max (run (DFTModelSectorMap.reader t) ((V,(m,(patches,old))),j)).peak 0≤_
 apply max_le _ (by omega)
 apply r.trans
 calc
  _ ≤ W*V+M+W*V+V+2 :=
   Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hj'.le mb) product) ob) 2
  _ = _ := by omega

theorem mapped_bounds (V M j c : ℕ) (d : Tape (ℕ×ℕ)) (cb:c≤M)
 (fit:(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2≤V) (hj:j≤V) :
 (DFTModelSectorMap.mapped d j c).1≤M ∧
 (DFTModelSectorMap.mapped d j c).2.1≤V ∧ (DFTModelSectorMap.mapped d j c).2.2≤V := by
 by_cases hc:c=0
 · simp [DFTModelSectorMap.mapped,hc]
 by_cases ha:j<(d.look (c-1) (0,0)).1
 · simp [DFTModelSectorMap.mapped,hc,ha]
 by_cases he:j<(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2
 · simp only [DFTModelSectorMap.mapped,hc,ha,he,↓reduceIte]
   exact ⟨cb,(Nat.le_add_left _ _).trans fit,(Nat.sub_le j _).trans hj⟩
 · simp [DFTModelSectorMap.mapped,hc,ha,he]

theorem produced_map_bounds {V : ℕ} {d : Tape (ℕ×ℕ)} (g:DFTModelSectorMap.Geometry V d) :
 MapBounds V d.len (run DFTModelSectorMap.program (V,d)).val := by
 intro j hj
 let c:=DFTModelSectorMap.chosen (DFTModelSectorMapParameters.blockBits V) j
  (DFTModelSectorMap.marks V d) (DFTModelSectorMap.packedTable V d)
  (DFTModelSectorMap.highTable V) (DFTModelSectorMap.powerTable V) (DFTModelSectorMap.carryTable V d)
 have cb:c≤d.len:=DFTModelSectorMap.chosen_bound g j
 have fit:(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2≤V:=by
  by_cases hc:c-1<d.len
  · exact g.fit _ hc
  · simp [Tape.look,hc]
 rw [DFTModelSectorMap.program_value]
 simp only [Tape.look,Tape.tab,hj,↓reduceDIte]
 change (DFTModelSectorMap.mapped d j c).1≤d.len ∧
  (DFTModelSectorMap.mapped d j c).2.1≤V ∧ (DFTModelSectorMap.mapped d j c).2.2≤V
 exact mapped_bounds V d.len j c d cb fit hj.le

theorem joined_valid (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)}
 (g:DFTModelSectorMap.Geometry V d) (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).valid := by
 rw [joined_run,joinedTape_run]
 change ((run DFTModelSectorMap.program (V,d)).valid ∧
  (run (program t) (W,(V,((run DFTModelSectorMap.program (V,d)).val,(patches,old))))).valid)∧True
 exact ⟨⟨DFTModelSectorMap.program_valid g,program_valid _ _ _ _ _ _⟩,True.intro⟩

theorem joined_work (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)}
 (g:DFTModelSectorMap.Geometry V d) (count:d.len≤V)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).work≤2200*(V+W*V+1) := by
 rw [joined_run,joinedTape_run]
 dsimp only [Bill.pay,Bill.pass,Bill.one]
 have m:=DFTModelSectorMap.program_work_linear g count
 have p:=program_work t W V (run DFTModelSectorMap.program (V,d)).val patches old
 omega

theorem joined_peak (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)}
 (g:DFTModelSectorMap.Geometry V d) (count:d.len≤V)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).peak≤6*(V+W*V+1) := by
 rw [joined_run,joinedTape_run]
 dsimp only [Bill.pay,Bill.pass,Bill.one]
 have m:=DFTModelSectorMap.program_peak g count
 have p:=program_peak t W V d.len (run DFTModelSectorMap.program (V,d)).val patches old (produced_map_bounds g)
 omega

theorem specification (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)}
 (g:DFTModelSectorMap.Geometry V d) (count:d.len≤V)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).valid ∧
 (run (joined t) (W,((V,d),(patches,old)))).val.2.len=W*V ∧
 (run (joined t) (W,((V,d),(patches,old)))).work≤2200*(V+W*V+1) ∧
 (run (joined t) (W,((V,d),(patches,old)))).peak≤6*(V+W*V+1) :=
 ⟨joined_valid t g patches old,joined_length t W V d patches old,
  joined_work t g count patches old,joined_peak t g count patches old⟩

end
end ExactFourierCircuits.DFTModelSectorMaterialization
