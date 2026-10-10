import DFTModelCacheSelectedPhysicalRowsBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelRecursiveScalarCore
open DFTModelCacheHeight (Words words_mono degree degree_positive literals straight straight_words)
open scoped BigOperators
noncomputable section
attribute [local irreducible] borrowed borrowedArgs mapper prepare program
 DFTModelCacheColorSelection.program

theorem tab_words_bound {s t:Ty} (n:Prog false s w) (b:Prog false (p s w) t)
 (x:s.T) (P:ℕ) (hn:(run n x).val≤P) (hp:(run n x).peak≤P)
 (hb:∀j,j<(run n x).val→Words t P (run b (x,j)).val ∧ (run b (x,j)).peak≤P) :
 Words (Ty.a t) P (run (.tab n b) x).val ∧ (run (.tab n b) x).peak≤P := by
 constructor
 · rw [DFTModelCacheMatchingNat.tab_value_code]
   exact ⟨hn,fun i=>(hb i.val i.isLt).1⟩
 · change max (max (run n x).peak (Bill.tab (run n x).val t.blank (fun j=>run b (x,j))).peak) 0≤P
   rw [ModelEquivalenceInterpreter.tab_peak]
   exact max_le (max_le hp (max_le hn (Finset.sup_le (fun j hj=>(hb j (Finset.mem_range.mp hj)).2)))) (Nat.zero_le _)

theorem geometry_tab_bound {t:Ty} (b:Prog false Candidate t) (hs:straight b=true)
 (hl:literals b≤1) (x:Geometry.T) (B:ℕ) (hB:5≤B) (hx:Words Geometry B x) :
 Words (Ty.a t) (B^degree b) (run (.tab radix b) x).val ∧
 (run (.tab radix b) x).peak≤B^degree b := by
 have grow:B≤B^degree b:=le_self_pow (by omega) (by have :=degree_positive b;omega)
 apply tab_words_bound radix b x (B^degree b)
 · exact hx.1.trans grow
 · change 0≤B^degree b
   exact Nat.zero_le _
 · intro j hj
   change j<x.1 at hj
   exact straight_words b hs () B (by omega) (hl.trans (by omega))
    (x,j) ⟨hx,(Nat.le_of_lt hj).trans hx.1⟩

def borrowedDegree : ℕ := max (max (degree candidate) (degree eligible)) DFTModelCacheColorSelection.wordDegree
def wordDegree : ℕ := max borrowedDegree (degree mapRow)

theorem candidateInput_words (v s e t a B:ℕ) (hB:1≤B) (hv:v≤B) :
 Words DFTModelCacheColorSelection.Input B (candidateInput v s e t a) := by
 refine ⟨hB,⟨hv,?_⟩,hv,?_⟩
 · intro i
   exact ⟨(Nat.le_of_lt i.isLt).trans hv,Nat.zero_le _,Nat.zero_le _⟩
 · intro i
   change (if UniformBorrowedCoordinateMachine.Eligible s e t a i.val then 1 else 0)≤B
   split_ifs <;>omega

theorem borrowedArgs_words (x:Geometry.T) (B:ℕ) (hB:1≤B) (hx:Words Geometry B x) :
 Words DFTModelCacheColorSelection.Input B (run borrowedArgs x).val := by
 rcases x with ⟨v,s,e,t,a,g⟩
 change Words DFTModelCacheColorSelection.Input B (run borrowedArgs (geom v s e t a g)).val
 rw [borrowedArgs_value]
 exact candidateInput_words v s e t a B hB hx.1

theorem borrowedArgs_peak (x:Geometry.T) (B:ℕ) (hB:5≤B) (hx:Words Geometry B x) :
 (run borrowedArgs x).peak≤B^borrowedDegree := by
 have c:=geometry_tab_bound candidate (by with_unfolding_all decide) (by with_unfolding_all decide) x B hB hx
 have e:=geometry_tab_bound eligible (by with_unfolding_all decide) (by with_unfolding_all decide) x B hB hx
 have dc:degree candidate≤borrowedDegree:=(le_max_left _ _).trans (le_max_left _ _)
 have de:degree eligible≤borrowedDegree:=(le_max_right _ _).trans (le_max_left _ _)
 have cp:=c.2.trans (Nat.pow_le_pow_right (by omega) dc)
 have ep:=e.2.trans (Nat.pow_le_pow_right (by omega) de)
 have positive:1≤B^borrowedDegree:=one_le_pow₀ (by omega)
 rw [borrowedArgs,fork_run,fork_run]
 simpa only [Bill.pass,Bill.one,Bill.word,max_zero,atom_run,Atom.run] using max_le positive (max_le cp ep)

theorem borrowed_peak (x:Geometry.T) (B:ℕ) (hB:5≤B) (hx:Words Geometry B x) :
 (run borrowed x).peak≤B^borrowedDegree := by
 have prep:=borrowedArgs_peak x B hB hx
 have sel:=DFTModelCacheColorSelection.program_bound (run borrowedArgs x).val B hB
  (borrowedArgs_words x B (by omega) hx)
 have ds:DFTModelCacheColorSelection.wordDegree≤borrowedDegree:=le_max_right _ _
 have selected:=sel.2.2.trans (Nat.pow_le_pow_right (by omega) ds)
 rw [borrowed,comp_run]
 simpa only [Bill.pass,Bill.pay,max_zero] using max_le prep selected

theorem borrowed_words (x:Geometry.T) (B:ℕ) (hx:Words Geometry B x) :
 Words (Ty.a Row) B (run borrowed x).val := by
 rcases x with ⟨v,s,e,t,a,g⟩
 change Words (Ty.a Row) B (run borrowed (geom v s e t a g)).val
 rw [borrowed_value]
 have len:(availableRows v s e t a).length≤v := by
  simp only [availableRows,List.length_map,UniformBorrowedCoordinateMachine.available]
  simpa only [List.length_range] using List.length_filter_le (fun i=>decide (UniformBorrowedCoordinateMachine.Eligible s e t a i)) (List.range v)
 refine ⟨len.trans hx.1,?_⟩
 intro i
 have nth:(availableRows v s e t a)[i.val]?=some ((availableRows v s e t a)[i.val]):=List.getElem?_eq_getElem i.isLt
 change Words Row B ((availableRows v s e t a)[i.val]?.getD Row.blank)
 rw [nth]
 have hi:i.val<(UniformBorrowedCoordinateMachine.available v s e t a).length:=by
  simpa only [availableRows,List.length_map,Tape.tab] using i.isLt
 have coord: (UniformBorrowedCoordinateMachine.available v s e t a)[i.val]<v:=
  (UniformBorrowedCoordinateMachine.available_mem.mp (List.getElem_mem hi)).1
 simp only [Option.getD_some,availableRows,List.getElem_map]
 exact ⟨(Nat.le_of_lt coord).trans hx.1,Nat.zero_le _,Nat.zero_le _⟩

theorem mapper_peak (x:Ready.T) (B:ℕ) (hB:5≤B) (hx:Words Ready B x) :
 (run mapper x).peak≤B^wordDegree := by
 have grow:B≤B^degree mapRow:=le_self_pow (by omega) (by have :=degree_positive mapRow;omega)
 have count:run (.comp rows (.atom .len)) x=⟨x.1.2.len,5,x.1.2.len,True⟩:=by
  simp [rows,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
 have hn:(run (.comp rows (.atom .len)) x).val≤B^degree mapRow:=by rw [count];exact hx.1.2.1.trans grow
 have hp:(run (.comp rows (.atom .len)) x).peak≤B^degree mapRow:=by rw [count];exact hx.1.2.1.trans grow
 have maps:=tab_words_bound (.comp rows (.atom .len)) mapRow x (B^degree mapRow) hn hp (by
   intro j hj
   change j<x.1.2.len at hj
   exact straight_words mapRow (by with_unfolding_all decide) () B (by omega)
    ((show literals mapRow≤1 by with_unfolding_all decide).trans (by omega))
    (x,j) ⟨hx,(Nat.le_of_lt hj).trans hx.1.2.1⟩)
 rw [mapper]
 exact maps.2.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))

/-- All input words, including physical labels, bound integer peaks by a fixed
AST exponent. They never determine work or dense allocation lengths. -/
theorem program_peak (x:Input.T) (B:ℕ) (hB:5≤B) (hx:Words Input B x) :
 (run program x).peak≤B^wordDegree := by
 have b:=borrowed_peak x.1 B hB hx.1
 have m:=mapper_peak (x,(run borrowed x.1).val) B hB ⟨hx,borrowed_words x.1 B hx.1⟩
 have prep:(run prepare x).peak=(run borrowed x.1).peak := by
  rw [prepare,DFTModelCacheColorRebase.retained_comp_run]
  simp [atom_run,Atom.run,Bill.one]
 rw [program,comp_run]
 change max (max (run prepare x).peak (run mapper (run prepare x).val).peak) 0≤_
 rw [prep,prepare_value]
 exact max_le (max_le (b.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))) m) (Nat.zero_le _)

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
