import DFTModelCacheCompact

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheCompact
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

attribute [local irreducible] fields H scale inverseDiagonal inverseH G row indexOp width

theorem cell_run (v : Input.T) (i : ℕ) : run cell (v,i)=
    (run (DFTModelCacheLiteral.choose G fields) ((v,i),i/v.1.len)).pay
      12 (max v.1.len (i/v.1.len)) := by
  rw [cell,comp_run,fork_run,index_run]
  simp only [atom_run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_zero,true_and]
  congr 1
  · omega
  · exact max_comm _ _

theorem cell_work (v : Input.T) (i : ℕ) : (run cell (v,i)).work≤157 := by
  rw [cell_run]
  have h:=DFTModelCacheLiteral.choose_work G fields (v,i) (i/v.1.len)
  rw [fields] at h
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil] at h
  have hs:=fields_run v i
  rw [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2] at h
  change (run (DFTModelCacheLiteral.choose G fields) ((v,i),i/v.1.len)).work+12≤_
  dsimp only [Bill.work] at h
  rw [fields]
  omega

theorem cell_peak (v : Input.T) (i : ℕ) (hi : i<5*v.1.len) :
    (run cell (v,i)).peak≤5*(v.1.len+1) := by
  have hr : 0<v.1.len := by nlinarith
  have hd : i/v.1.len<5 := (Nat.div_lt_iff_lt_mul hr).2 hi
  have hm : i%v.1.len<v.1.len := Nat.mod_lt _ hr
  have hs:=fields_run v i
  have hp : (run (DFTModelCacheLiteral.choose G fields) ((v,i),i/v.1.len)).peak≤
      5*(v.1.len+1) := by
    apply DFTModelCacheLiteral.choose_peak
    · omega
    · omega
    · rw [hs.2.2.2.2];change max _ _≤_;omega
    · intro f hf
      rw [fields] at hf
      simp at hf
      rcases hf with rfl|rfl|rfl|rfl
      · rw [hs.1];change max _ _≤_;omega
      · rw [hs.2.1];change max _ _≤_;omega
      · rw [hs.2.2.1];change max _ _≤_;omega
      · rw [hs.2.2.2.1];change max _ _≤_;omega
  rw [cell_run]
  change max _ (max _ _)≤_
  exact max_le hp (max_le (by omega) (by omega))

theorem program_run (v : Input.T) : run program v=
    (Bill.tab (5*v.1.len) sc.blank (fun j=>run cell (v,j))).pay
      8 (max (max v.1.len 5) (5*v.1.len)) := by
  change ((run count v).pass (fun k=>Bill.tab k sc.blank
    (fun j=>run cell (v,j)))).pay 1 0=_
  rw [count_run]
  simp only [Bill.pass,Bill.pay,max_zero,true_and]
  congr 1
  · omega
  · exact max_comm _ _

theorem program_value (v : Input.T) :
    (run program v).val=Tape.tab (5*v.1.len) (expected v) := by
  rw [program_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (cell_value v))

theorem program_valid (v : Input.T) : (run program v).valid := by
  rw [program_run]
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>cell_valid v j)

theorem program_work (v : Input.T) : (run program v).work≤1000*(v.1.len+1) := by
  rw [program_run]
  change (Bill.tab _ _ _).work+8≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j∈Finset.range (5*v.1.len),(run cell (v,j)).work)≤5*v.1.len*157 := by
    calc
      _≤∑_j∈Finset.range (5*v.1.len),157 := Finset.sum_le_sum (fun j _=>cell_work v j)
      _=_ := by simp
  omega

theorem program_peak (v : Input.T) : (run program v).peak≤5*(v.1.len+1) := by
  rw [program_run]
  change max (Bill.tab _ _ _).peak _≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (by omega) ?_) (max_le (max_le (by omega) (by omega)) (by omega))
  exact Finset.sup_le (fun j hj=>cell_peak v j (Finset.mem_range.mp hj))

end
end ExactFourierCircuits.DFTModelCacheCompact
