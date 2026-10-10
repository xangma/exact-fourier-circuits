import DFTModelSectorMapProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] power sparse DFTModelSectorMapBits.pack DFTModelSectorMapBits.highTable
 DFTModelSectorMapParameters.program DFTModelSectorMapCarry.program finalMap
 startBits startMarks startPack startHighs startPowers startCarry finish

theorem snd_program_run {a b c : Ty} (f : Prog false b c) (x : a.T) (y : b.T) :
 run (.comp (.atom .snd) f) (x,y)=(run f y).pay 2 0 := by
 simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1;omega

theorem tab_run {a b : Ty} (n : Prog false a w) (f : Prog false (p a w) b) (x : a.T) :
 run (.tab n f) x=((run n x).pass (fun len=>Bill.tab len b.blank (fun i=>run f (x,i)))).pay 1 0 :=rfl

theorem powers_run (b : ℕ) : run powers b=
 (Bill.tab (b+1) 0 (fun i=>run ((.comp (.atom .snd) power) : Prog false (p w w) w) (b,i))).pay 6 (b+1) := by
 have count:run (binary .add (.atom .id) (.atom (.lit 1))) b=⟨b+1,5,b+1,True⟩:=by
  simp [binary,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
 rw [powers,tab_run,count]
 simp only [Bill.pass,Bill.pay,Ty.blank,true_and,max_zero]
 congr 1 <;> omega

attribute [local irreducible] powers

theorem powers_valid (b : ℕ) : (run powers b).valid := by
 rw [powers_run]
 change (Bill.tab _ _ _).valid
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro i _
 rw [snd_program_run]
 exact power_valid i

theorem powers_work (b : ℕ) : (run powers b).work≤20*(b+1)^2 := by
 rw [powers_run]
 change (Bill.tab _ _ _).work+6≤_
 rw [ModelEquivalenceInterpreter.tab_work]
 have hs:(∑i∈Finset.range (b+1),(run ((.comp (.atom .snd) power) : Prog false (p w w) w) (b,i)).work)≤(b+1)*(8*b+6):=by
  calc
   _ ≤ ∑_i∈Finset.range (b+1),(8*b+6):=by
    apply Finset.sum_le_sum
    intro i hi
    rw [snd_program_run]
    change (run power i).work+2≤_
    rw [power_work]
    have:=Finset.mem_range.mp hi;omega
   _ = _:=by simp
 nlinarith

theorem powers_peak (b : ℕ) : (run powers b).peak≤2^b := by
 rw [powers_run]
 change max (Bill.tab _ _ _).peak (b+1)≤_
 rw [ModelEquivalenceInterpreter.tab_peak]
 have hb:b+1≤2^b:=Nat.succ_le_of_lt b.lt_two_pow_self
 apply max_le _ hb
 apply max_le hb
 apply Finset.sup_le
 intro i hi
 rw [snd_program_run]
 change max (run power i).peak 0≤_
 have hp:=power_peak i
 have hn:=Finset.mem_range.mp hi
 have pw:2^i≤2^b:=Nat.pow_le_pow_right (by decide) (by omega)
 omega

theorem powers_work_linear (V : ℕ) :
 (run powers (DFTModelSectorMapParameters.blockBits V)).work≤480*(V+1) := by
 have hw:=powers_work (DFTModelSectorMapParameters.blockBits V)
 have hb:=DFTModelSectorMapParameters.blockBits_pos V
 have hs:=DFTModelSectorMapParameters.blockBits_square V
 nlinarith

theorem carry_work_linear {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V) :
 (run DFTModelSectorMapCarry.program (DFTModelSectorMapParameters.blockBits V,(V,d))).work≤392*(V+1) := by
 have hw:=DFTModelSectorMapCarry.program_work (DFTModelSectorMapParameters.blockBits V) V d g.starts_ordered
 have hp:=DFTModelSectorMapParameters.blockBits_pos V
 have hc:=DFTModelSectorMapParameters.clog_le_twice_blockBits d.len V count
 have hs:=DFTModelSectorMapParameters.packed_span V
 have hl:V/DFTModelSectorMapParameters.blockBits V+1≤
  (V/DFTModelSectorMapParameters.blockBits V+1)*DFTModelSectorMapParameters.blockBits V:=Nat.le_mul_of_pos_right _ hp
 nlinarith

theorem program_work_eq (V : ℕ) (d : Tape (ℕ×ℕ)) :
 (run program (V,d)).work=
 (run DFTModelSectorMapParameters.program V).work+(run sparse (V,d)).work+
 (run DFTModelSectorMapBits.pack (DFTModelSectorMapParameters.blockBits V,(V,marks V d))).work+
 (run DFTModelSectorMapBits.highTable (DFTModelSectorMapParameters.blockBits V)).work+
 (run powers (DFTModelSectorMapParameters.blockBits V)).work+
 (run DFTModelSectorMapCarry.program (DFTModelSectorMapParameters.blockBits V,(V,d))).work+
 (run finalMap (tables V d (DFTModelSectorMapParameters.blockBits V) (marks V d)
  (packedTable V d) (highTable V) (powerTable V) (carryTable V d))).work+122 := by
 unfold program
 rw [bind,bind_work,startBits_run]
 dsimp only [Bill.pay]
 rw [DFTModelSectorMapParameters.program_value]
 rw [bind,bind_work,startMarks_run]
 dsimp only [Bill.pay]
 rw [bind,bind_work,startPack_run]
 dsimp only [Bill.pay]
 rw [bind,bind_work,startHighs_run]
 dsimp only [Bill.pay]
 rw [bind,bind_work,startPowers_run]
 dsimp only [Bill.pay]
 rw [bind,bind_work,startCarry_run]
 dsimp only [Bill.pay]
 rw [finish_run]
 dsimp only [Bill.pay]
 dsimp only [marks,packedTable,highTable,powerTable,carryTable]
 omega

theorem program_work_linear {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (count:d.len≤V) :
 (run program (V,d)).work≤2000*(V+1) := by
 rw [program_work_eq]
 have p:=DFTModelSectorMapParameters.preparation_work_linear V (marks V d)
 have s:=sparse_work V d
 have w:=powers_work_linear V
 have c:=carry_work_linear g count
 have f:=finalMap_work V (DFTModelSectorMapParameters.blockBits V) d (marks V d)
  (packedTable V d) (highTable V) (powerTable V) (carryTable V d)
 omega

theorem program_valid {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) :
 (run program (V,d)).valid := by
 unfold program
 rw [bind,bind_valid,startBits_run]
 dsimp only [Bill.pay]
 rw [DFTModelSectorMapParameters.program_value]
 rw [bind,bind_valid,startMarks_run]
 dsimp only [Bill.pay]
 rw [bind,bind_valid,startPack_run]
 dsimp only [Bill.pay]
 rw [bind,bind_valid,startHighs_run]
 dsimp only [Bill.pay]
 rw [bind,bind_valid,startPowers_run]
 dsimp only [Bill.pay]
 rw [bind,bind_valid,startCarry_run]
 dsimp only [Bill.pay]
 rw [finish_run]
 dsimp only [Bill.pay]
 exact ⟨DFTModelSectorMapParameters.program_valid V,sparse_valid V d,
  DFTModelSectorMapBits.pack_valid _ _ _,DFTModelSectorMapBits.highTable_valid _,powers_valid _,
  DFTModelSectorMapCarry.program_valid _ _ d g.starts_ordered,finalMap_valid _ _ _ _ _ _ _ _⟩

end
end ExactFourierCircuits.DFTModelSectorMap
