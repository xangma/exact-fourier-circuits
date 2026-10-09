import DFTModelCRTRecursion

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def TableBound (V : ℕ) (t : Tape (ℕ × ℕ)) : Prop :=
  ∀j<t.len,(t.look j (0,0)).1<V ∧ (t.look j (0,0)).2<V

theorem prefix_bound (k : ℕ) (x : Args.T) (positive : 0<x.2.1) :
    TableBound x.2.1 (prefixTable k x) := by
  cases k with
  | zero =>
      intro j hj
      simp only [prefixTable,Tape.tab] at hj ⊢
      simp [Tape.look,hj,positive]
  | succ k =>
      intro j hj
      change j < (readRow x).1*(prefixTable k (successor x)).len at hj
      change ((Tape.tab _ (valueCell x (prefixTable k (successor x)))).look j (0,0)).1 < _ ∧
        ((Tape.tab _ (valueCell x (prefixTable k (successor x)))).look j (0,0)).2 < _
      simp only [Tape.look,Tape.tab,hj,↓reduceDIte,valueCell]
      exact ⟨Nat.mod_lt _ positive,Nat.mod_lt _ positive⟩

theorem cell_peak_le (x : Args.T) (t : Tape (ℕ × ℕ)) (V j : ℕ)
    (lengthPositive : 0<t.len) (lengthBound : t.len≤V) (indexBound : j≤V)
    (table : TableBound V t)
    (alphaBound : (readRow x).2.1≤V) (betaBound : (readRow x).2.2≤V) :
    (run cell ((x,t),j)).peak ≤ (V+1)^2 := by
  have modlt : j%t.len<t.len := Nat.mod_lt _ lengthPositive
  obtain ⟨av,bv⟩ := table _ modlt
  have db : j/t.len≤V := (Nat.div_le_self _ _).trans indexBound
  have mb : j%t.len≤V := (Nat.mod_le _ _).trans indexBound
  have am : (j/t.len)*(readRow x).2.1≤V*V := Nat.mul_le_mul db alphaBound
  have bm : (j/t.len)*(readRow x).2.2≤V*V := Nat.mul_le_mul db betaBound
  have aa : (t.look (j%t.len) (0,0)).1+(j/t.len)*(readRow x).2.1≤(V+1)^2 := by
    nlinarith
  have ba : (t.look (j%t.len) (0,0)).2+(j/t.len)*(readRow x).2.2≤(V+1)^2 := by
    nlinarith
  have ar := Nat.mod_le ((t.look (j%t.len) (0,0)).1+(j/t.len)*(readRow x).2.1) x.2.1
  have br := Nat.mod_le ((t.look (j%t.len) (0,0)).2+(j/t.len)*(readRow x).2.2) x.2.1
  have vv : V≤(V+1)^2 := by nlinarith
  simp only [cell,alphaCell,betaCell,nat,oldEntry,oldIndex,old,oldLength,digit,
    alphaWeight,betaWeight,cellRow,row,cellArgs,volume,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,
    max_le_iff]
  simp only [readRow] at alphaBound betaBound am bm aa ba ar br
  omega

theorem extend_peak_le (x : Args.T) (t : Tape (ℕ × ℕ)) (V : ℕ)
    (lengthPositive : 0<t.len) (lengthBound : t.len≤V)
    (outputBound : (readRow x).1*t.len≤V) (table : TableBound V t)
    (alphaBound : (readRow x).2.1≤V) (betaBound : (readRow x).2.2≤V) :
    (run extend (x,t)).peak ≤ (V+1)^2 := by
  change max (max (run extendedLength (x,t)).peak
    (Bill.tab (run extendedLength (x,t)).val Entry.blank
      (fun j => run cell ((x,t),j))).peak) 0 ≤ _
  rw [extendedLength_run,ModelEquivalenceInterpreter.tab_peak]
  dsimp only [Bill.val,Bill.peak]
  have vv : V≤(V+1)^2 := by nlinarith
  refine max_le (max_le (max_le (lengthBound.trans vv) (outputBound.trans vv))
    (max_le (outputBound.trans vv) ?_)) (by omega)
  apply Finset.sup_le
  intro j hj
  exact cell_peak_le x t V j lengthPositive lengthBound
    (by have := Finset.mem_range.mp hj;omega) table alphaBound betaBound

def RowsTwo (k : ℕ) (x : Args.T) : Prop :=
  ∀i<k,2≤(x.2.2.look (x.1+i) (0,(0,0))).1
def WeightsBound (k : ℕ) (x : Args.T) (V : ℕ) : Prop :=
  ∀i<k,(x.2.2.look (x.1+i) (0,(0,0))).2.1≤V ∧
    (x.2.2.look (x.1+i) (0,(0,0))).2.2≤V

theorem prefix_positive (k : ℕ) (x : Args.T) (rows : RowsTwo k x) :
    0<(prefixTable k x).len := by
  induction k generalizing x with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
      change 0<(readRow x).1*(prefixTable k (successor x)).len
      apply Nat.mul_pos
      · have h : 2≤(readRow x).1 := by simpa [readRow] using rows 0 (by omega)
        omega
      · apply ih
        intro i hi
        simpa [successor,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using rows (i+1) (by omega)

theorem base_peak (x : Args.T) : (run base x).peak=1 := by
  simp [base,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    Bill.tab,Bill.sow,Bill.steps,Ty.blank]

theorem depth_peak_le (k : ℕ) (x : Args.T) (V : ℕ)
    (positive : 0<V) (volumeEq : x.2.1=V) (indexBound : x.1+k≤V)
    (rows : RowsTwo k x) (weights : WeightsBound k x V)
    (lengthBound : (prefixTable k x).len≤V) :
    (depthRun (run base) (Code.run step) k x).peak ≤ (V+1)^2 := by
  change (x.1:ℕ)+k≤V at indexBound
  have vv : V≤(V+1)^2 := by nlinarith
  induction k generalizing x with
  | zero =>
      change max (run base x).peak 0≤_
      rw [base_peak]
      simp only [max_zero]
      omega
  | succ k ih =>
      have row : 2≤(readRow x).1 := by simpa [readRow] using rows 0 (by omega)
      have childRows : RowsTwo k (successor x) := by
        intro i hi
        simpa [successor,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using rows (i+1) (by omega)
      have childWeights : WeightsBound k (successor x) V := by
        intro i hi
        simpa [successor,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using weights (i+1) (by omega)
      have outputBound : (readRow x).1*(prefixTable k (successor x)).len≤V := lengthBound
      have childLength : (prefixTable k (successor x)).len≤V := by nlinarith
      have cb := ih (successor x) volumeEq childRows childWeights childLength
        (by simpa [successor,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using indexBound)
      have pb : TableBound V (prefixTable k (successor x)) := by
        simpa [successor,volumeEq] using prefix_bound k (successor x) (by simpa [successor,volumeEq])
      have eb := extend_peak_le x (prefixTable k (successor x)) V
        (prefix_positive k _ childRows) childLength outputBound pb
        (by simpa [readRow] using (weights 0 (by omega)).1)
        (by simpa [readRow] using (weights 0 (by omega)).2)
      simp only [depthRun,step_run,Bill.pay]
      rw [depth_value]
      have ib : x.1+1≤V :=
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) x.1).trans indexBound
      have kb : k+1≤V := (Nat.le_add_left (k+1) x.1).trans indexBound
      exact max_le (max_le (ib.trans vv) (max_le cb eb)) (kb.trans vv)

theorem tables_peak_le (k : ℕ) (x : Args.T) (V : ℕ)
    (positive : 0<V) (volumeEq : x.2.1=V) (indexBound : x.1+k≤V)
    (rows : RowsTwo k x) (weights : WeightsBound k x V)
    (lengthBound : (prefixTable k x).len≤V) :
    (run tables (k,x)).peak ≤ (V+1)^2 := by
  change (x.1:ℕ)+k≤V at indexBound
  have vv : V≤(V+1)^2 := by nlinarith
  exact max_le (depth_peak_le k x V positive volumeEq indexBound rows weights lengthBound)
    (((Nat.le_add_left k x.1).trans indexBound).trans vv)

end
end ExactFourierCircuits.DFTModelCRT
