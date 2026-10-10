import DFTModelCacheColorSelectionStepBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorSelection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheHeight (Words words_mono words_blank degree literals degree_positive straight_words)
open DFTModelCacheColor (Row)
noncomputable section
attribute [local irreducible] selector step row count

def selectBudget (S:ℕ) : ℕ := 111+1001*S
def workBudget (S:ℕ) : ℕ := selectBudget S+6+2+4*S+S*(selectBudget S+2)+1
/-- The exponent is a fixed constant determined by the actual finite expression AST. -/
def wordDegree : ℕ := degree row*degree step+degree count+1
def peakBudget (B:ℕ) : ℕ := (2*B+2)^wordDegree

theorem rowsPrefix_length (x:Input.T) (j:ℕ) : (rowsPrefix x j).length ≤ j := by
  calc
    _ ≤ (List.range j).length:=List.length_filterMap_le _ _
    _ = j:=List.length_range

theorem advance_count (x:Input.T) (q j:ℕ) (s:State.T) : (advance x q j s).1 ≤ s.1+1 := by
  unfold advance
  split_ifs <;> first | exact le_refl _ | exact Nat.le_succ _

theorem steps_count (x:Input.T) (q j:ℕ) : (steps x q j).val.1 ≤ j := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    change (run step ((x,q),(j,(steps x q j).val))).val.1 ≤ j+1
    rw [step_value]
    exact (advance_count _ _ _ _).trans (Nat.add_le_add_right ih 1)

theorem steps_valid (x:Input.T) (q j:ℕ) : (steps x q j).valid := by
  induction j with
  | zero=>trivial
  | succ j ih=>exact ⟨ih,step_valid _ _ _ _⟩

theorem steps_work (x:Input.T) (q j:ℕ) : (steps x q j).work ≤ 1+1001*j := by
  induction j with
  | zero=>simp only [steps,Bill.steps,Bill.one];omega
  | succ j ih=>
    have hh:=step_work x q j (steps x q j).val
    change (steps x q j).work+(run step ((x,q),(j,(steps x q j).val))).work+1 ≤ _
    omega

private theorem pow_contains (B d:ℕ) (hB:2 ≤ B) (hd:1 ≤ d) : B ≤ B^d :=
  le_self_pow (by omega) (by omega)

theorem row_words (x:Input.T) (M j:ℕ) (hM:5 ≤ M) (hx:Words Input M x) (hj:j ≤ M) :
    Words Row (M^degree row) (rowValue x j) := by
  have h:=straight_words row (by with_unfolding_all decide) () M (by omega)
    (show literals row ≤ M from (show literals row ≤ 5 by with_unfolding_all decide).trans hM) (x,j) ⟨hx,hj⟩
  rw [←row_value];exact h.1

theorem steps_row_words (x:Input.T) (q M j:ℕ) (hM:5 ≤ M) (hx:Words Input M x) (hj:j ≤ M) :
    Words Row (M^degree row) (steps x q j).val.2 := by
  induction j with
  | zero=>exact words_blank Row _
  | succ j ih=>
    have old:=ih (by omega)
    have fresh:=row_words x M j hM hx (by omega)
    change Words Row (M^degree row) (run step ((x,q),(j,(steps x q j).val))).val.2
    rw [step_value]
    unfold advance
    split_ifs <;>assumption

private theorem degree_step_le : degree row*degree step ≤ wordDegree := by
  unfold wordDegree;omega
private theorem degree_count_le : degree count ≤ wordDegree := by
  unfold wordDegree;omega
private theorem wordDegree_positive : 1 ≤ wordDegree := by unfold wordDegree;omega

theorem steps_peak (x:Input.T) (q M j:ℕ) (hM:5 ≤ M) (hx:Words Input M x)
    (hq:q ≤ M) (hj:j ≤ M) : (steps x q j).peak ≤ M^wordDegree := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have old:=ih (by omega)
    have hc:=steps_count x q j
    have hr:=steps_row_words x q M j hM hx (by omega)
    have hm:M ≤ M^degree row:=pow_contains M _ (by omega) (degree_positive row)
    have jM:j ≤ M:=(Nat.le_succ j).trans hj
    have cursor:Words Cursor (M^degree row) ((x,q),(j,(steps x q j).val)):=
      ⟨⟨words_mono _ hm _ hx,hq.trans hm⟩,jM.trans hm,⟨(hc.trans jM).trans hm,hr⟩⟩
    have hp:=straight_words step (by with_unfolding_all decide) () (M^degree row) ((show 2 ≤ M by omega).trans hm)
      ((show literals step ≤ 5 by with_unfolding_all decide).trans (hM.trans hm)) _ cursor
    rw [←pow_mul] at hp
    have he:M^(degree row*degree step) ≤ M^wordDegree:=Nat.pow_le_pow_right (by omega) degree_step_le
    change max (max (steps x q j).peak (run step ((x,q),(j,(steps x q j).val))).peak) (j+1) ≤ _
    exact max_le (max_le old (hp.2.trans he)) (hj.trans (pow_contains M _ (by omega) wordDegree_positive))

theorem selector_run (x:Input.T) (q:ℕ) : run selector (x,q)=
    ⟨(steps x q (x.2.1.len)).val,
      (run count x).work+(steps x q (x.2.1.len)).work+10,
      max (run count x).peak (steps x q (x.2.1.len)).peak,
      (run count x).valid ∧ (steps x q (x.2.1.len)).valid⟩ := by
  have hn:run (.comp (.atom .fst) count:Prog false Request w) (x,q)=
      ⟨(run count x).val,(run count x).work+2,(run count x).peak,(run count x).valid⟩:=by
    simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,true_and]
    congr 1
    omega
  have hi:run (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0))
      (.fork (.atom (.lit 0)) (.atom (.lit 0)))):Prog false Request State) (x,q)=
      ⟨(0,(0,(0,0))),7,0,True⟩:=by
    simp [run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass]
  rw [selector]
  change ((run (.comp (.atom .fst) count:Prog false Request w) (x,q)).pass (fun l=>
    (run (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0))
      (.fork (.atom (.lit 0)) (.atom (.lit 0)))):Prog false Request State) (x,q)).pass
      (fun st=>Bill.steps st (fun i z=>run step ((x,q),(i,z))) l))).pay 1 0=_
  rw [hn,hi]
  simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  rw [count_value]
  change (⟨(steps x q (x.2.1.len)).val,
    (run count x).work+2+(7+(steps x q (x.2.1.len)).work)+1,
    max (run count x).peak (steps x q (x.2.1.len)).peak,
    (run count x).valid ∧ (steps x q (x.2.1.len)).valid⟩:Bill State.T)=_
  congr 1
  omega

theorem selector_bound (x:Input.T) (q M:ℕ) (hM:5 ≤ M) (hx:Words Input M x)
    (hq:q ≤ M) (hS:x.2.1.len ≤ M) :
    (run selector (x,q)).valid ∧ (run selector (x,q)).work ≤ selectBudget (x.2.1.len) ∧
    (run selector (x,q)).peak ≤ M^wordDegree := by
  have hw:=steps_work x q (x.2.1.len)
  have hp:=steps_peak x q M (x.2.1.len) hM hx hq hS
  have hs:=straight_words count (by with_unfolding_all decide) () M (by omega)
    ((show literals count ≤ 5 by with_unfolding_all decide).trans hM) x hx
  have he:M^degree count ≤ M^wordDegree:=Nat.pow_le_pow_right (by omega) degree_count_le
  rw [selector_run]
  refine ⟨⟨count_valid _,steps_valid _ _ _⟩,?_,max_le (hs.2.trans he) hp⟩
  have hh:=count_work x
  dsimp only [Bill.work]
  unfold selectBudget
  omega

theorem length_run (x:Input.T) : run length x=
    ⟨(run selector (x,0)).val.1,(run selector (x,0)).work+6,
      (run selector (x,0)).peak,(run selector (x,0)).valid⟩ := by
  rw [length]
  simp only [run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem rowCell_run (x:Input.T) (j:ℕ) : run rowCell (x,j)=
    ⟨(run selector (x,j)).val.2,(run selector (x,j)).work+2,
      (run selector (x,j)).peak,(run selector (x,j)).valid⟩ := by
  rw [rowCell]
  simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,max_zero,and_true]

private theorem tab_work_arith (a n M C S:ℕ) (hn:n ≤ M) (hs:S ≤ n*C) :
    a+(2+4*n+S)+1 ≤ a+2+4*M+M*C+1 := by
  have hm:=Nat.mul_le_mul_right C hn
  omega

theorem tab_bound {s t:Ty} (n:Prog false s w) (b:Prog false (p s w) t) (x:s.T)
    (M C P:ℕ) (hn:(run n x).valid) (hm:(run n x).val ≤ M)
    (hp:(run n x).peak ≤ P) (hM:M ≤ P)
    (hb:∀j,j<(run n x).val→(run b (x,j)).valid ∧ (run b (x,j)).work ≤ C ∧ (run b (x,j)).peak ≤ P) :
    (run (.tab n b) x).valid ∧
    (run (.tab n b) x).work ≤ (run n x).work+2+4*M+M*C+1 ∧
    (run (.tab n b) x).peak ≤ P := by
  have hs:(∑j∈Finset.range (run n x).val,(run b (x,j)).work) ≤ (run n x).val*C := by
    calc
      _ ≤ ∑_j∈Finset.range (run n x).val,C:=Finset.sum_le_sum (fun j hj=>(hb j (Finset.mem_range.mp hj)).2.1)
      _ = (run n x).val*C:=by simp
  have hpeak:(Finset.range (run n x).val).sup (fun j=>(run b (x,j)).peak) ≤ P :=
    Finset.sup_le (fun j hj=>(hb j (Finset.mem_range.mp hj)).2.2)
  have hv:∀j,j<(run n x).val→(run b (x,j)).valid:=fun j hj=>(hb j hj).1
  simp only [run] at *
  simp only [Code.run,Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_valid,ModelEquivalenceInterpreter.tab_work,
    ModelEquivalenceInterpreter.tab_peak]
  change ((run n x).valid ∧ ∀j,j<(run n x).val→(run b (x,j)).valid) ∧
    (run n x).work+(2+4*(run n x).val+∑j∈Finset.range (run n x).val,(run b (x,j)).work)+1 ≤ _ ∧
    max (max (run n x).peak (max (run n x).val
      ((Finset.range (run n x).val).sup (fun j=>(run b (x,j)).peak)))) 0 ≤ _
  exact ⟨⟨hn,hv⟩,tab_work_arith _ _ M C _ hm hs,
    max_le (max_le hp (max_le (hm.trans hM) hpeak)) (Nat.zero_le _)⟩

theorem program_bound_at (x:Input.T) (M:ℕ) (hM:5 ≤ M) (hx:Words Input M x)
    (hS:x.2.1.len ≤ M) :
    (run program x).valid ∧ (run program x).work ≤ workBudget (x.2.1.len) ∧
    (run program x).peak ≤ M^wordDegree := by
  have hl:=selector_bound x 0 M hM hx (Nat.zero_le _) hS
  have hn:(run length x).valid:=by rw [length_run];exact hl.1
  have hp:(run length x).peak ≤ M^wordDegree:=by rw [length_run];exact hl.2.2
  have hw:(run length x).work ≤ selectBudget (x.2.1.len)+6:=by
    rw [length_run];exact Nat.add_le_add_right hl.2.1 6
  have hc:(run length x).val ≤ x.2.1.len:=by rw [length_value];exact rowsPrefix_length _ _
  have hSP:x.2.1.len ≤ M^wordDegree:=hS.trans (pow_contains M _ (by omega) wordDegree_positive)
  have hb:∀j,j<(run length x).val→(run rowCell (x,j)).valid ∧
      (run rowCell (x,j)).work ≤ selectBudget (x.2.1.len)+2 ∧ (run rowCell (x,j)).peak ≤ M^wordDegree:=by
    intro j hj
    have hh:=selector_bound x j M hM hx (((Nat.le_of_lt hj).trans hc).trans hS) hS
    rw [rowCell_run]
    exact ⟨hh.1,Nat.add_le_add_right hh.2.1 2,hh.2.2⟩
  have hh:=tab_bound length rowCell x (x.2.1.len) (selectBudget (x.2.1.len)+2)
    (M^wordDegree) hn hc hp hSP hb
  change (run program x).valid ∧ _ at hh
  refine ⟨hh.1,?_,hh.2.2⟩
  calc
    _ ≤ (run length x).work+2+4*x.2.1.len+x.2.1.len*(selectBudget (x.2.1.len)+2)+1:=hh.2.1
    _ ≤ (selectBudget (x.2.1.len)+6)+2+4*x.2.1.len+x.2.1.len*(selectBudget (x.2.1.len)+2)+1:=by omega
    _ = workBudget (x.2.1.len):=rfl

/-- Physical addresses bound integer peaks only. Allocation/work depends on row count. -/
theorem program_bound (x:Input.T) (B:ℕ) (hB:5≤B) (hx:Words Input B x) :
 (run program x).valid ∧ (run program x).work≤workBudget x.2.1.len ∧
 (run program x).peak≤B^wordDegree :=
 program_bound_at x B hB hx hx.2.1.1

theorem selector_work (x:Input.T) (q:ℕ) :
    (run selector (x,q)).work ≤ selectBudget (x.2.1.len) := by
  have hs:=count_work x
  have hh:=steps_work x q (x.2.1.len)
  rw [selector_run]
  dsimp only [Bill.work]
  unfold selectBudget
  omega

/-- Validity and work require no input-word bound or topological certificate. -/
theorem program_valid (x:Input.T) : (run program x).valid :=
  DFTModelCacheTraversal.indexCode_valid program (by with_unfolding_all decide) () x

theorem program_work (x:Input.T) : (run program x).work ≤ workBudget (x.2.1.len) := by
  have hc:(run length x).val ≤ x.2.1.len:=by rw [length_value];exact rowsPrefix_length _ _
  have hw:(run length x).work ≤ selectBudget (x.2.1.len)+6:=by
    rw [length_run];exact Nat.add_le_add_right (selector_work x 0) 6
  have hb:∀j,(run rowCell (x,j)).work ≤ selectBudget (x.2.1.len)+2:=by
    intro j
    rw [rowCell_run]
    exact Nat.add_le_add_right (selector_work x j) 2
  have hs:(∑j∈Finset.range (run length x).val,(run rowCell (x,j)).work) ≤
      (run length x).val*(selectBudget (x.2.1.len)+2):=by
    calc
      _ ≤ ∑_j∈Finset.range (run length x).val,(selectBudget (x.2.1.len)+2):=
        Finset.sum_le_sum (fun j _=>hb j)
      _ = _:=by simp
  change (run length x).work+(Bill.tab (run length x).val Row.blank (fun j=>run rowCell (x,j))).work+1 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  exact (tab_work_arith _ _ _ _ _ hc hs).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hw 2) (4*x.2.1.len))
      (x.2.1.len*(selectBudget (x.2.1.len)+2))) 1)

theorem workBudget_polynomial (S:ℕ) : workBudget S ≤ 1200*(S+1)^2 := by
  unfold workBudget selectBudget
  nlinarith

theorem program_work_polynomial (x:Input.T) :
    (run program x).work ≤ 1200*(x.2.1.len+1)^2 :=
  (program_work x).trans (workBudget_polynomial _)

end
end ExactFourierCircuits.DFTModelCacheColorSelection
