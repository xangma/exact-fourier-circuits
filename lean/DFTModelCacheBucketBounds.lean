import DFTModelCacheBucketScanBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDAGDepth (nat)
noncomputable section
attribute [local irreducible] selector length orderCell directoryCell

def workBudget (G:ℕ):ℕ:=
  (selectBudget G+14)+2+4*((G+1)*G)+((G+1)*G)*(selectBudget G+16)+1+
  7+2+4*(G+2)+(G+2)*(selectBudget G+8)+1+1

private theorem peak_input_bound (N G:ℕ):G+1 ≤ selectPeak N G := by
  unfold selectPeak
  nlinarith
private theorem count_peak_bound (N G:ℕ):(G+1)*G ≤ selectPeak N G := by
  unfold selectPeak
  nlinarith
private theorem directory_peak_bound (N G:ℕ):G+2 ≤ selectPeak N G := by
  unfold selectPeak
  nlinarith
private theorem tab_work_arith (a n M C S:ℕ) (hn:n ≤ M) (hs:S ≤ n*C):
    a+(2+4*n+S)+1 ≤ a+2+4*M+M*C+1 := by
  have hm:=Nat.mul_le_mul_right C hn
  omega

private theorem finish_work_arith (a C A B T:ℕ) (ha:a ≤ C):
    a+2+A+B+1+T ≤ C+2+A+B+1+T := by omega

theorem projection_billing (b:Bill State.T) (w p:ℕ) (first:Bool):
    (((⟨(),w,p,True⟩:Bill Unit).pass (fun _=>b)).pay 1 0 |>.pass
      (fun s=>Bill.one (if first then s.1 else s.2))).pay 1 0=
    (⟨if first then b.val.1 else b.val.2,b.work+w+3,max p b.peak,b.valid⟩:Bill ℕ) := by
  simp only [Bill.pass,Bill.pay,Bill.one,true_and,and_true,max_zero]
  congr 1
  omega

theorem length_run (x:Input.T):run length x=
    ⟨(run selector (x,(x.2.1+1,0))).val.1,
      (run selector (x,(x.2.1+1,0))).work+14,
      max (x.2.1+1) (run selector (x,(x.2.1+1,0))).peak,
      (run selector (x,(x.2.1+1,0))).valid⟩ := by
  have hr:run fullRequest x=⟨(x,(x.2.1+1,0)),11,x.2.1+1,True⟩:=by
    simp [fullRequest,nat,count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [length]
  change (((run fullRequest x).pass (run selector)).pay 1 0 |>.pass
    (fun s=>Bill.one s.1)).pay 1 0=_
  rw [hr]
  exact projection_billing (run selector (x,(x.2.1+1,0))) 11 (x.2.1+1) true

theorem orderCell_run (x:Input.T) (j:ℕ):run orderCell (x,j)=
    ⟨(run selector (x,(x.2.1+1,j))).val.2,
      (run selector (x,(x.2.1+1,j))).work+16,
      max (x.2.1+1) (run selector (x,(x.2.1+1,j))).peak,
      (run selector (x,(x.2.1+1,j))).valid⟩ := by
  have hr:run (.fork (.atom .fst)
    (.fork (.comp (.atom .fst) (nat .add count (.atom (.lit 1)))) (.atom .snd)):
      Prog false (p Input w) Request) (x,j)=⟨(x,(x.2.1+1,j)),13,x.2.1+1,True⟩:=by
    simp [nat,count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [orderCell]
  change (((run (.fork (.atom .fst)
    (.fork (.comp (.atom .fst) (nat .add count (.atom (.lit 1)))) (.atom .snd))) (x,j)).pass
    (run selector)).pay 1 0 |>.pass (fun s=>Bill.one s.2)).pay 1 0=_
  rw [hr]
  exact projection_billing (run selector (x,(x.2.1+1,j))) 13 (x.2.1+1) false

theorem directoryCell_run (x:Input.T) (l:ℕ):run directoryCell (x,l)=
    ⟨(run selector (x,(l,0))).val.1,(run selector (x,(l,0))).work+8,
      (run selector (x,(l,0))).peak,(run selector (x,(l,0))).valid⟩ := by
  rw [directoryCell]
  have hr:run (.fork (.atom .fst) (.fork (.atom .snd) (.atom (.lit 0))):
      Prog false (p Input w) Request) (x,l)=⟨(x,(l,0)),5,0,True⟩:=by
    simp [run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass]
  change (((run (.fork (.atom .fst) (.fork (.atom .snd) (.atom (.lit 0)))) (x,l)).pass
    (run selector)).pay 1 0 |>.pass (fun s=>Bill.one s.1)).pay 1 0=_
  rw [hr]
  exact projection_billing (run selector (x,(l,0))) 5 0 true

theorem length_bound (x:Input.T):
    (run length x).valid ∧ (run length x).work ≤ selectBudget x.2.1+14 ∧
    (run length x).peak ≤ selectPeak x.1 x.2.1 ∧
    (run length x).val ≤ (x.2.1+1)*x.2.1 := by
  have hs:=selector_bound x (x.2.1+1) 0 (le_refl _)
  have hc:=UniformDAGBucketMachine.offset_bound x.2.1 (x.2.1+1) (depthValue x)
  rw [length_run]
  dsimp only [Bill.valid,Bill.work,Bill.peak,Bill.val]
  rw [selector_value]
  refine ⟨hs.1,by omega,?_,hc⟩
  apply max_le ?_ hs.2.2
  exact peak_input_bound x.1 x.2.1

theorem orderCell_bound (x:Input.T) (j:ℕ):
    (run orderCell (x,j)).valid ∧ (run orderCell (x,j)).work ≤ selectBudget x.2.1+16 ∧
    (run orderCell (x,j)).peak ≤ selectPeak x.1 x.2.1 := by
  have hs:=selector_bound x (x.2.1+1) j (le_refl _)
  rw [orderCell_run]
  refine ⟨hs.1,by dsimp only [Bill.work];omega,?_⟩
  dsimp only [Bill.peak]
  apply max_le ?_ hs.2.2
  exact peak_input_bound x.1 x.2.1

theorem directoryCell_bound (x:Input.T) (l:ℕ) (hl:l<x.2.1+2):
    (run directoryCell (x,l)).valid ∧ (run directoryCell (x,l)).work ≤ selectBudget x.2.1+8 ∧
    (run directoryCell (x,l)).peak ≤ selectPeak x.1 x.2.1 := by
  have hs:=selector_bound x l 0 (by omega)
  rw [directoryCell_run]
  exact ⟨hs.1,Nat.add_le_add_right hs.2.1 8,hs.2.2⟩

/-- Generic billing for actual Nat array tabulation. Used below only with
concrete closed count and cell producers. -/
theorem tab_bound {s:Ty} (n:Prog false s w) (b:Prog false (p s w) w) (x:s.T)
    (M C P:ℕ) (hn:(run n x).valid) (hm:(run n x).val ≤ M)
    (hp:(run n x).peak ≤ P) (hM:M ≤ P)
    (hb:∀j,j<(run n x).val→(run b (x,j)).valid ∧ (run b (x,j)).work ≤ C ∧ (run b (x,j)).peak ≤ P):
    (run (.tab n b) x).valid ∧
    (run (.tab n b) x).work ≤ (run n x).work+2+4*M+M*C+1 ∧
    (run (.tab n b) x).peak ≤ P := by
  have hs:(∑j∈Finset.range (run n x).val,(run b (x,j)).work) ≤ (run n x).val*C := by
    calc
      _ ≤ ∑_j∈Finset.range (run n x).val,C:=Finset.sum_le_sum (fun j hj=>(hb j (Finset.mem_range.mp hj)).2.1)
      _ = (run n x).val*C:=by simp
  have hpeak:(Finset.range (run n x).val).sup (fun j=>(run b (x,j)).peak) ≤ P := by
    exact Finset.sup_le (fun j hj=>(hb j (Finset.mem_range.mp hj)).2.2)
  have hv:∀j,j<(run n x).val→(run b (x,j)).valid:=fun j hj=>(hb j hj).1
  simp only [run] at *
  simp only [Code.run,Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_valid,ModelEquivalenceInterpreter.tab_work,
    ModelEquivalenceInterpreter.tab_peak]
  change ((run n x).valid ∧ ∀j,j<(run n x).val→(run b (x,j)).valid) ∧
    (run n x).work+(2+4*(run n x).val+∑j∈Finset.range (run n x).val,(run b (x,j)).work)+1 ≤ _ ∧
    max (max (run n x).peak (max (run n x).val
      ((Finset.range (run n x).val).sup (fun j=>(run b (x,j)).peak)))) 0 ≤ _
  refine ⟨⟨hn,hv⟩,tab_work_arith _ _ M C _ hm hs,?_⟩
  exact max_le (max_le hp (max_le (hm.trans hM) hpeak)) (Nat.zero_le _)

theorem program_bound (x:Input.T):
    (run program x).valid ∧ (run program x).work ≤ workBudget x.2.1 ∧
    (run program x).peak ≤ selectPeak x.1 x.2.1 := by
  have hl:=length_bound x
  have hM:(x.2.1+1)*x.2.1 ≤ selectPeak x.1 x.2.1:=count_peak_bound x.1 x.2.1
  have ho:=tab_bound length orderCell x ((x.2.1+1)*x.2.1) (selectBudget x.2.1+16)
    (selectPeak x.1 x.2.1) hl.1 hl.2.2.2 hl.2.2.1 hM (fun j _=>orderCell_bound x j)
  have hc:run (nat .add count (.atom (.lit 2))) x=⟨x.2.1+2,7,x.2.1+2,True⟩:=by
    simp [nat,count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  have hd:=tab_bound (nat .add count (.atom (.lit 2))) directoryCell x (x.2.1+2) (selectBudget x.2.1+8)
    (selectPeak x.1 x.2.1) (by rw [hc];trivial) (by rw [hc])
    (by rw [hc];exact directory_peak_bound _ _) (directory_peak_bound _ _)
    (fun j hj=>directoryCell_bound x j (by simpa only [hc] using hj))
  rw [hc] at hd
  dsimp only [Bill.work] at hd
  change (run order x).valid ∧ (run order x).work ≤ _ ∧ (run order x).peak ≤ _ at ho
  change (run directory x).valid ∧ (run directory x).work ≤ _ ∧ (run directory x).peak ≤ _ at hd
  rw [program]
  change ((run order x).valid ∧ (run directory x).valid ∧ True) ∧
    (run order x).work+((run directory x).work+1) ≤ _ ∧
    max (run order x).peak (max (run directory x).peak 0) ≤ _
  refine ⟨⟨ho.1,hd.1,trivial⟩,?_,by omega⟩
  calc
    _ ≤ ((run length x).work+2+4*((x.2.1+1)*x.2.1)+
        ((x.2.1+1)*x.2.1)*(selectBudget x.2.1+16)+1)+
        ((7+2+4*(x.2.1+2)+(x.2.1+2)*(selectBudget x.2.1+8)+1)+1) :=
      Nat.add_le_add ho.2.1 (Nat.add_le_add_right hd.2.1 1)
    _ ≤ (selectBudget x.2.1+14)+2+4*((x.2.1+1)*x.2.1)+
        ((x.2.1+1)*x.2.1)*(selectBudget x.2.1+16)+1+
        ((7+2+4*(x.2.1+2)+(x.2.1+2)*(selectBudget x.2.1+8)+1)+1) :=
      finish_work_arith _ _ _ _ _ hl.2.1
    _ = workBudget x.2.1 := by unfold workBudget;ring

end
end ExactFourierCircuits.DFTModelCacheBucket
