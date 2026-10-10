import DFTModelCacheSpectrumBank

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSpectrumBank
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

def values (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) : Tape ℂ :=
  Tape.tab (7*n) (fun j=>if j<n then omega^j else
    DFTModelCacheSpectrumSum.value (ks.look ((j-n)/n) (Tape.empty ℂ))
      (omega^((j-n)%n)) n)

theorem program_value (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (n,(omega,ks))).val=values n omega ks := by
  rw [program_run]
  change (Bill.tab (7*n) (0:ℂ) (fun j=>run cell ((n,(omega,ks)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 1
  funext j
  rw [cell_run]
  by_cases hj:j<n
  · simp only [hj,↓reduceIte,Bill.pay]
    rw [power_run]
    exact DFTModelScalarPower.program_value j omega
  · simp only [hj,↓reduceIte,Bill.pay]
    rw [spectrum_run,DFTModelCacheSpectrumDFT.row_run]
    rfl

theorem program_length (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (n,(omega,ks))).val.len=7*n := by rw [program_value];rfl

theorem cell_valid (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run cell ((n,(omega,ks)),j)).valid := by
  rw [cell_run]
  by_cases hj:j<n
  · simp only [hj,↓reduceIte,Bill.pay]
    rw [power_run]
    exact DFTModelScalarPower.program_valid j omega
  · simp only [hj,↓reduceIte,Bill.pay]
    rw [spectrum_run,DFTModelCacheSpectrumDFT.row_run]
    trivial

theorem program_valid (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (n,(omega,ks))).valid := by
  rw [program_run]
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>cell_valid n j omega ks)

theorem cell_work (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) (hj:j<7*n) :
    (run cell ((n,(omega,ks)),j)).work≤82*n+140 := by
  rw [cell_run]
  by_cases h:j<n
  · simp only [h,↓reduceIte,Bill.pay]
    rw [power_run]
    dsimp only [Bill.pay]
    have hw:=DFTModelScalarPower.program_work j omega
    have hl:=Nat.log2_le_self (j+1)
    omega
  · simp only [h,↓reduceIte,Bill.pay]
    rw [spectrum_run,DFTModelCacheSpectrumDFT.row_run]
    dsimp only [Bill.pay,Bill.work]
    have hn:0<n:=by omega
    have hm:=Nat.mod_lt (j-n) hn
    have hw:=DFTModelScalarPower.program_work ((j-n)%n) omega
    have hl:=Nat.log2_le_self ((j-n)%n+1)
    omega

theorem program_work (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (n,(omega,ks))).work≤1200*(n+1)^2 := by
  rw [program_run]
  change (Bill.tab (7*n) (0:ℂ) (fun j=>run cell ((n,(omega,ks)),j))).work+6≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs:(∑j∈Finset.range (7*n),(run cell ((n,(omega,ks)),j)).work)≤
      (7*n)*(82*n+140) := by
    calc
      _ ≤ ∑j∈Finset.range (7*n),(82*n+140) := by
        apply Finset.sum_le_sum
        intro j hj
        exact cell_work n j omega ks (Finset.mem_range.mp hj)
      _ = _ := by simp [Nat.mul_comm]
  nlinarith

theorem cell_peak (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) (hj:j<7*n) :
    (run cell ((n,(omega,ks)),j)).peak≤7*n+7 := by
  rw [cell_run]
  by_cases h:j<n
  · simp only [h,↓reduceIte,Bill.pay]
    rw [power_run]
    dsimp only [Bill.pay]
    have hp:=DFTModelScalarPower.program_peak j omega
    omega
  · simp only [h,↓reduceIte,Bill.pay]
    rw [spectrum_run,DFTModelCacheSpectrumDFT.row_run]
    dsimp only [Bill.pay,Bill.peak]
    have hn:0<n:=by omega
    have hm:=Nat.mod_lt (j-n) hn
    have hp:=DFTModelScalarPower.program_peak ((j-n)%n) omega
    omega

theorem program_peak (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    (run program (n,(omega,ks))).peak≤7*n+7 := by
  rw [program_run]
  change max (Bill.tab (7*n) (0:ℂ) (fun j=>run cell ((n,(omega,ks)),j))).peak
    (max 7 (7*n))≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs:(Finset.range (7*n)).sup (fun j=>(run cell ((n,(omega,ks)),j)).peak)≤7*n+7 := by
    apply Finset.sup_le
    intro j hj
    exact cell_peak n j omega ks (Finset.mem_range.mp hj)
  omega

theorem source_power (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) (j:Fin n) :
    (run program (n,(omega,ks))).val.look j.val 0=omega^j.val := by
  rw [program_value]
  have hj:j.val<7*n:=by have:=j.isLt;omega
  simp [values,Tape.look,Tape.tab,hj,j.isLt]

theorem source_spectrum (n : ℕ) (ks : Tape (Tape ℂ)) (b:Fin 6) (j:Fin n) :
    (run program (n,(OAI.ExactFourier.zeta n,ks))).val.look (n+b.val*n+j.val) 0=
      (OAI.ExactFourier.fourierMatrix n).mulVec
        (fun i:Fin n=>(ks.look b.val (Tape.empty ℂ)).look i.val 0) j := by
  rw [program_value]
  have hn:0<n:=Nat.pos_of_ne_zero (by intro h;simpa [h] using j.isLt)
  have hj:=j.isLt
  have hb:=b.isLt
  have hbn:b.val*n+n≤6*n:=by nlinarith
  have hfit:n+b.val*n+j.val<7*n:=by omega
  have hdiff:n+b.val*n+j.val-n=b.val*n+j.val:=by omega
  have hdiv:(b.val*n+j.val)/n=b.val:=by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hmod:(b.val*n+j.val)%n=j.val:=by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hj]
  simp only [values,Tape.look,Tape.tab,hfit,↓reduceDIte,
    show ¬n+b.val*n+j.val<n by omega,↓reduceIte,hdiff,hdiv,hmod]
  have h:=DFTModelCacheSpectrumDFT.source_value n (ks.look b.val (Tape.empty ℂ))
    (fun i:Fin n=>(ks.look b.val (Tape.empty ℂ)).look i.val 0) (fun _=>rfl) j
  rw [DFTModelCacheSpectrumDFT.program_value] at h
  simpa only [Tape.look,Tape.tab,j.isLt,↓reduceDIte] using h

theorem source_sharedBank (K : ℕ) (ks : Tape (Tape ℂ))
    (f:Fin 6→Fin (UniformRadixTwoDAG.width K)→ℂ)
    (hf:∀b j,(ks.look b.val (Tape.empty ℂ)).look j.val 0=f b j)
    (i:Fin (UniformToeplitzCrossDAG.bankSize K)) :
    (run program (UniformRadixTwoDAG.width K,
      (OAI.ExactFourier.zeta (UniformRadixTwoDAG.width K),ks))).val.look i.val 0=
        UniformToeplitzCrossDAG.sharedBank K f i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.val_castAdd,UniformToeplitzCrossDAG.sharedBank,Fin.addCases_left] using
      source_power (UniformRadixTwoDAG.width K) _ ks j
  · intro q
    let bj:Fin 6×Fin (UniformRadixTwoDAG.width K):=finProdFinEquiv.symm q
    have hq:bj.1.val*UniformRadixTwoDAG.width K+bj.2.val=q.val := by
      have h:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
      change bj.2.val+UniformRadixTwoDAG.width K*bj.1.val=q.val at h
      simpa only [Nat.mul_comm,Nat.add_comm] using h
    have h:=source_spectrum (UniformRadixTwoDAG.width K) ks bj.1 bj.2
    have he:(fun j:Fin (UniformRadixTwoDAG.width K)=>
      (ks.look bj.1.val (Tape.empty ℂ)).look j.val 0)=f bj.1 := by
      funext j
      exact hf bj.1 j
    rw [he] at h
    simpa only [Fin.val_natAdd,UniformToeplitzCrossDAG.sharedBank,Fin.addCases_right,
      Nat.add_assoc,hq] using h

end
end ExactFourierCircuits.DFTModelCacheSpectrumBank
