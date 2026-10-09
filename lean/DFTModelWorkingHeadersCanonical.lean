import DFTModelWorkingHeadersScan

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def suffix (ell j : ℕ) : Tape ℕ :=
  Tape.tab (ell-j) (fun i => UniformWorkingLength.oddPrime (j+i))

theorem tape_ext {u v : Tape ℕ} (hl : u.len=v.len)
    (hv : ∀i,i<u.len→u.look i 0=v.look i 0) : u=v := by
  cases u with | mk l f =>
    cases v with | mk m g =>
      dsimp only at hl
      subst m
      congr
      funext i
      simpa [Tape.look,i.isLt] using hv i.val i.isLt

theorem suffix_end (ell : ℕ) : suffix ell ell=Tape.empty ℕ := by
  apply tape_ext (by simp [suffix,Tape.tab,Tape.empty])
  intro i hi
  simp [suffix,Tape.tab] at hi

theorem suffix_cons (ell j : ℕ) (hj : j<ell) :
    cons (UniformWorkingLength.oddPrime j) (suffix ell (j+1))=suffix ell j := by
  have hl : ell-(j+1)+1=ell-j := by omega
  apply tape_ext (by simpa only [cons_len,suffix,Tape.tab] using hl)
  intro i hi
  have hi' : i<ell-j := by simpa only [cons_len,suffix,Tape.tab,hl] using hi
  rw [Tape.look_of_lt _ _ hi,Tape.look_of_lt _ _ hi']
  change (if i=0 then UniformWorkingLength.oddPrime j else
    (suffix ell (j+1)).look (i-1) 0)=UniformWorkingLength.oddPrime (j+i)
  by_cases hz : i=0
  · simp [hz]
  · have htail : i-1<ell-(j+1) := by omega
    simp only [hz,ite_false]
    rw [Tape.look_of_lt _ _ htail]
    change UniformWorkingLength.oddPrime (j+1+(i-1))=UniformWorkingLength.oddPrime (j+i)
    congr 1
    omega

theorem scan_canonical (n : ℕ) (hn : 0<n) (p j f : ℕ)
    (h3 : 3≤p) (hp : p≤UniformWorkingLength.nextPrime n)
    (hc : Nat.primeCounting' p=j+1)
    (hf : UniformWorkingLength.nextPrime n-p+1≤f) :
    scan n p (UniformWorkingLength.primeProduct j) f=
      (UniformWorkingLength.oddProduct n,suffix (UniformWorkingLength.axisCount n) j) := by
  induction f generalizing p j with
  | zero => omega
  | succ f ih =>
    by_cases he : p=UniformWorkingLength.nextPrime n
    · have hpr : Nat.Prime p := he ▸ UniformWorkingLength.oddPrime_prime _
      have hcheck := (UniformWorkingPreparation.trialPrime_true p).2 hpr
      have hj : j=UniformWorkingLength.axisCount n := by
        have hq := UniformWorkingLength.oddPrime_count (UniformWorkingLength.axisCount n)
        change Nat.primeCounting' (UniformWorkingLength.nextPrime n)=_ at hq
        rw [he] at hc
        omega
      have hprod : 2*n<UniformWorkingLength.primeProduct j*p := by
        simpa only [hj,he,UniformWorkingLength.oddProduct] using (UniformWorkingLength.maximal_product hn).2
      simp only [scan,hcheck,ite_true,hprod]
      rw [hj,suffix_end]
      rfl
    · have hlt : p<UniformWorkingLength.nextPrime n := by omega
      by_cases hpr : Nat.Prime p
      · have hcheck := (UniformWorkingPreparation.trialPrime_true p).2 hpr
        have hjp := UniformWorkingPreparation.prime_of_count hpr hc
        have hj : j<UniformWorkingLength.axisCount n := by
          by_contra h
          have hq := UniformWorkingLength.oddPrime_strictMono.monotone
            (show UniformWorkingLength.axisCount n≤j by omega)
          rw [←hjp] at hq
          change UniformWorkingLength.nextPrime n≤p at hq
          omega
        have hnew : UniformWorkingLength.primeProduct j*p=UniformWorkingLength.primeProduct (j+1) := by
          rw [hjp,UniformWorkingLength.primeProduct]
        have hnprod : UniformWorkingLength.primeProduct (j+1)≤2*n :=
          (UniformWorkingLength.primeProduct_strictMono.monotone (by omega)).trans
            (UniformWorkingLength.maximal_product hn).1
        have hnot : ¬2*n<UniformWorkingLength.primeProduct (j+1) := by omega
        have hc' : Nat.primeCounting' (p+1)=(j+1)+1 := by
          simp only [UniformWorkingPreparation.counting_succ,hpr,ite_true,hc]
        have ht := ih (p+1) (j+1) (by omega) (by omega) hc' (by omega)
        simp only [scan,hcheck,ite_true,hnew,hnot,ite_false,ht]
        rw [hjp,suffix_cons _ _ hj]
      · have hcheck : (UniformWorkingPreparation.trialPrime p).value≠true :=
          (UniformWorkingPreparation.trialPrime_true p).not.mpr hpr
        have hc' : Nat.primeCounting' (p+1)=j+1 := by
          simp only [UniformWorkingPreparation.counting_succ,hpr,ite_false,hc,Nat.add_zero]
        have ht := ih (p+1) j (by omega) (by omega) hc' (by omega)
        simpa only [scan,hcheck,Bool.false_eq_true,ite_false] using ht

end
end ExactFourierCircuits.DFTModelWorkingHeaders
