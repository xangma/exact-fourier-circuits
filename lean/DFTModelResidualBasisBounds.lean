import DFTModelResidualBasisGeometry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBasisBounds
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore DFTModelResidualBasisImages
noncomputable section
attribute [local irreducible] power

 theorem exponent_lt (q w r p i : ℕ) (_hp:p < w+1) (hi:i < q*(w+1)+r) :
    exponentValue q (w+1) p i < q*(w+1)+r := by
  unfold exponentValue
  by_cases low:i < q
  · rw [ite_eq_left low]
    have h:=Nat.mul_lt_mul_of_pos_right low (by omega : 0 < w+1)
    omega
  · rw [ite_eq_right low]
    by_cases rep:i < q*(w+1)
    · rw [ite_eq_left rep]
      have diff:i-q < q*w := by
        have h: i < q*w+q:=by nlinarith
        omega
      have wp:0 < w := by
        by_contra no
        have wz:w=0:=by omega
        simp [wz] at diff
      have col:(i-q)/w < q := (Nat.div_lt_iff_lt_mul wp).2 (by simpa [Nat.mul_comm] using diff)
      have adj:=Nat.mod_lt (i-q) wp
      have row:(if (i-q)%w < p then (i-q)%w else (i-q)%w+1) < w+1 := by split_ifs <;> omega
      have mul:=Nat.mul_le_mul_right (w+1) (Nat.succ_le_iff.mpr col)
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at mul
      simp only [Nat.add_sub_cancel]
      omega
    · rw [ite_eq_right rep]
      exact hi

 theorem program_work (q w r a p : ℕ) (_hp:p < w+1) :
    (run program (q,(w+1,(r,(a,p))))).work ≤ (8*(q*(w+1)+r)+204)*(q*(w+1)+r)+18 := by
  change (run count (q,(w+1,(r,(a,p))))).work+
    (Bill.tab (run count (q,(w+1,(r,(a,p))))).val Ty.w.blank
      (fun i=>run cell ((q,(w+1,(r,(a,p)))),i))).work+1 ≤ _
  rw [count_run,ModelEquivalenceInterpreter.tab_work]
  dsimp only [Bill.val,Bill.work]
  have cells:(∑i∈Finset.range (q*(w+1)+r),(run cell ((q,(w+1,(r,(a,p)))),i)).work) ≤ (q*(w+1)+r)*(8*(q*(w+1)+r)+200) := by
    calc
      _ ≤ ∑_i∈Finset.range (q*(w+1)+r),(8*(q*(w+1)+r)+200) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (cell_work q (w+1) r a p i).trans (by have h:=exponent_lt q w r p i _hp (Finset.mem_range.mp hi);omega)
      _=_ := by simp
  nlinarith

 theorem exponent_peak (q m r a p i : ℕ) :
    (run exponent ((q,(m,(r,(a,p)))),i)).peak ≤ q*m+i*m+i+m+p+2 := by
  have di:=Nat.div_le_self (i-q) (m-1)
  have mo:=Nat.mod_le (i-q) (m-1)
  have sub:=Nat.sub_le i q
  have mul:=Nat.mul_le_mul_right m (di.trans sub)
  have iw:(i-q)%(m-1) ≤ i := mo.trans sub
  by_cases lo:i < q <;> by_cases hi:i < q*m <;> by_cases adj:(i-q)%(m-1) < p <;>
    simp only [exponent,selectedExponent,repExponent,omitted,adjacent,col,repIndex,repWidth,
      fromParams,columns,width,pivot,lowerCount,binary,run,Code.run,
      Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,lo,hi,adj,↓reduceIte,
      one_ne_zero,max_le_iff]
  all_goals repeat' apply And.intro
  all_goals omega

theorem mul_peak {s:Ty} (f g:Prog false s Ty.w) (x:s.T) :
    (run (binary .mul f g) x).peak=max (max (run f x).peak (run g x).peak)
      ((run f x).val*(run g x).val) := by
  simp [binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] exponent multiplier cell UniformBinaryXorCoordinates.encode

 theorem cell_peak (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
    (p:Fin (w+1)) (hp:v p=1) (i:Fin (q*(w+1)+r)) :
    (run cell ((q,(w+1,(r,((UniformBinaryXorCoordinates.encode v).val,p.val)))),i.val)).peak ≤ 2^(q*(w+1)+r)+(q*(w+1)+r)*(w+3)+(w+1)+p.val+2 := by
  let a:=(UniformBinaryXorCoordinates.encode v).val
  let k:=q*(w+1)+r
  have ex:=exponent_peak q (w+1) r a p.val i.val
  have e:=exponent_lt q w r p.val i.val p.isLt i.isLt
  have pow:2^(exponentValue q (w+1) p.val i.val) ≤ 2^k := Nat.pow_le_pow_right (by decide) e.le
  have pw:=power_peak (exponentValue q (w+1) p.val i.val)
  have value:=DFTModelResidualBasisGeometry.image_value q w r v p hp i
  have small:imageValue q (w+1) a p.val i.val < 2^k := by rw [value];exact Fin.isLt _
  have qm:q*(w+1) ≤ k:=by dsimp [k];omega
  have ib:i.val ≤ k:=i.isLt.le
  have im:=Nat.mul_le_mul_right (w+1) ib
  have compPeak:(run (.comp exponent power) ((q,(w+1,(r,(a,p.val)))),i.val)).peak ≤
      2^k+k*(w+3)+(w+1)+p.val+2 := by
    change max (max (run exponent ((q,(w+1,(r,(a,p.val)))),i.val)).peak
      (run power (run exponent ((q,(w+1,(r,(a,p.val)))),i.val)).val).peak) 0 ≤ _
    rw [exponent_value]
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals nlinarith
  have mp:(run multiplier ((q,(w+1,(r,(a,p.val)))),i.val)).peak ≤ 1 := by
    rw [multiplier_run]
  have pval:(run cell ((q,(w+1,(r,(a,p.val)))),i.val)).val=imageValue q (w+1) a p.val i.val :=
    cell_value q (w+1) r a p.val i.val
  unfold cell at pval
  change (run (.comp exponent power) ((q,(w+1,(r,(a,p.val)))),i.val)).val*
    (run multiplier ((q,(w+1,(r,(a,p.val)))),i.val)).val=imageValue q (w+1) a p.val i.val at pval
  rw [cell,mul_peak,pval]
  exact max_le (max_le compPeak (mp.trans (by have pos:=Nat.two_pow_pos k;nlinarith)))
    (small.le.trans (by nlinarith))

theorem program_peak (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
    (p:Fin (w+1)) (hp:v p=1) :
    (run program (q,(w+1,(r,((UniformBinaryXorCoordinates.encode v).val,p.val))))).peak ≤
      2^(q*(w+1)+r)+(q*(w+1)+r)*(w+3)+(w+1)+p.val+2 := by
  let a:=(UniformBinaryXorCoordinates.encode v).val
  let k:=q*(w+1)+r
  have cells:(Finset.range k).sup (fun i=>(run cell ((q,(w+1,(r,(a,p.val)))),i)).peak) ≤
      2^k+k*(w+3)+(w+1)+p.val+2 := by
    apply Finset.sup_le
    intro i hi
    exact cell_peak q w r v p hp ⟨i,Finset.mem_range.mp hi⟩
  change max (max (run count (q,(w+1,(r,(a,p.val))))).peak
    (Bill.tab (run count (q,(w+1,(r,(a,p.val))))).val Ty.w.blank
      (fun i=>run cell ((q,(w+1,(r,(a,p.val)))),i))).peak) 0 ≤ _
  rw [count_run,ModelEquivalenceInterpreter.tab_peak]
  dsimp only [Bill.peak,Bill.val]
  have pos:=Nat.two_pow_pos k
  have qk:q*(w+1)≤k:=by dsimp [k];omega
  have kb:k≤2^k := Nat.le_of_lt k.lt_two_pow_self
  dsimp only [k] at cells pos qk kb
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals nlinarith

end
end ExactFourierCircuits.DFTModelResidualBasisBounds
