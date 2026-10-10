import DFTModelSectorMapFinal
import DFTModelSectorMapCarrySearch

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelSectorMapBits
noncomputable section

theorem Geometry.starts_ordered {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) :
 DFTModelSectorMapCarry.Ordered d := by
 intro i j h hj
 by_cases eq:i=j
 · subst j;exact le_refl _
 · have:=g.ordered i j (by omega) hj (by omega)
   dsimp [DFTModelSectorMapCarry.start];omega

theorem sparse_origin {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d) (j : ℕ)
 (hj:j < V) (nonzero:(run sparse (V,d)).val.look j 0 ≠ 0) :
 ∃i,i < d.len  ∧ 0 < (d.look i (0,0)).2  ∧ (d.look i (0,0)).1=j  ∧
 (run sparse (V,d)).val.look j 0=i+1 := by
 classical
 have hex:∃i,i < d.len  ∧ 0 < (d.look i (0,0)).2  ∧ (d.look i (0,0)).1=j := by
  by_contra absent
  have none:∀i,i < d.len → 0 < (d.look i (0,0)).2 → (d.look i (0,0)).1 ≠ j:=by
   intro i hi hp eq;exact absent ⟨i,hi,hp,eq⟩
  exact nonzero (sparse_none g j hj none)
 obtain ⟨i,hi,hp,eq⟩:=hex
 exact ⟨i,hi,hp,eq,eq ▸ sparse_at g i hi hp⟩

theorem cut_inside {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 (i j t c : ℕ) (hi:i < d.len) (start:(d.look i (0,0)).1 ≤ t) (tj:t ≤ j)
 (inside:j < (d.look i (0,0)).1+(d.look i (0,0)).2)
 (cut:DFTModelSectorMapCarry.Cut d t c) : c=i+1 := by
 obtain ⟨_,clen,left,right⟩:=cut
 have ilt:i < c:=by
  by_contra h
  have bad:=right i (by omega) hi
  dsimp [DFTModelSectorMapCarry.start] at bad;omega
 have cle:c ≤ i+1:=by
  by_contra h
  have ic:i+1 < d.len:=by omega
  have before:=g.ordered i (i+1) hi ic (by omega)
  have bad:=left (i+1) (by omega)
  dsimp [DFTModelSectorMapCarry.start] at bad;omega
 omega

theorem chosen_sector {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 (b j i : ℕ) (bp:0 < b) (hj:j < V) (hi:i < d.len)
 (start:(d.look i (0,0)).1 ≤ j)
 (inside:j < (d.look i (0,0)).1+(d.look i (0,0)).2)
 (pw ca : Tape ℕ) (powers:∀k,k ≤ b → pw.look k 0=2^k)
 (carry:∀c,c < V/b+1 → DFTModelSectorMapCarry.Cut d (c*b) (ca.look c 0)) :
 chosen b j (run sparse (V,d)).val
 (run pack (b,(V,(run sparse (V,d)).val))).val (run highTable b).val pw ca=i+1 := by
 have chunk:j/b < V/b+1:=by have:=Nat.div_le_div_right (c:=b) hj.le;omega
 have rem:j%b < b:=Nat.mod_lt _ bp
 have decomp:j%b+(j/b)*b=j:=by simpa only [Nat.mul_comm] using Nat.mod_add_div j b
 have positive:0 < (d.look i (0,0)).2:=by omega
 have marks:=produced_prefix_nearest b V (run sparse (V,d)).val (j/b) (j%b) chunk rem
 unfold chosen
 rw [powers (j%b+1) (by omega)]
 rcases marks with ⟨hz,none⟩|⟨k,hk,hz,nonzero,last⟩
 · rw [hz,ite_eq_left rfl]
   have earlier:(d.look i (0,0)).1 ≤ (j/b)*b:=by
    by_contra h
    have diff:(d.look i (0,0)).1-(j/b)*b < j%b+1:=by omega
    have marked:=none ((d.look i (0,0)).1-(j/b)*b) diff
    have eq:(j/b)*b+((d.look i (0,0)).1-(j/b)*b)=(d.look i (0,0)).1:=by omega
    rw [eq,sparse_at g i hi positive] at marked
    omega
   exact cut_inside g i j ((j/b)*b) (ca.look (j/b) 0) hi earlier (by omega)
    inside (carry _ chunk)
 · have atfit:(j/b)*b+k < V:=by omega
   obtain ⟨l,hl,pl,sl,ml⟩:=sparse_origin g ((j/b)*b+k) atfit nonzero
   have eq:l=i:=by
    by_contra ne
    rcases lt_or_gt_of_ne ne with less|greater
    · have before:=g.ordered l i hl hi less
      have diff:(d.look i (0,0)).1-(j/b)*b < j%b+1:=by omega
      have after:k < (d.look i (0,0)).1-(j/b)*b:=by omega
      have marked:=last _ after diff
      have eq:(j/b)*b+((d.look i (0,0)).1-(j/b)*b)=(d.look i (0,0)).1:=by omega
      rw [eq,sparse_at g i hi positive] at marked
      omega
    · have before:=g.ordered i l hi hl greater;omega
   have nz:((run highTable b).val.look
    ((run pack (b,(V,(run sparse (V,d)).val))).val.look (j/b) 0%2^(j%b+1)) 0) ≠ 0:=by
    rw [hz]
    exact Nat.succ_ne_zero k
   rw [ite_eq_right nz,hz]
   simp only [Nat.add_sub_cancel]
   exact eq ▸ ml

theorem mapped_sector (d : Tape (ℕ×ℕ)) (i j : ℕ)
 (start:(d.look i (0,0)).1 ≤ j)
 (inside:j < (d.look i (0,0)).1+(d.look i (0,0)).2) :
 mapped d j (i+1)=(i+1,((d.look i (0,0)).2,j-(d.look i (0,0)).1)) := by
 simp [mapped,Nat.not_lt.mpr start,inside]

theorem mapped_gap (d : Tape (ℕ×ℕ)) (j c : ℕ)
 (gap:∀i,i < d.len → ¬((d.look i (0,0)).1 ≤ j  ∧ j < (d.look i (0,0)).1+(d.look i (0,0)).2)) :
 mapped d j c=(0,(0,0)) := by
 by_cases hc:c=0
 · simp [mapped,hc]
 by_cases fit:c-1 < d.len
 · have hg:=gap (c-1) fit
   by_cases hs:j < (d.look (c-1) (0,0)).1
   · simp [mapped,hc,hs]
   · have he:¬j < (d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2:=by omega
     simp [mapped,hc,hs,he]
 · have empty:d.look (c-1) (0,0)=(0,0):=by simp [Tape.look,fit]
   simp [mapped,hc,empty]

end
end ExactFourierCircuits.DFTModelSectorMap
