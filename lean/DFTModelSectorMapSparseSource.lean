import DFTModelSectorMapCore
import UniformSectorBatchDirectoryMachine
import UniformSectorTransposeCoordinates

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformSectorPacking
noncomputable section

def Encoded (xs : List BlockState) (d : Tape (ℕ×ℕ)) : Prop :=
 d.len=xs.length ∧ ∀i (hi:i<xs.length),d.look i (0,0)=((xs[i]'hi).start,(xs[i]'hi).width)

structure Geometry (V : ℕ) (d : Tape (ℕ×ℕ)) : Prop where
 fit : ∀i,i<d.len→(d.look i (0,0)).1+(d.look i (0,0)).2≤V
 ordered : ∀i j,i<d.len→j<d.len→i<j→
  (d.look i (0,0)).1+(d.look i (0,0)).2≤(d.look j (0,0)).1

theorem sow_length {α : Type} (n m : ℕ) (z : α) (f : ℕ→ℕ×α) :
 (Tape.sow n m z f).len=n := by
 induction m with
 | zero=>rfl
 | succ m ih=>exact ih

theorem sow_lookup_absent {α : Type} (n m j : ℕ) (z : α) (f : ℕ→ℕ×α)
 (hj:j<n) (none:∀ i, i < m → (f i).1≠j) :
 (Tape.sow n m z f).look j z=z := by
 induction m with
 | zero=>simp [Tape.sow,Tape.sow.iter,Tape.tab,Tape.look,hj]
 | succ m ih=>
  change ((Tape.sow n m z f).set (f m).1 (f m).2).look j z=z
  have neq:j≠(f m).1:=Ne.symm (none m (by omega))
  have old:=ih (fun i hi=>none i (by omega))
  simpa only [Tape.look,Tape.set,sow_length,hj,↓reduceDIte,neq,↓reduceIte] using old

theorem sow_lookup_unique {α : Type} (n m i j : ℕ) (z : α) (f : ℕ→ℕ×α)
 (hi : i < m) (hj : j < n) (hit : (f i).1 = j)
 (unique : ∀ k, k < m → k ≠ i → (f k).1 ≠ j) :
 (Tape.sow n m z f).look j z=(f i).2 := by
 induction m with
 | zero=>omega
 | succ m ih=>
  change ((Tape.sow n m z f).set (f m).1 (f m).2).look j z=_
  by_cases last:i=m
  · subst i
    simp only [Tape.look,Tape.set,sow_length,hj,↓reduceDIte,hit,↓reduceIte]
  · have neq:j≠(f m).1:=Ne.symm (unique m (by omega) (Ne.symm last))
    have old:=ih (by omega) (fun k hk hki=>unique k (by omega) hki)
    simpa only [Tape.look,Tape.set,sow_length,hj,↓reduceDIte,neq,↓reduceIte] using old

theorem Geometry.distinct {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 {i j : ℕ} (hi:i<d.len) (hj:j<d.len) (ne:i≠j)
 (pi:0<(d.look i (0,0)).2) (pj:0<(d.look j (0,0)).2) :
 (d.look i (0,0)).1≠(d.look j (0,0)).1 := by
 rcases lt_or_gt_of_ne ne with h|h
 · have:=g.ordered i j hi hj h;omega
 · have:=g.ordered j i hj hi h;omega

theorem sparse_length (V : ℕ) (d : Tape (ℕ×ℕ)) : (run sparse (V,d)).val.len=V := by
 rw [sparse_value];exact sow_length _ _ _ _

theorem sparse_at {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 (i : ℕ) (hi:i<d.len) (positive:0<(d.look i (0,0)).2) :
 (run sparse (V,d)).val.look (d.look i (0,0)).1 0=i+1 := by
 have fit:=g.fit i hi
 have inside:(d.look i (0,0)).1<V:=by omega
 have ne:(d.look i (0,0)).2≠0:=by omega
 rw [sparse_value]
 apply sow_lookup_unique V d.len i _ 0 (stamp V d) hi inside
 · simp [stamp,ne]
 · intro j hj hji
   by_cases empty:(d.look j (0,0)).2=0
   · simp only [stamp,empty,↓reduceIte]
     omega
   · have pos:0<(d.look j (0,0)).2:=by omega
     simpa only [stamp,empty,↓reduceIte] using g.distinct hj hi hji pos positive

theorem sparse_none {V : ℕ} {d : Tape (ℕ×ℕ)} (_g : Geometry V d)
 (j : ℕ) (hj:j<V)
 (none:∀i,i<d.len→0<(d.look i (0,0)).2→(d.look i (0,0)).1≠j) :
 (run sparse (V,d)).val.look j 0=0 := by
 rw [sparse_value]
 apply sow_lookup_absent _ _ _ _ _ hj
 intro i hi
 by_cases empty:(d.look i (0,0)).2=0
 · simp only [stamp,empty,↓reduceIte];omega
 · simpa only [stamp,empty,↓reduceIte] using none i hi (by omega)

/-- Semantic extraction only: this is not an uncharged typed heap-read primitive. -/
def nativeReadback (E M : ℕ) (s : UniformMachine.State) : Tape (ℕ×ℕ) :=
 Tape.tab M (fun i=>((s.natHeap (E+5*i+3)).getD 0,(s.natHeap (E+5*i+1)).getD 0))

theorem native_encoded {W E A : ℕ} (xs : List BlockState) (s : UniformMachine.State)
 (table:∀i (hi:i<xs.length),UniformSectorBatchDirectoryMachine.BatchCell W E A i (xs[i]'hi) s) :
 Encoded xs (nativeReadback E xs.length s) := by
 refine ⟨rfl,?_⟩
 intro i hi
 have h:=table i hi
 simp only [nativeReadback,Tape.look,Tape.tab,hi,↓reduceDIte,
  UniformSectorBatchDirectoryMachine.BatchCell] at h ⊢
 rw [h.2.2.2.1,h.2.1]
 rfl

theorem canonical_geometry (axes : List Axis) (d : Tape (ℕ×ℕ))
 (encoded:Encoded (sectorStates axes) d) : Geometry (radices axes).prod d := by
 constructor
 · intro i hi
   have hs:i<(sectorStates axes).length:=by rw [←encoded.1]; exact hi
   rw [encoded.2 i hs]
   exact UniformSectorBatchDirectoryMachine.sector_fits axes i hs
 · intro i j hi hj less
   have is:i<(sectorStates axes).length:=by rw [←encoded.1]; exact hi
   have js:j<(sectorStates axes).length:=by rw [←encoded.1]; exact hj
   rw [encoded.2 i is,encoded.2 j js]
   exact UniformSectorBatchDirectoryMachine.sector_before axes i j is js less

theorem canonical_positive (axes : List Axis) (d : Tape (ℕ×ℕ))
 (encoded:Encoded (sectorStates axes) d) (i : ℕ) (hi:i<d.len) :
 0<(d.look i (0,0)).2 := by
 have hs:i<(sectorStates axes).length:=by rw [←encoded.1]; exact hi
 rw [encoded.2 i hs]
 dsimp only [Prod.snd]
 rw [UniformSectorBatchDirectoryMachine.sector_width axes i hs]
 exact Nat.two_pow_pos _

theorem positive_length_sum (xs : List BlockState)
 (positive:∀st∈xs,0<st.width) : xs.length≤(xs.map BlockState.width).sum := by
 induction xs with
 | nil=>simp
 | cons st xs ih=>
   have p:=positive st (by simp)
   have rest:=ih (fun z hz=>positive z (by simp [hz]))
   simp only [List.length_cons,List.map_cons,List.sum_cons]
   omega

theorem canonical_count (axes : List Axis) (d : Tape (ℕ×ℕ))
 (encoded:Encoded (sectorStates axes) d) : d.len≤(radices axes).prod := by
 rw [encoded.1,←UniformSectorBatchDirectoryMachine.sector_width_sum axes]
 apply positive_length_sum
 intro st hst
 obtain ⟨i,hi,equal⟩:=List.mem_iff_getElem.mp hst
 rw [←equal,UniformSectorBatchDirectoryMachine.sector_width axes i hi]
 exact Nat.two_pow_pos _

end
end ExactFourierCircuits.DFTModelSectorMap
