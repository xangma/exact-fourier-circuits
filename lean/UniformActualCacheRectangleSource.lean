import UniformActualCacheRectangleRetention
import UniformCacheRangeSelectorData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCacheRectangleSource
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry UniformLocalCacheSlotConductorMachine
namespace S
abbrev Source:=UniformGlobalCalendarSelector.Source
end S
noncomputable section

def ListedSource (D stride:ℕ)(L:List (ℕ×ℕ))(heap:ℕ→Option ℕ):Prop:=
 ∀i (hi:i < L.length),heap (D+stride*i)=some (L[i]).1 ∧heap (D+stride*i+6)=some (L[i]).2
def records (L:List (ℕ×ℕ))(i:ℕ):ℕ×ℕ:=L[i]?.getD (0,0)
lemma listed_source {D stride L heap}(h:ListedSource D stride L heap):
 S.Source D stride L.length (records L) heap:=by
 intro i hi
 simpa [records,hi] using h i hi
lemma append_source {D stride xs ys heap}(left:ListedSource D stride xs heap)
 (right:ListedSource (D+stride*xs.length) stride ys heap):
 ListedSource D stride (xs++ys) heap:=by
 intro i hi
 by_cases low:i < xs.length
 · simpa only[List.getElem_append_left low] using left i low
 · have bound:i-xs.length < ys.length:=by simp only[List.length_append] at hi;omega
   have item:=right (i-xs.length) bound
   have address:D+stride*i=(D+stride*xs.length)+stride*(i-xs.length):=by
    rw[Nat.add_assoc,←Nat.mul_add]
    rw[show xs.length+(i-xs.length)=i by omega]
   rw[←address] at item
   have high:xs.length ≤ i:=by omega
   rw[List.getElem_append_right high]
   exact item

def block (n:ℕ)(q:Request):List (ℕ×ℕ):=
 List.ofFn (fun t:Fin (slotCount n q.row)=>(q.time+28*t.val,0))
def entries (n:ℕ)(qs:List Request):List (ℕ×ℕ):=qs.flatMap (block n)
lemma block_length (n:ℕ)(q:Request):(block n q).length=slotCount n q.row:=List.length_ofFn
lemma entries_length (n:ℕ)(qs:List Request):(entries n qs).length=slotPrefix n qs qs.length:=by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>
  simp only[entries,List.flatMap_cons,List.length_append,block_length,List.length_cons,slotPrefix]
  exact congrArg (slotCount n q.row+·) ih

lemma blocks_source (n stride:ℕ)(qs:List Request)(D:ℕ)(heap:ℕ→Option ℕ)
 (h:∀i (hi:i < qs.length),ListedSource (D+stride*slotPrefix n qs i) stride (block n qs[i]) heap):
 ListedSource D stride (entries n qs) heap:=by
 induction qs generalizing D with
 | nil=>intro i hi;simp only[entries,List.flatMap_nil,List.length_nil] at hi;omega
 | cons q qs ih=>
  have first:ListedSource D stride (block n q) heap:=by
   exact h 0 (by simp)
  have tail:ListedSource (D+stride*slotCount n q.row) stride (entries n qs) heap:=by
   apply ih
   intro i hi
   have current:=h (i+1) (by simp;omega)
   change ListedSource (D+stride*(slotCount n q.row+slotPrefix n qs i)) stride (block n qs[i]) heap at current
   simpa only[Nat.mul_add,Nat.add_assoc] using current
  change ListedSource D stride (block n q++entries n qs) heap
  exact append_source first (by simpa only[block_length] using tail)

lemma complete_cells {c n axisIndex qs R T}(g:UniformLocalRequestGeometry.Geometry c n axisIndex qs R T)
 {s:State}(all:∀i (hi:i < qs.length),Complete c n axisIndex qs R T g i hi s)
 (i:ℕ)(hi:i < qs.length)(t:ℕ)(ht:t < slotCount n qs[i].row):
 s.natHeap ((axis c n axisIndex).control+3*radix n axisIndex+4+
  (3*radix n axisIndex+11)*(slotPrefix n qs i+t))=some (qs[i].time+28*t) ∧
 s.natHeap ((axis c n axisIndex).control+3*radix n axisIndex+4+
  (3*radix n axisIndex+11)*(slotPrefix n qs i+t)+6)=some 0:=by
 obtain ⟨slot,witness,l,bl,contents⟩:=all i hi t ht
 have time:=contents.abi.1
 have kind:=contents.abi.2.2.2.2.2.2
 rw[controller,requestAt_eq qs i hi] at time kind
 change s.natHeap ((axis c n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
  3*radix n axisIndex+4+(3*radix n axisIndex+11)*t)=some (qs[i].time+28*t) at time
 change s.natHeap ((axis c n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
  3*radix n axisIndex+4+(3*radix n axisIndex+11)*t+6)=some 0 at kind
 have address:(axis c n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
  3*radix n axisIndex+4+(3*radix n axisIndex+11)*t=
  (axis c n axisIndex).control+3*radix n axisIndex+4+
  (3*radix n axisIndex+11)*(slotPrefix n qs i+t):=by ring
 rw[address] at time kind
 exact ⟨time,kind⟩

/-- Every timestamp and kind comes from the genuine produced Contents of the
actual finite rectangle loop. The flattened count is its measured slot prefix. -/
theorem rectangle_source {c n axisIndex qs R T}(g:UniformLocalRequestGeometry.Geometry c n axisIndex qs R T)
 {s:State}(all:∀i (hi:i < qs.length),Complete c n axisIndex qs R T g i hi s):
 S.Source ((axis c n axisIndex).control+3*radix n axisIndex+4) (3*radix n axisIndex+11)
  (slotPrefix n qs qs.length) (records (entries n qs)) s.natHeap:=by
 rw[←entries_length]
 apply listed_source
 apply blocks_source
 intro i hi t ht
 have bound:t < slotCount n qs[i].row:=by simpa only[block_length] using ht
 have h:=complete_cells g all i hi t bound
 simpa only[block,List.getElem_ofFn,Nat.mul_add,Nat.add_assoc] using h

lemma block_values {n:ℕ}{q:Request}{B:ℕ}(room:q.time+28*slotCount n q.row ≤ B)
 (v:ℕ×ℕ)(member:v∈block n q):v.1+28 ≤ B ∧v.2 ≤ B:=by
 obtain ⟨t,rfl⟩:=List.mem_ofFn.mp member
 have order:=Nat.mul_le_mul_left 28 (show t.val+1 ≤ slotCount n q.row by have:=t.isLt;omega)
 constructor
 · simp only[Nat.mul_add,Nat.mul_one] at order
   omega
 · exact Nat.zero_le _

lemma rectangle_values {c n axisIndex qs R T}(g:UniformLocalRequestGeometry.Geometry c n axisIndex qs R T):
 ∀i,i < slotPrefix n qs qs.length →
  (records (entries n qs) i).1+28 ≤ envelope c n ∧(records (entries n qs) i).2 ≤ envelope c n:=by
 intro k hk
 have length:k < (entries n qs).length:=by rw[entries_length];exact hk
 have mem:(entries n qs)[k]∈entries n qs:=List.getElem_mem length
 obtain ⟨q,hq,hblock⟩:=List.mem_flatMap.mp mem
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 subst q
 have room:=((g.slots i hi).endpoints (352*(controller c n axisIndex qs i).height.K+330) le_rfl).2.2.1
 change (controller c n axisIndex qs i).time+
  28*(352*(controller c n axisIndex qs i).height.K+330) ≤ envelope c n at room
 rw[controller_count c n axisIndex qs i hi] at room
 rw[controller,requestAt_eq qs i hi] at room
 have good:=block_values (B:=envelope c n) room _ hblock
 simpa [records,length] using good
end
end ExactFourierCircuits.UniformActualCacheRectangleSource
