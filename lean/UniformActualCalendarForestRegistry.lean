import UniformActualCalendarDirectProduced
import UniformDirectLeafForestRangeSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarForestRegistry
open UniformMachine UniformActualCalendarRegistry UniformDirectLeafForestContents
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestModel
open UniformLocalCacheTreeMachine UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource
open UniformDirectLeafCacheLoopBoot
noncomputable section
variable {visits:List Visit}

lemma is_leaf (i:Fin visits.length) (j:Fin (operations visits[i])):leaf visits[i]:=by
 by_contra neg
 have bound:=j.isLt
 simp only[operations,ite_eq_right neg] at bound
 omega


lemma record_bound {p:Parameters} {A:ℕ} (i:Fin visits.length) (j:Fin (operations visits[i])):
 j.val<(UniformDirectLeafForestLeafEnd.qs p A visits[i]).length:=by
 rw[UniformDirectLeafForestLeafEnd.count]
 have bound:=j.isLt
 have stop:=is_leaf i j
 change j.val<(if leaf visits[i] then size visits[i].task.width else 0) at bound
 rw[ite_eq_left stop] at bound
 exact bound

def block (p:Parameters) (visits:List Visit) (A:ℕ) (i:Fin visits.length):List (ℕ×ℕ):=
 List.ofFn (fun j:Fin (operations visits[i])=>
  UniformDirectLeafForestRangeSource.nodeRecords p visits A i.val i.isLt j.val)



lemma block_get {p:Parameters} {A:ℕ} (i:Fin visits.length)(j:Fin (block p visits A i).length):
 (block p visits A i).get j=UniformDirectLeafForestRangeSource.nodeRecords p visits A i.val i.isLt j.val:=by
 exact List.getElem_ofFn j.isLt

variable {p:Parameters} {A:ℕ} {positive:2≤p.radix} {s:State}
 (h:Contents p visits A positive s)

def data (i:Fin visits.length) (j:Fin (operations visits[i])):=
 Classical.choice (h.cached i.val i.isLt i.isLt (is_leaf i j) j.val (record_bound i j))

/-- All node entries are the actual semantic outputs retained by461. A
nonleaf has zero entries, as measured by the real durable range bank. -/
def family {O T B:ℕ} (facts:Facts p visits) (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*demand visits≤T) (radix:p.radix≤B)
 (i:Fin visits.length):
 Family p.radix O T B (position p visits i.val).entry (3*p.radix+11) (block p visits A i) s where
 entry:=fun j=>by
  have count:j.val<operations visits[i]:=by simpa only[block,List.length_ofFn] using j.isLt
  let index:Fin (operations visits[i]):=⟨j.val,count⟩
  let res:=data h i index
  have stop:=is_leaf i index
  have hj:=record_bound (p:=p) (A:=A) i index
  have good:=records_valid visits[i].task.width visits[i].task.offset (A+3*p.radix) 0 p.radix
   (facts.extent i.val i.isLt) _ (List.getElem_mem hj)
  have bounds:=UniformDirectLeafForestContents.slot_bounds entry i.isLt stop hj
  have permutation:(slot (UniformDirectLeafForestForward.config p visits i.val) p.radix
    (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j.val).permutation+p.radix≤T:=by
   have last:=bounds.2.2.2.trans nat
   change p.start.permutation+(3*p.radix+11)*before visits i.val+(3*p.radix+11)*j.val+p.radix≤T
   change p.start.entry+(3*p.radix+11)*before visits i.val+(3*p.radix+11)*j.val+7≤T at last
   omega
  have produced:=UniformActualCalendarDirectProduced.produced res good.2
   (bounds.2.2.2.trans nat) (bounds.2.1.trans pool) permutation radix
  apply Produced.cast produced rfl
  · rfl
  · rw[block_get]
    have actualBound:j.val<(UniformDirectLeafForestLeafEnd.qs p A visits[i.val]).length:=hj
    rw[UniformDirectLeafForestRangeSource.nodeRecords,dite_eq_left actualBound]
  · rw[block_get]
    have actualBound:j.val<(UniformDirectLeafForestLeafEnd.qs p A visits[i.val]).length:=hj
    rw[UniformDirectLeafForestRangeSource.nodeRecords,dite_eq_left actualBound]

end
end ExactFourierCircuits.UniformActualCalendarForestRegistry
