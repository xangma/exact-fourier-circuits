import UniformAxisCacheInputs
import UniformLocalStoredRequestResult
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePhysical
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformAxisCacheSelectedPreparation

/-- Physical contents of one completed axis, excluding mutable controller
registers shared by subsequent axes. -/
structure Heaps (c:Constants)(n:ℕ)(j:Fin (ell n))(s u:State):Prop where
 nat:∀a,(axis c n j).tasks≤a→a<(axis c n j).endNat→u.natHeap a=s.natHeap a
 scalar:∀a,(axis c n j).pool≤a→a<(axis c n j).endScalar→u.scalarHeap a=s.scalarHeap a
lemma Heaps.refl (c:Constants)(n:ℕ)(j:Fin (ell n))(s:State):Heaps c n j s s:=
 ⟨by intros;rfl,by intros;rfl⟩
lemma Heaps.trans {c n j s u v}(h:Heaps c n j s u)(g:Heaps c n j u v):Heaps c n j s v:=
 ⟨fun a lo hi=>(g.nat a lo hi).trans (h.nat a lo hi),
  fun a lo hi=>(g.scalar a lo hi).trans (h.scalar a lo hi)⟩
lemma Heaps.of_eq {c n j s u}(nat:u.natHeap=s.natHeap)(scalar:u.scalarHeap=s.scalarHeap):
 Heaps c n j s u:=⟨fun a _ _=>congrFun nat a,fun a _ _=>congrFun scalar a⟩

lemma axis_lower (c:Constants)(n:ℕ)(j:Fin (ell n)):
 slab c n≤(axis c n j).tasks∧slab c n≤(axis c n j).pool:=by
 dsimp only [axis,axisBank,natStart,scalarStart]
 omega
lemma control_after_tasks (c:Constants)(n:ℕ)(j:Fin (ell n)):
 (axis c n j).tasks≤(axis c n j).control:=by
 dsimp only [axis,axisBank]
 omega

lemma preparation (c:Constants)(n:ℕ)(i j:Fin (ell n))(old:i.val<j.val)(s u:State)
 (nat:∀a,a<natAt c n j.val→u.natHeap a=s.natHeap a)
 (scalar:u.scalarHeap=s.scalarHeap):Heaps c n i s u:=by
 have before:=(axis_separation c n i j old).1
 change (axis c n i).endNat≤natAt c n j.val at before
 exact ⟨fun a _ hi=>nat a (by omega),fun a _ _=>congrFun scalar a⟩

lemma requests (c:Constants)(n:ℕ)(i j:Fin (ell n))(old:i.val<j.val)(s u:State)
 (frame:UniformLocalStoredRequestLoop.LoopFrame c n j s u):Heaps c n i s u:=by
 have sep:=axis_separation c n i j old
 have lower:=axis_lower c n i
 have control:=control_after_tasks c n j
 refine ⟨?_,?_⟩
 · intro a lo hi
   exact frame.nat a (by omega) (Or.inl (by omega))
 · intro a lo hi
   exact frame.scalar a (by omega) (Or.inl (by omega))

end ExactFourierCircuits.UniformAxisCachePhysical
