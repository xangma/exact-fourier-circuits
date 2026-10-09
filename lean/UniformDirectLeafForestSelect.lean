import UniformDirectLeafForestLeafStep
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestSelect
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestModel
open UniformLocalCacheTreeMachine
noncomputable section

lemma leaf_branch {p:Parameters}{visits:List Visit}{i n B:ℕ}{q:Visit}
 (x:Fin n→ℂ)(s:State)(h:ReadCursor p visits i q s)(stop:leaf q)
 (code:461≤B)(pc:s.pc=37)(wb:WordBound B s):∃ticks,
 BoundedRuns UniformDirectLeafForestProgram.program n x B s ticks (setPC s 39) ∧ticks≤2:=by
 by_cases small:q.task.width<2
 · have nextBound:=changePC_bound B s 39 wb (by omega)
   refine ⟨1,.next wb ?_ (.refl nextBound),by omega⟩
   simp [UniformMachine.step,pc,UniformDirectLeafForestProgram.width_at,h.width,h.two,small,setPC]
 · have selected:UniformWorkspacePlanner.selected q.task.width=0:=by
    exact (show q.task.width<2∨UniformWorkspacePlanner.selected q.task.width=0 from stop).resolve_left small
   have bound:=changePC_bound B s 38 wb (by omega)
   have second:=changePC_bound B (setPC s 38) 39 bound (by omega)
   refine ⟨2,.next wb ?_ (.next bound ?_ (.refl second)),by omega⟩
   · simp [UniformMachine.step,pc,UniformDirectLeafForestProgram.width_at,h.width,h.two,small]
   · simp [UniformMachine.step,UniformDirectLeafForestProgram.selected_at,setPC,h.zero,h.selected,selected]

lemma split_branch {p:Parameters}{visits:List Visit}{i n B:ℕ}{q:Visit}
 (x:Fin n→ℂ)(s:State)(h:ReadCursor p visits i q s)(split:¬leaf q)
 (code:461≤B)(pc:s.pc=37)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 2 (setPC s 445):=by
 have small:¬q.task.width<2:=fun hq=>split (Or.inl hq)
 have selected:0<UniformWorkspacePlanner.selected q.task.width:=by
  by_contra hq;exact split (Or.inr (by omega))
 have bound:=changePC_bound B s 38 wb (by omega)
 have second:=changePC_bound B (setPC s 38) 445 bound (by omega)
 refine .next wb ?_ (.next bound ?_ (.refl second))
 · simp [UniformMachine.step,pc,UniformDirectLeafForestProgram.width_at,h.width,h.two,small]
 · simp [UniformMachine.step,UniformDirectLeafForestProgram.selected_at,setPC,h.zero,h.selected,selected]
end
end ExactFourierCircuits.UniformDirectLeafForestSelect
