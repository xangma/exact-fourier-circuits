import UniformGlobalAxisDispatchExecution
import UniformGlobalDiagonalRowsMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalProducedAxisBanks
open UniformMachine UniformSectorPackingMachine
noncomputable section

lemma rows_append (xs ys:List PhysicalAxis) (depth base:ℕ) (s:State):
 Rows (xs++ys) depth base s ↔Rows xs depth base s ∧Rows ys (depth+xs.length) base s:=by
 induction xs generalizing depth with
 | nil=>simp only[List.nil_append,Rows,List.length_nil,Nat.add_zero,true_and]
 | cons a xs ih=>
  simp only[List.cons_append,Rows,List.length_cons,ih]
  have address:depth+(xs.length+1)=(depth+1)+xs.length:=by omega
  rw[address]
  tauto

lemma rows_single_shift (a:PhysicalAxis) (depth base:ℕ) (s:State):
 Rows [a] 0 (base+4*depth) s ↔Rows [a] depth base s:=by
 simp only[Rows,Nat.mul_zero,Nat.add_zero]

lemma rows_ofFn {m:ℕ} (f:Fin m→PhysicalAxis) (depth base:ℕ) (s:State)
 (produced:∀i:Fin m,Rows [f i] 0 (base+4*(depth+i.val)) s):
 Rows (List.ofFn f) depth base s:=by
 induction m generalizing depth with
 | zero=>simp only[List.ofFn_zero,Rows]
 | succ m ih=>
  rw[List.ofFn_succ]
  have head:=produced 0
  simp only[Fin.val_zero,Nat.add_zero] at head
  have first:Rows [f 0] depth base s:=(rows_single_shift _ _ _ _).mp head
  have tail:Rows (List.ofFn (fun i:Fin m=>f i.succ)) (depth+1) base s:=by
   apply ih
   intro i
   have next:=produced i.succ
   have address:depth+i.succ.val=depth+1+i.val:=by simp only[Fin.val_succ];omega
   simpa only[address] using next
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,tail⟩

lemma widths_ofFn {m:ℕ} (f:Fin m→PhysicalAxis) (s:State)
 (produced:∀i:Fin m,Widths [f i] s):Widths (List.ofFn f) s:=by
 intro a member j
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 exact produced i _ (by simp only[List.mem_singleton]) j

lemma permutations_ofFn {m:ℕ} (f:Fin m→PhysicalAxis) (s:State)
 (produced:∀i:Fin m,Permutations [f i] s):Permutations (List.ofFn f) s:=by
 intro a member j
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 exact produced i _ (by simp only[List.mem_singleton]) j

lemma banks_ofFn {m W:ℕ} (g:UniformGlobalRolePackingMachine.Geometry W)
 (f:Fin m→PhysicalAxis) (s:State)
 (rows:∀i:Fin m,Rows [f i] 0 (g.rows+4*i.val) s)
 (widths:∀i:Fin m,Widths [f i] s)
 (permutations:∀i:Fin m,Permutations [f i] s):
 UniformGlobalRolePackingMachine.Banks g (List.ofFn f) s:=by
 refine ⟨rows_ofFn f 0 g.rows s ?_,widths_ofFn f s widths,permutations_ofFn f s permutations⟩
 intro i
 simpa only[Nat.zero_add] using rows i

lemma directory_ofFn {m:ℕ} (f:Fin m→UniformGlobalDiagonalRowsMachine.Entry)
 (D index:ℕ) (s:State)
 (produced:∀i:Fin m,s.natHeap (D+2*(index+i.val))=some (f i).radix ∧
  s.natHeap (D+2*(index+i.val)+1)=some (f i).pool):
 UniformGlobalDiagonalRowsMachine.Directory D (List.ofFn f) index s:=by
 induction m generalizing index with
 | zero=>simp only[List.ofFn_zero,UniformGlobalDiagonalRowsMachine.Directory]
 | succ m ih=>
  rw[List.ofFn_succ]
  refine ⟨?_,?_⟩
  · simpa only[Fin.val_zero,Nat.add_zero,UniformGlobalDiagonalRowsMachine.Cell] using produced 0
  · apply ih
    intro i
    have next:=produced i.succ
    have address:index+i.succ.val=index+1+i.val:=by simp only[Fin.val_succ];omega
    simpa only[address] using next

lemma pools_ofFn {m:ℕ} (f:Fin m→UniformGlobalDiagonalRowsMachine.Entry) (s:State)
 (produced:∀i:Fin m,∀lane:Fin 9,∀j:Fin (f i).radix,
  s.scalarHeap ((f i).pool+lane.val*(f i).radix+j.val)=some (UniformPairMachine.prepared ((f i).value lane j))):
 UniformGlobalDiagonalRowsMachine.Pools (List.ofFn f) s:=by
 intro a member lane j
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 exact produced i lane j
end
end ExactFourierCircuits.UniformGlobalProducedAxisBanks
