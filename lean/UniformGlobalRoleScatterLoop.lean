import UniformGlobalRoleScatterMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalRoleScatterMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalNatPreparation (PermutationBank)
noncomputable section

lemma source_transfer {W:ℕ} (g:Geometry W) {v:ℕ→Fin g.volume→Scalar} (i:Fin W) {s u:State}
 (src:Source g v s)
 (out:∀q,(q < g.destination+i.val*g.volume ∨ g.destination+(i.val+1)*g.volume  ≤  q)→u.scalarHeap q=s.scalarHeap q):
 Source g v u:=by
 intro r hr j
 have disjoint:g.source+r*g.volume+j.val < g.destination+i.val*g.volume ∨
  g.destination+(i.val+1)*g.volume  ≤  g.source+r*g.volume+j.val:=by
  have rFit:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
  have iFit:=Nat.mul_le_mul_right g.volume (Nat.succ_le_of_lt i.isLt)
  rcases g.disjoint with h|h
  · left;have:=j.isLt;nlinarith
  · right;have:=j.isLt;nlinarith
 exact (out _ disjoint).trans (src r hr j)
lemma filled_transfer {W:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ→Fin g.volume→Scalar)
 (i:Fin W) {s u:State} (old:Filled g p v i.val s)
 (fresh:∀j:Fin g.volume,u.scalarHeap (g.destination+i.val*g.volume+(p j).val)=some (v i.val j))
 (out:∀q,(q < g.destination+i.val*g.volume ∨g.destination+(i.val+1)*g.volume  ≤  q)→u.scalarHeap q=s.scalarHeap q):
 Filled g p v (i.val+1) u:=by
 intro r hr j
 by_cases same:r=i.val
 · subst r;exact fresh j
 · have before:r < i.val:=by omega
   have fit:=Nat.mul_le_mul_right g.volume (show r+1 ≤ i.val by omega)
   exact (out _ (Or.inl (by have:=(p j).isLt;nlinarith))).trans (old r before j)
lemma outside_local {W:ℕ} (g:Geometry W) (i:Fin W) {s u:State}
 (out:∀q,(q < g.destination+i.val*g.volume ∨g.destination+(i.val+1)*g.volume  ≤  q)→u.scalarHeap q=s.scalarHeap q):
 Outside g s u:=by
 intro q h
 apply out q
 rcases h with h|h
 · left;omega
 · right;have fit:=Nat.mul_le_mul_right g.volume (Nat.succ_le_of_lt i.isLt);nlinarith

theorem loop {W n:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ→Fin g.volume→Scalar)
 (x:Fin n→ℂ) (remaining:ℕ):
 ∀i s,i ≤ W→W-i=remaining→s.pc=4→WordBound g.B s→Cursor g i s→
  PermutationBank g.volume g.permutation s.natHeap p→Source g v s→Filled g p v i s→
 ∃u,BoundedExecution (programFor W) n x g.B s (remaining*(9*g.volume+12)+2) u ∧u.pc=24 ∧
  Filled g p v W u ∧Frame s u ∧Outside g s u:=by
 induction remaining with
 |zero=>
  intro i s le count pc wb cursor table source filled
  have equal:i=W:=by omega
  let u:=setPC s 24
  have ub:=changePC_bound g.B s 24 wb (by have:=g.code;omega)
  have first:BoundedRuns (programFor W) n x g.B s 1 u:=.next wb
   (by simp[step,pc,branch_at,cursor.index,cursor.roles,equal,u,setPC]) (.refl ub)
  have stop:BoundedExecution (programFor W) n x g.B u 1 u:=.halt ub (by simp[step,u,setPC,halt_at])
  refine ⟨u,by simpa using first.executes stop,rfl,?_,Frame.refl s,fun _ _=>rfl⟩
  intro r hr j;exact filled r (by omega) j
 |succ remaining ih=>
  intro i s le count pc wb cursor table source filled
  have lt:i < W:=by omega
  let role:Fin W:=⟨i,lt⟩
  obtain ⟨t,first,tp,next,fresh,frame,out⟩:=iteration g p v x s role cursor table source pc wb
  have keptTable:PermutationBank g.volume g.permutation t.natHeap p:=by rw[frame.1];exact table
  have keptSource:=source_transfer g role source out
  have nextFilled:=filled_transfer g p v role filled fresh out
  obtain ⟨u,last,up,done,lastFrame,lastOut⟩:=ih (i+1) t (by omega) (by omega) tp first.final_bound next
   keptTable keptSource nextFilled
  refine ⟨u,?_,up,done,frame.trans lastFrame,?_⟩
  · convert first.executes last using 1;ring
  · intro q h;exact (lastOut q h).trans (outside_local g role out q h)

lemma boot_cursor {W:ℕ} {g:Geometry W} {s:State} (h:Header g s):Cursor g 0 (applyBlock (boot W) s):=by
 constructor
 · constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,h.permutation]
 all_goals simp[boot,applyBlock,Op.apply,writeNat,next]

/-- AllW roles execute actual12 at one fixed site. The shared permutation
bank can be the genuine137-produced inverse-address bank. Both disjoint
scalar-bank orientations are allowed, and the entire Nat heap is retained. -/
theorem execution {W n:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ→Fin g.volume→Scalar)
 (x:Fin n→ℂ) (s:State) (header:Header g s)
 (table:PermutationBank g.volume g.permutation s.natHeap p) (source:Source g v s)
 (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W) n x g.B s (W*(9*g.volume+12)+6) u ∧u.pc=24 ∧
 Filled g p v W u ∧Frame s u ∧Outside g s u:=by
 have safe:readable (boot W) s ∧peak (boot W) s ≤ g.B:=by
  simp[boot,readable,peak,Op.readable,Op.peak]
  have:=g.code;have:=g.roles;omega
 have first:=block_runs (boot W) (programFor W) 0 n g.B x s (boot_code W) pc wb
  (by rw[boot_length];have:=g.code;omega) safe.1 safe.2
 let b:=applyBlock (boot W) s
 have bp:b.pc=4:=by rw[applyBlock_pc,boot_length,pc]
 obtain ⟨u,rest,up,filled,frame,out⟩:=loop g p v x W 0 b (by omega) (by omega) bp first.final_bound
  (boot_cursor header) table source (by intro i hi;omega)
 refine ⟨u,?_,up,filled,(boot_frame W s).trans frame,out⟩
 convert first.executes rest using 1;rw[boot_length];omega

theorem native_values {W:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ→Fin g.volume→Scalar)
 {s:State} (filled:Filled g p v W s):
 ∀r,r<W→∀j:Fin g.volume,s.scalarHeap (g.destination+r*g.volume+j.val)=some (v r (p.symm j)):=by
 intro r hr j
 simpa only[Equiv.apply_symm_apply] using filled r hr (p.symm j)
end
end ExactFourierCircuits.UniformGlobalRoleScatterMachine
