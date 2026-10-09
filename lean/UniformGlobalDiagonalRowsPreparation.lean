import UniformGlobalDiagonalRowsLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
lemma boot_cursor {L:Layout} {lane:Fin 9} {s:State} (h:Header L lane s):
 Cursor L lane 0 0 (applyBlock boot s):=by
 constructor
 · constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.count,h.directory,h.lane,h.rows,h.permutation,h.coefficient]
 all_goals simp[boot,applyBlock,Op.apply,writeNat,next]
lemma boot_frame (s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega)[boot,applyBlock,Op.apply,writeNat,next]
/-- Fully initialized49 program produces every row/permutation/coefficient
bank from original physical radix/pool records and prepared pool values. -/
theorem execution (as:List Entry) (L:Layout) (lane:Fin 9) {n:ℕ} (x:Fin n→ℂ) (s:State)
 (length:as.length=L.ell) (total:amount as=L.total)
 (h:Header L lane s) (directory:Directory L.directory as 0 s) (pools:Pools as s)
 (bound:∀a∈as,a.pool+9*a.radix ≤ L.coefficient) (pc:s.pc=0) (wb:WordBound L.B s):
 ∃u,BoundedExecution program n x L.B s (9*L.total+35*L.ell+7) u ∧u.pc=48 ∧
 Produced L lane as 0 0 u ∧Frame s u ∧Outside L as 0 0 s u:=by
 have safe:readable boot s ∧peak boot s ≤ L.B:=by
  simp[boot,readable,peak,Op.readable,Op.peak]
  have:=L.code;omega
 have start:=block_runs boot program 0 n L.B x s boot_code pc wb
  (by have:=L.code;change 0+5 ≤ L.B;omega) safe.1 safe.2
 let b:=applyBlock boot s
 have bp:b.pc=5:=by rw[applyBlock_pc,pc];rfl
 have dir:Directory L.directory as 0 b:=Directory.transfer as 0 (by omega) directory (fun _ _=>rfl)
 have source:Pools as b:=Pools.transfer as pools bound (fun _ _=>rfl)
 obtain ⟨u,rest,up,produced,frame,out⟩:=loop as L lane x bound 0 0 b (by omega) (by omega)
  (boot_cursor h) dir source bp start.final_bound
 refine ⟨u,?_,up,produced,(boot_frame s).trans frame,⟨out.nat,out.scalar⟩⟩
 convert start.executes rest using 1
 change 9*L.total+35*L.ell+7=5+(9*amount as+35*as.length+2)
 rw[length,total]
 omega
lemma execution_saved {s u:State} (h:Frame s u):
 ∀q,100 ≤ q→q ≤ 106→u.natReg q=s.natReg q:=by
 intro q lo hi
 exact h.2.2 q (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
lemma axes_bounds (as:List Entry) (lane:Fin 9) (P C o:ℕ):
 ∀a∈axes lane P C o as,a.permutationBase+a.radix ≤ P+o+amount as ∧
  a.coefficientBase+a.radix ≤ C+o+amount as:=by
 induction as generalizing o with
 | nil=>simp[axes]
 | cons b as ih=>
   intro a ha
   simp only[axes,List.mem_cons] at ha
   rcases ha with equal|ha
   · subst a
     simp only[axis,amount,List.map_cons,List.sum_cons]
     constructor <;>omega
   · have next:=ih (o+b.radix) a ha
     simpa only[amount,List.map_cons,List.sum_cons,Nat.add_assoc] using next
lemma produced_banks {W:ℕ} (as:List Entry) (L:Layout) (lane:Fin 9)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (s:State)
 (sameRows:g.row=L.rows) (pBelow:L.permutation+L.total ≤ g.natStack)
 (cBelow:L.coefficient+L.total ≤ g.scalarStack) (total:amount as=L.total)
 (done:Produced L lane as 0 0 s):
 UniformGlobalTensorDiagonalMachine.Banks g (axes lane L.permutation L.coefficient 0 as) s:=by
 refine ⟨?_,done.2.1,done.2.2,?_,?_⟩
 · simpa only[sameRows] using done.1
 · intro a ha
   have bound:=(axes_bounds as lane L.permutation L.coefficient 0 a ha).1
   rw[Nat.add_zero,total] at bound
   omega
 · intro a ha
   have bound:=(axes_bounds as lane L.permutation L.coefficient 0 a ha).2
   rw[Nat.add_zero,total] at bound
   omega
end
end ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
