import UniformGlobalDiagonalRowsMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section
/-- Actual placed29 call. Args are installed by setup from physical directory
reads in the enclosing iteration, not a ready-output/action premise. -/
lemma placed_row {n i o:ℕ} (L:Layout) (lane:Fin 9) (a:Entry) (x:Fin n→ℂ) (s:State)
 (hi:i < L.ell) (off:o+a.radix ≤ L.total) (pool:a.pool+9*a.radix ≤ L.coefficient)
 (h:Cursor L lane i o s)
 (args:UniformGlobalDiagonalPhasePreparation.Args a.radix a.pool (L.permutation+o)
  (L.coefficient+o) L.rows i lane s)
 (source:UniformTensorDiagonalBankMachine.Coefficients a.radix (a.pool+lane.val*a.radix) (a.value lane) s)
 (pc:s.pc=16) (wb:WordBound L.B s):
 ∃u,BoundedRuns program n x L.B s (9*a.radix+21) u ∧u.pc=45 ∧
 Cursor L lane i o u ∧u.natReg 4380=a.radix ∧Frame s u ∧RowData L lane a i o s u:=by
 let ready:=setPC s 0
 have readyB:=changePC_bound L.B s 0 wb (by have:=L.code;omega)
 have args':UniformGlobalDiagonalPhasePreparation.Args a.radix a.pool (L.permutation+o)
  (L.coefficient+o) L.rows i lane ready:=
  ⟨args.radix,args.pool,args.lane,args.permutation,args.coefficient,args.row,args.depth⟩
 have sep:a.pool+lane.val*a.radix+a.radix ≤ L.coefficient+o:=by
  have lv:lane.val+1 ≤ 9:=by have:=lane.isLt;omega
  have mult:=Nat.mul_le_mul_right a.radix lv
  nlinarith
 obtain ⟨t,run,result⟩:=UniformGlobalDiagonalPhasePreparation.execution (a.value lane) args' source (Or.inl sep)
  (Or.inl (by have:=L.rowsBelow;omega)) (by have:=L.coefficientBound;omega)
  (by have:=L.rowsBelow;have:=L.permutationBound;omega) (by have:=L.permutationBound;omega)
  (by have:=L.coefficientBound;omega) (by have:=L.code;omega) x rfl readyB
 have moved:=UniformBoundedAssembly.boundedExecution_placed row_code
  (by rw[UniformGlobalDiagonalPhasePreparation.program_length];have:=L.code;omega) (by have:=L.code;omega) run
 rw[UniformMultiAxisSectorMetadataPreparation.placed_zero s 16 pc] at moved
 let u:=setPC t 45
 have cur:=row_cursor (h.withPC (pc:=0)) run
 have radius:t.natReg 4380=a.radix:=(row_nat run (by omega) (by omega)).trans args'.radix
 refine ⟨u,moved,rfl,cur.withPC,radius,?_,?_⟩
 · refine ⟨result.outputs,result.roots,?_⟩
   intro q h0 h1 h2
   exact (row_nat run h0 (by omega)).trans (show ready.natReg q=s.natReg q from rfl)
 · exact ⟨result.permutation,result.coefficient,result.rowWidth,result.rowPermutation,
    result.rowCoefficient,result.natFrame,result.scalarFrame⟩

lemma tick_row {n i o:ℕ} (L:Layout) (lane:Fin 9) (a:Entry) (x:Fin n→ℂ) (s:State)
 (hi:i < L.ell) (off:o+a.radix ≤ L.total) (h:Cursor L lane i o s)
 (radius:s.natReg 4380=a.radix) (pc:s.pc=45) (wb:WordBound L.B s):
 ∃u,BoundedRuns program n x L.B s 3 u ∧u.pc=5 ∧
 Cursor L lane (i+1) (o+a.radix) u ∧Frame s u ∧u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap:=by
 have safe:readable finish s ∧peak finish s ≤ L.B:=by
  simp[finish,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.offset,h.index,h.one,radius]
  have:=L.coefficientBound;have:=L.code;have:=L.rowsBelow;have:=L.permutationBound;omega
 have setting:=block_runs finish program 45 n L.B x s finish_code pc wb
  (by have:=L.code;change 45+2 ≤ L.B;omega) safe.1 safe.2
 let done:=applyBlock finish s
 let u:=setPC done 5
 have dp:done.pc=47:=by rw[applyBlock_pc,pc];rfl
 have jump:BoundedRuns program n x L.B done 1 u:=.next setting.final_bound
  (by simp[step,dp,jump_at,u,setPC]) (.refl (changePC_bound L.B done 5 setting.final_bound (by have:=L.code;omega)))
 refine ⟨u,by simpa [finish] using setting.trans jump,rfl,(finish_cursor h radius).withPC (pc:=5),finish_frame s,rfl,rfl⟩
lemma load_row {n i o:ℕ} (L:Layout) (lane:Fin 9) (a:Entry) (x:Fin n→ℂ) (s:State)
 (hi:i < L.ell) (off:o+a.radix ≤ L.total) (pool:a.pool+9*a.radix ≤ L.coefficient)
 (h:Cursor L lane i o s) (cell:Cell L.directory i a s) (pc:s.pc=5) (wb:WordBound L.B s):
 ∃u,BoundedRuns program n x L.B s 11 u ∧u.pc=16 ∧Cursor L lane i o u ∧
 UniformGlobalDiagonalPhasePreparation.Args a.radix a.pool (L.permutation+o)
  (L.coefficient+o) L.rows i lane u ∧Frame s u ∧u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap:=by
 let entered:=setPC s 6
 have eb:=changePC_bound L.B s 6 wb (by have:=L.code;omega)
 have branch:BoundedRuns program n x L.B s 1 entered:=.next wb
  (by simp[step,pc,branch_at,h.index,h.count,hi,entered,setPC]) (.refl eb)
 have eh:Cursor L lane i o entered:=h.withPC (pc:=6)
 have safe:=setup_safe eh cell hi off pool
 have setting:=block_runs setup program 6 n L.B x entered setup_code rfl eb
  (by have:=L.code;change 6+10 ≤ L.B;omega) safe.1 safe.2
 let u:=applyBlock setup entered
 have up:u.pc=16:=by rw[applyBlock_pc];rfl
 exact ⟨u,by simpa only[show setup.length=10 from rfl] using branch.trans setting,up,setup_cursor eh,
  setup_header eh cell,setup_frame entered,(setup_heaps entered).1,(setup_heaps entered).2⟩

/-- Complete literal49 row visit from its actual physical directory and pool
read, through the real29 helper and charged cursor advance. -/
lemma iteration {n i o:ℕ} (L:Layout) (lane:Fin 9) (a:Entry) (x:Fin n→ℂ) (s:State)
 (hi:i < L.ell) (off:o+a.radix ≤ L.total) (pool:a.pool+9*a.radix ≤ L.coefficient)
 (h:Cursor L lane i o s) (cell:Cell L.directory i a s)
 (source:∀j:Fin a.radix,s.scalarHeap (a.pool+lane.val*a.radix+j.val)=some (prepared (a.value lane j)))
 (pc:s.pc=5) (wb:WordBound L.B s):
 ∃u,BoundedRuns program n x L.B s (9*a.radix+35) u ∧u.pc=5 ∧
 Cursor L lane (i+1) (o+a.radix) u ∧Frame s u ∧RowData L lane a i o s u:=by
 obtain ⟨t,first,tp,tc,args,frame1,nat1,scalar1⟩:=load_row L lane a x s hi off pool h cell pc wb
 have coef:UniformTensorDiagonalBankMachine.Coefficients a.radix (a.pool+lane.val*a.radix) (a.value lane) t:=by
  intro j
  exact (congrFun scalar1 _).trans (by simpa only[Nat.add_assoc] using source j)
 obtain ⟨v,second,vp,vc,radius,frame2,data⟩:=placed_row L lane a x t hi off pool tc args coef tp first.final_bound
 obtain ⟨u,last,up,uc,frame3,nat3,scalar3⟩:=tick_row L lane a x v hi off vc radius vp second.final_bound
 refine ⟨u,?_,up,uc,frame1.trans (frame2.trans frame3),?_⟩
 · convert first.trans (second.trans last) using 1
   omega
 · rcases data with ⟨perm,coeff,r0,r1,r2,nf,sf⟩
   refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
   · intro j;exact (congrFun nat3 _).trans (perm j)
   · intro j;exact (congrFun scalar3 _).trans (coeff j)
   · exact (congrFun nat3 _).trans r0
   · exact (congrFun nat3 _).trans r1
   · exact (congrFun nat3 _).trans r2
   · intro q hq hp;exact (congrFun nat3 q).trans ((nf q hq hp).trans (congrFun nat1 q))
   · intro q hq;exact (congrFun scalar3 q).trans ((sf q hq).trans (congrFun scalar1 q))
end
end ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
