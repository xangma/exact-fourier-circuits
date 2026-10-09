import UniformGlobalDiagonalRowsPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTensorDiagonalPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (product)
noncomputable section
/-- Actual49 physical pool/axis row production followed by actual81 tensor
traversal. There is no generated tensor Banks or per-role callback premise. -/
def programFor (W:ℕ):Program:=UniformGlobalDiagonalRowsMachine.program.map (relocate 0 49)++
 (UniformGlobalTensorDiagonalMachine.programFor W).map (relocate 49 130)++[.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=131:=by
 simp only[programFor,List.length_append,List.length_map,UniformGlobalDiagonalRowsMachine.program_length,
  UniformGlobalTensorDiagonalMachine.program_length,List.length_singleton]
lemma rows_code (W:ℕ):CodeAt UniformGlobalDiagonalRowsMachine.program (programFor W) 0 49:=by
 exact UniformRankCrossPreparationMachine.segment_code []
  ((UniformGlobalTensorDiagonalMachine.programFor W).map (relocate 49 130)++[.halt]) _ 0 49 rfl
lemma tensor_code (W:ℕ):CodeAt (UniformGlobalTensorDiagonalMachine.programFor W) (programFor W) 49 130:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (UniformGlobalDiagonalRowsMachine.program.map (relocate 0 49)) [.halt] _ 49 130
  (by rw[List.length_map,UniformGlobalDiagonalRowsMachine.program_length])
lemma halt_at (W:ℕ):(programFor W)[130]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformGlobalDiagonalRowsMachine.program_length,UniformGlobalTensorDiagonalMachine.program_length];omega)]
 simp only[List.length_append,List.length_map,UniformGlobalDiagonalRowsMachine.program_length,
  UniformGlobalTensorDiagonalMachine.program_length];rfl

/-- One complete simultaneous diagonal phase from actual physical factor-pool
records. Both generated coefficient-bank writes and every tensor traversal
instruction are charged. The pool itself is an honest upstream producer. -/
theorem execution {W n:ℕ} (as:List UniformGlobalDiagonalRowsMachine.Entry)
 (L:UniformGlobalDiagonalRowsMachine.Layout) (lane:Fin 9)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (sameB:g.B=L.B) (sameRows:g.row=L.rows) (length:as.length=L.ell) (sameAxes:g.ell=L.ell)
 (total:UniformGlobalDiagonalRowsMachine.amount as=L.total)
 (volume:g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
 (pBelow:L.permutation+L.total ≤ g.natStack) (cBelow:L.coefficient+L.total ≤ g.scalarStack)
 (sourceSeparate:g.source+W*g.volume ≤ L.coefficient ∨ L.coefficient+L.total ≤ g.source)
 (rowHeader:UniformGlobalDiagonalRowsMachine.Header L lane s)
 (directory:UniformGlobalDiagonalRowsMachine.Directory L.directory as 0 s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools as s)
 (poolBound:∀a∈as,a.pool+9*a.radix ≤ L.coefficient)
 (tensorHeader:UniformGlobalTensorDiagonalMachine.Header g s)
 (source:UniformGlobalTensorDiagonalMachine.Source g v s)
 (code:131 ≤ L.B) (pc:s.pc=0) (wb:WordBound L.B s):
 ∃u,BoundedExecution (programFor W) n x L.B s
  (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u ∧u.pc=130 ∧
 UniformGlobalTensorDiagonalMachine.Filled g
  (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as) v W u ∧
 (∀q,100 ≤ q→q ≤ 106→u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,(q < L.rows ∨L.rows+3*L.ell ≤ q)→(q < L.permutation ∨L.permutation+L.total ≤ q)→
  (q < g.natStack ∨g.natStack+3*g.ell ≤ q)→u.natHeap q=s.natHeap q) ∧
 (∀q,(q < L.coefficient ∨L.coefficient+L.total ≤ q)→
  (q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination ∨g.destination+W*g.volume ≤ q)→u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨t,first,tp,produced,frame,out⟩:=UniformGlobalDiagonalRowsMachine.execution as L lane x s
  length total rowHeader directory pools poolBound pc wb
 have placedRows:=UniformBoundedAssembly.boundedExecution_placed (rows_code W)
  (by rw[UniformGlobalDiagonalRowsMachine.program_length];omega) (by omega) first
 rw[show placed 0 s=s by cases s;simp[placed]] at placedRows
 let ready:=setPC t 0
 have readyB:WordBound g.B ready:=by
  rw[sameB]
  exact changePC_bound L.B t 0 first.final_bound (by omega)
 have header:UniformGlobalTensorDiagonalMachine.Header g ready:=by
  constructor
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.volume
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.source
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.destination
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.axes
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.rows
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.natStack
  · exact (frame.2.2 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))).trans tensorHeader.scalarStack
 have alen:g.ell=(UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as).length:=by
  rw[UniformGlobalDiagonalRowsMachine.axes_length,length,sameAxes]
 have originalBanks:=UniformGlobalDiagonalRowsMachine.produced_banks as L lane g t sameRows pBelow cBelow total produced
 have banks:UniformGlobalTensorDiagonalMachine.Banks g
  (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as) ready:=
  originalBanks.transfer (i:=0) alen (fun _ _=>rfl) (fun _ _ _=>rfl)
 have input:UniformGlobalTensorDiagonalMachine.Source g v ready:=by
  intro i hi j hj
  have separated:g.source+i*g.volume+j < L.coefficient ∨
    L.coefficient+UniformGlobalDiagonalRowsMachine.amount as ≤ g.source+i*g.volume+j:=by
   rcases sourceSeparate with before|after
   · exact Or.inl (by nlinarith)
   · exact Or.inr (by rw[total];omega)
  exact (out.scalar _ separated).trans (source i hi j hj)
 have avol:g.volume=(radices (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as)).prod:=by
  rw[UniformGlobalDiagonalRowsMachine.axes_radices];exact volume
 obtain ⟨z,second,zp,filled,frame2,nat2,scalar2⟩:=UniformGlobalTensorDiagonalMachine.execution g
  (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as) v x ready alen avol header banks input rfl readyB
 have second':BoundedExecution (UniformGlobalTensorDiagonalMachine.programFor W) n x L.B ready
  (W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+6) z:=by
  simpa only[sameB,UniformGlobalDiagonalRowsMachine.axes_radices] using second
 have placedTensor:=UniformBoundedAssembly.boundedExecution_placed (tensor_code W)
  (by rw[UniformGlobalTensorDiagonalMachine.program_length];omega) (by omega) second'
 rw[show placed 49 ready=setPC t 49 by cases t;rfl] at placedTensor
 let u:=setPC z 130
 have stop:BoundedExecution (programFor W) n x L.B u 1 u:=.halt placedTensor.final_bound
  (by simp[step,u,setPC,halt_at])
 refine ⟨u,?_,rfl,filled,?_,frame2.1.trans frame.1,frame2.2.1.trans frame.2.1,?_,?_⟩
 · convert placedRows.executes (placedTensor.executes stop) using 1
   omega
 · intro q hlo hhi
   exact (frame2.2.2.2 q (by omega) (by omega) (Or.inl (by omega))).trans
    (UniformGlobalDiagonalRowsMachine.execution_saved frame q hlo hhi)
 · intro q hr hp hn
   have rows:q < L.rows+3*0 ∨L.rows+3*(0+as.length) ≤ q:=by simpa only[Nat.zero_add,Nat.mul_zero,Nat.add_zero,length] using hr
   have perm:q < L.permutation+0 ∨L.permutation+0+UniformGlobalDiagonalRowsMachine.amount as ≤ q:=by simpa only[Nat.add_zero,total] using hp
   exact (nat2 q hn).trans (out.nat q rows perm)
 · intro q hc hs hd
   have current:q < L.coefficient+0 ∨L.coefficient+0+UniformGlobalDiagonalRowsMachine.amount as ≤ q:=by
    simpa only[Nat.add_zero,total] using hc
   exact (scalar2 q hs hd).trans (out.scalar q current)
lemma axes_identity (as:List UniformGlobalDiagonalRowsMachine.Entry) (lane:Fin 9) (P C o:ℕ):
 ∀a∈UniformGlobalDiagonalRowsMachine.axes lane P C o as,∀j,a.permutation j=j:=by
 induction as generalizing o with
 | nil=>simp[UniformGlobalDiagonalRowsMachine.axes]
 | cons b as ih=>
   intro a ha j
   simp only[UniformGlobalDiagonalRowsMachine.axes,List.mem_cons] at ha
   rcases ha with equal|ha
   · subst a;rfl
   · exact ih (o+b.radix) a ha j
/-- Numeric specialization of the produced identity-permutation banks. -/
theorem diagonal_values {W:ℕ} {g:UniformGlobalTensorDiagonalMachine.Geometry W}
 {as:List UniformGlobalDiagonalRowsMachine.Entry} {lane:Fin 9} {P C:ℕ} {v:ℕ→ℕ→Scalar} {u:State}
 (done:UniformGlobalTensorDiagonalMachine.Filled g
  (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) v W u):
 ∀i,i<W→∀j:Fin (radices (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as)).prod,
 u.scalarHeap (g.destination+i*g.volume+j.val)=some
  (product (tensorCoefficient (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) j) (v i j.val)):=
 UniformGlobalTensorDiagonalMachine.diagonal_values (axes_identity as lane P C 0) done
end
end ExactFourierCircuits.UniformGlobalTensorDiagonalPreparation
