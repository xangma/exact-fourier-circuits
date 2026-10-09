import UniformGlobalDiagonalReturn
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDiagonalReturnCore
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalDiagonalChildPrefix (Context diagonalTicks phaseValues)
open UniformGlobalDiagonalReturn (programFor diagonal_code setup_code copy_code setup header_kept setup_safe setup_headers)
noncomputable section
/-- Only the five genuine diagonal inputs read by actual147. Packing,
sector headers and a desired tensor output are not entry premises. -/
structure Ready {W:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (s:State):Prop where
 diagonalHeader:UniformGlobalDiagonalRowsMachine.Header c.rows c.lane s
 directory:UniformGlobalDiagonalRowsMachine.Directory c.rows.directory c.entries 0 s
 pools:UniformGlobalDiagonalRowsMachine.Pools c.entries s
 tensorHeader:UniformGlobalTensorDiagonalMachine.Header c.tensor s
 source:UniformGlobalTensorDiagonalMachine.Source c.tensor v s
/-- Actual147 retains the ordinary cache prefixes while executing the
produced factor-pool diagonal and returning every real tagged role to source. -/
theorem execution {W n:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar)
 (x:Fin n→ℂ) (s:State) (ready:Ready c v s)
 (code:147 ≤ c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u,BoundedExecution (programFor W) n x c.metadata.B s
  (diagonalTicks c+7*(W*c.tensor.volume)+10) u ∧u.pc=146 ∧
 (∀r,r < W→∀j:Fin c.packing.volume,
  u.scalarHeap (c.tensor.source+r*c.tensor.volume+j.val)=some (phaseValues c v r j)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < c.rows.coefficient→q < c.tensor.scalarStack→q < c.tensor.source→q < c.tensor.destination→
  u.scalarHeap q=s.scalarHeap q) ∧
 (∀q,q < c.rows.rows → q < c.rows.permutation → q < c.tensor.natStack → u.natHeap q=s.natHeap q):=by
 have rowsBound:WordBound c.rows.B s:=by rw[c.sharedB];exact wb
 obtain ⟨t,diagonal,tp,values,saved,outputs,roots,nat,scalars⟩:=
  UniformGlobalTensorDiagonalPreparation.execution c.entries c.rows c.lane c.tensor v x s c.tensorB c.tensorRows
   c.entryLength c.tensorAxes c.entryTotal c.tensorVolume c.tensorPermutation c.tensorCoefficient c.tensorSource
   ready.diagonalHeader ready.directory ready.pools c.poolsBelow ready.tensorHeader ready.source
   (by rw[c.sharedB];omega) pc rowsBound
 have diagonal':BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x c.metadata.B s
  (diagonalTicks c) t:=by simpa only[c.sharedB,diagonalTicks] using diagonal
 have first:=UniformBoundedAssembly.boundedExecution_placed (diagonal_code W)
  (by rw[UniformGlobalTensorDiagonalPreparation.program_length];omega) (by omega) diagonal'
 rw[show placed 0 s=s by cases s;simp[placed]] at first
 let entry:=setPC t 131
 have hvol:entry.natReg 4501=c.tensor.volume:=
  (header_kept diagonal' 4501 (Or.inl rfl)).trans ready.tensorHeader.volume
 have hsrc:entry.natReg 4502=c.tensor.source:=
  (header_kept diagonal' 4502 (Or.inr (Or.inl rfl))).trans ready.tensorHeader.source
 have hdst:entry.natReg 4503=c.tensor.destination:=
  (header_kept diagonal' 4503 (Or.inr (Or.inr rfl))).trans ready.tensorHeader.destination
 have eb:WordBound c.metadata.B entry:=first.final_bound
 have safe:=setup_safe c.tensor entry hvol hsrc hdst
 have setRun:=block_runs (setup W) (programFor W) 131 n c.metadata.B x entry (setup_code W) rfl eb
  (by change 131+5 ≤ c.metadata.B;omega) safe.1 (by rw[←c.sharedB,←c.tensorB];exact safe.2)
 let copyEntry:=setPC (applyBlock (setup W) entry) 0
 have cb:=changePC_bound c.metadata.B (applyBlock (setup W) entry) 0 setRun.final_bound (by omega)
 have produced:UniformGlobalRolePackingMachine.Source c.packing (phaseValues c v) copyEntry:=
  UniformGlobalTensorPackingBridge.packing_source c.packing c.tensor c.entries c.lane c.rows.permutation c.rows.coefficient
   c.volume c.tensorVolume c.tensorOutput v copyEntry values
 have src:UniformScalarCopyMachine.Source (W*c.tensor.volume) c.tensor.destination copyEntry.scalarHeap:=by
  intro j hj
  have hj':j < W*c.packing.volume:=by rwa[c.volume]
  have positive:0 < c.packing.volume:=by
   by_contra h
   have hz:c.packing.volume=0:=by omega
   simp[hz] at hj'
  let r:=j/c.packing.volume
  let k:Fin c.packing.volume:=⟨j%c.packing.volume,Nat.mod_lt j positive⟩
  have rb:r < W:=(Nat.div_lt_iff_lt_mul positive).mpr hj'
  have eq:r*c.packing.volume+k.val=j:=by
   dsimp[r,k];simpa only[Nat.mul_comm] using Nat.div_add_mod j c.packing.volume
  refine ⟨phaseValues c v r k,?_⟩
  have p:=produced r rb k
  simpa only[c.tensorOutput,Nat.add_assoc,eq] using p
 have args:=setup_headers c.tensor entry hvol hsrc hdst
 have sourceBound:c.tensor.source+W*c.tensor.volume ≤ c.metadata.B:=by
  have:=c.tensor.sourceBelow;have:=c.tensor.scalarStackBound
  rw[c.tensorB,c.sharedB] at *;omega
 have disjoint:c.tensor.destination+W*c.tensor.volume ≤ c.tensor.source ∨
  c.tensor.source+W*c.tensor.volume ≤ c.tensor.destination:=by
  right;have:=c.tensor.sourceBelow;have:=c.tensor.destinationAbove;omega
 obtain ⟨z,copy,copied,_source,out,frame,_regs⟩:=UniformScalarCopyMachine.execution_disjoint n x
  (W*c.tensor.volume) c.tensor.destination c.tensor.source c.metadata.B copyEntry src
  (by rw[←c.sharedB,←c.tensorB];exact c.tensor.destinationBound) disjoint sourceBound (by omega) rfl
  args.1 args.2.1 args.2.2 cb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (copy_code W)
  (by rw[UniformScalarCopyMachine.program_length];omega) (by omega) copy
 have atCopy:placed 136 copyEntry=applyBlock (setup W) entry:=by
  have hp:(applyBlock (setup W) entry).pc=136:=by rw[applyBlock_pc];rfl
  exact UniformMultiAxisSectorMetadataPreparation.placed_zero _ _ hp
 rw[atCopy] at moved
 let u:=setPC z 146
 have stop:BoundedExecution (programFor W) n x c.metadata.B u 1 u:=.halt moved.final_bound
  (by simp[step,u,setPC,UniformGlobalDiagonalReturn.halt_at])
 refine ⟨u,?_,rfl,?_,frame.2.1.trans outputs,frame.2.2.1.trans roots,?_,?_⟩
 · convert first.executes (setRun.executes (moved.executes stop)) using 1
   change _=diagonalTicks c+(5+((7*(W*c.tensor.volume)+4)+1));omega
 · intro r hr j
   have bound:r*c.tensor.volume+j.val < W*c.tensor.volume:=by
    have bj:j.val < c.tensor.volume:=by rw[←c.volume];exact j.isLt
    nlinarith
   simpa only[u,setPC,Nat.add_assoc] using (copied _ bound).trans
    (by simpa only[c.tensorOutput,c.volume,Nat.add_assoc] using produced r hr j)
 · intro q hc hs ha hd
   exact (out q (Or.inl ha)).trans (scalars q (Or.inl hc) (Or.inl hs) (Or.inl hd))
 · intro q rows permutation stack
   exact (congrFun frame.1 q).trans (nat q (Or.inl rows) (Or.inl permutation) (Or.inl stack))

end
end ExactFourierCircuits.UniformDiagonalReturnCore
