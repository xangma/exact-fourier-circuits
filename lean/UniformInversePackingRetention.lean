import UniformProducedInversePacking
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInversePackingRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
open UniformProducedInversePacking (Preparation programFor producer_code scatter_code halt_at)
noncomputable section
/-- Re-export the actual137 allocation frame through actual25. Every cache
cell outside the three computed Nat workspaces retains its exact value. -/
theorem execution {W n:ℕ} (p:Preparation W) (as:List PhysicalAxis)
 (length:as.length=p.layout.ell) (volume:UniformSectorPackingMachine.physicalVolume as=p.layout.total)
 (v:ℕ→Fin p.layout.total→Scalar) (x:Fin n→ℂ) (s:State)
 (header:UniformSectorPackingMachine.Header p.layout s)
 (rows:Rows as 0 p.layout.rows s) (widths:Widths as s) (permutations:Permutations as s)
 (widthsBelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ p.layout.suffix)
 (permutationsBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ p.layout.suffix)
 (scatterHeader:UniformGlobalRoleScatterMachine.Header p.scatter s)
 (source:UniformGlobalRoleScatterMachine.Source p.scatter v s) (nonempty:0<W)
 (pc:s.pc=0) (wb:WordBound p.layout.B s):
 ∃u ticks,BoundedExecution (programFor W) n x p.layout.B s ticks u ∧
 ticks ≤ 213*p.layout.total+W*(9*p.layout.total+12)+27 ∧u.pc=162 ∧
 (∀r,r<W→∀j:Fin p.layout.total,u.scalarHeap (p.destination+r*p.layout.total+j.val)=
  some (v r ((UniformSectorPackingMachine.physicalUnpacking as p.layout volume).symm j))) ∧
 UniformSectorPackingMachine.InverseReady p.layout (UniformSectorPackingMachine.physicalUnpacking as p.layout volume) u ∧
 (∀q,(q<p.layout.destination ∨p.layout.destination+p.layout.total ≤ q)→
  (q<p.destination ∨p.destination+W*p.layout.total ≤ q)→u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 UniformSectorPackingMachine.OutsideAllocation p.layout s u ∧
 (∀j,6000 ≤ j → u.natReg j=s.natReg j):=by
 have firstSource:UniformSectorPackingMachine.SourceReady p.layout (v 0) s:=by
  intro j;simpa only[Preparation.scatter,Nat.zero_mul,Nat.add_zero] using source 0 nonempty j
 obtain ⟨t,ticks,cost,run,_tp,inverse,_packed,out,nat,frame⟩:=UniformSectorPackingMachine.execution
  as p.layout n x (v 0) s length volume header rows widths permutations widthsBelow permutationsBelow firstSource pc wb
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed (producer_code W)
  (by rw[UniformSectorPackingMachine.program_length];have:=p.code;omega) (by have:=p.code;omega) run
 rw[show placed 0 s=s by cases s;simp[placed]] at placedFirst
 let entry:=setPC t 0
 have entryBound:=changePC_bound p.layout.B t 0 run.final_bound (by omega)
 have ready:UniformGlobalRoleScatterMachine.Header p.scatter entry:=by
  constructor
  · exact (frame.2.2.1 5960 (Or.inr (Or.inl (by omega)))).trans scatterHeader.volume
  · exact (frame.2.2.1 5961 (Or.inr (Or.inl (by omega)))).trans scatterHeader.source
  · exact (frame.2.2.1 5962 (Or.inr (Or.inl (by omega)))).trans scatterHeader.destination
  · exact (frame.2.2.1 5963 (Or.inr (Or.inl (by omega)))).trans scatterHeader.permutation
 have keptSource:UniformGlobalRoleScatterMachine.Source p.scatter v entry:=by
  intro r hr j
  have fit:=Nat.mul_le_mul_right p.layout.total (show r+1 ≤ W by omega)
  have before:p.layout.source+r*p.layout.total+j.val < p.layout.destination:=by
   have:=p.tempAfterAll;have bound:j.val < p.layout.total:=j.isLt;nlinarith
  exact (out _ (Or.inl before)).trans (source r hr j)
 have table:UniformGlobalNatPreparation.PermutationBank p.scatter.volume p.scatter.permutation entry.natHeap
  (UniformSectorPackingMachine.physicalUnpacking as p.layout volume):=inverse
 obtain ⟨z,second,zp,filled,lastFrame,lastOut⟩:=UniformGlobalRoleScatterMachine.execution p.scatter
  (UniformSectorPackingMachine.physicalUnpacking as p.layout volume) v x entry ready table keptSource rfl entryBound
 have second':BoundedExecution (UniformGlobalRoleScatterMachine.programFor W) n x p.layout.B entry
  (W*(9*p.layout.total+12)+6) z:=second
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed (scatter_code W)
  (by rw[UniformGlobalRoleScatterMachine.program_length];have:=p.code;omega) (by have:=p.code;omega) second'
 rw[show placed 137 entry=setPC t 137 by cases t;rfl] at placedSecond
 let u:=setPC z 162
 have stop:BoundedExecution (programFor W) n x p.layout.B u 1 u:=.halt placedSecond.final_bound
  (by simp[step,u,setPC,UniformProducedInversePacking.halt_at])
 refine ⟨u,ticks+(W*(9*p.layout.total+12)+6+1),?_,?_,rfl,?_,?_,?_,
  lastFrame.2.1.trans frame.1,lastFrame.2.2.1.trans frame.2.1,?_,?_⟩
 · convert placedFirst.executes (placedSecond.executes stop) using 1
 · omega
 · exact UniformGlobalRoleScatterMachine.native_values p.scatter _ v filled
 · intro j
   exact (congrFun lastFrame.1 (p.layout.inverse+j.val)).trans (inverse j)
 · intro q temp target
   exact (lastOut q target).trans (out q temp)
 · intro q suffix stack inverse
   exact (congrFun lastFrame.1 q).trans (nat q suffix stack inverse)
 · intro j high
   exact (lastFrame.2.2.2.1 j (by unfold UniformGlobalRoleScatterMachine.Protected;omega)).trans
    (frame.2.2.1 j (Or.inr (Or.inl (by omega))))
end
end ExactFourierCircuits.UniformInversePackingRetention
