import UniformResidualFiberTraversal
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualFiberTraversal
open UniformMachine UniformResidualFiberAddressMachine
open UniformNatBlockMachine (Op applyBlock readable peak block_runs)
noncomputable section
theorem execution_headers (n B k q w images stack output table : ℕ) (image : ℕ→ℕ)
 (x : Fin n→ℂ) (s : State) (pc : s.pc=0)
 (input : Inputs k q w images stack output table s) (bound : WordBound B s)
 (code : 71 ≤ B) (imagesBefore : images+k ≤ stack)
 (stackBefore : stack+2*k ≤ output) (outputBefore : output+2^k ≤ table)
 (tableBound : table+2^q*2^q ≤ B) (volume : 2^(q*w) ≤ B)
 (bank : ∀i, i<k → s.natHeap (images+i)=some (image i))
 (imageSmall : ∀i, i<k → image i<2^(q*w))
 (entries : UniformXorTableMachine.Entries q table (2^q*2^q) s) : ∃u,
 BoundedExecution program n x B s (treeCost w k+9) u ∧ u.pc=70 ∧
 u.natReg 4023=2^k ∧ (∀j, j<2^k → u.natHeap (output+j)=some (address image k 0 j)) ∧
 (∀z, (z<stack ∨ stack+2*k≤z) → (z<output ∨ output+2^k≤z) → u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ Header k q w images stack output table u := by
 have safe : readable boot s ∧ peak boot s≤B := by
  simp [boot,readable,peak,Op.readable,Op.peak];omega
 have br:=block_runs boot program 0 n B x s boot_code pc bound (by change 7≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have rp : ready.pc=7 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc]
 have header : Header k q w images stack output table ready := by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,input.bits,input.images,input.stack,
   input.output,input.table,input.width,input.size]
 have depth : ready.natReg 4020=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have native : ready.natReg 4021=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have count : ready.natReg 4023=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 obtain ⟨v,run,e⟩:=tree_execution n B k q w images stack output table 0 k 0 0 image x ready header rp depth native count
  (by omega) br.final_bound code imagesBefore stackBefore (by simpa using outputBefore) tableBound volume
  (Nat.two_pow_pos _) bank imageSmall entries
 let u:State:={v with pc:=70}
 have finish : BoundedExecution program n x B v 2 u:=.next run.final_bound
  (by simp [step,e.pc,return_at,e.header.zero,e.depth,u])
  (.halt (changePC_bound B v 70 run.final_bound (by omega)) (by simp [step,u,halt_at]))
 refine ⟨u,?_,rfl,?_,?_,?_,e.scalarHeap,e.scalarReg,e.outputs,e.roots,by
  rcases e.header with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩⟩
 · convert br.executes (run.executes finish) using 1
   change treeCost w k+9=7+(treeCost w k+2)
   omega
 · simpa [u] using e.count
 · intro j hj
   simpa [u] using e.written j hj
 · intro z hstack hout
   simpa [u,ready,boot,applyBlock,Op.apply,writeNat,next] using e.outside z (by simpa using hstack) (by simpa using hout)

end
end ExactFourierCircuits.UniformResidualFiberTraversal
