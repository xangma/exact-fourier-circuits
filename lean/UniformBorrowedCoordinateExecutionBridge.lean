import UniformBorrowedCoordinateBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBorrowedCoordinateBridge
open UniformMachine UniformChunkPortMachine UniformToeplitzChunkWord

/-- Actual Borrowed17 execution prints the exact planner gate embedding. The
only resource inputs are the real raw headers and ordinary fit/address bounds. -/
theorem borrowed_execution (n B v s e t a g d:ℕ)(x:Fin n→ℂ)(u:State)
 (he:s+e ≤ v)(ha:t+a ≤ v)(fit:g+e+a ≤ v)
 (headers:UniformBorrowedCoordinateMachine.Headers s e t a g d u)
 (pc:u.pc=0)(wb:WordBound B u)(code:17 ≤ B)(width:v ≤ B)(table:d+g ≤ B):
 ∃c w,BoundedExecution UniformBorrowedCoordinateMachine.program n x B u c w ∧
 c ≤ 11*v+7 ∧
 (∀j:Fin g,w.natHeap (d+j.val)=some
  (P.borrowedEmbedding (positions (intervalEmbedding v s e he))
   (positions (intervalEmbedding v t a ha)) g (available_capacity he ha fit) j).val) ∧
 UniformBorrowedCoordinateMachine.Frame u w ∧UniformBorrowedCoordinateMachine.Outside d g u w:=by
 obtain ⟨c,w,run,cost,bank,frame,outside⟩:=UniformBorrowedCoordinateMachine.physical_embedding
  n x v s e t a g d B u headers pc wb code width (he.trans width) (ha.trans width) table fit
 refine ⟨c,w,run,cost,?_,frame,outside⟩
 intro j
 rw[←embedding_eq he ha fit (available_capacity he ha fit)]
 exact bank j

/-- Actual ChunkPort14 computes the exact dense abstract chunk coordinate from
its real Borrowed17 table. The zero-reference hole is excluded by natPorts. -/
theorem port_execution (n B v s e t a g Q:ℕ)(x:Fin n→ℂ)(u:State)
 (he:s+e ≤ v)(ha:t+a ≤ v)(separated:s+e ≤ t ∨ t+a ≤ s)(fit:g+e+a ≤ v)
 (i:Fin (e+g+a))(header:Header (natPorts e g a i) e g s t Q u)
 (bank:∀j:Fin g,u.natHeap (Q+j.val)=some (UniformBorrowedCoordinateMachine.embedding v s e t a g fit j).val)
 (bounds:Bounds e g a s t Q B)(pc:u.pc=0)(wb:WordBound B u):∃w,
 BoundedExecution UniformChunkPortMachine.program n x B u (runtime e g (natPorts e g a i)) w ∧
 w.natReg 1030=((placementOfFit (g:=g) (intervalEmbedding v s e he) (intervalEmbedding v t a ha)
  (interval_separated he ha separated) (by omega)).embedding i).val ∧Frame u w:=by
 obtain ⟨w,run,result,_range,frame⟩:=physical_execution n B v (natPorts e g a i) e g a s t Q x u
  he ha separated fit header (natPorts_domain e g a i) bank bounds pc wb
 exact ⟨w,run,result.trans (mapped_natPorts_eq he ha separated fit i),frame⟩
end ExactFourierCircuits.UniformBorrowedCoordinateBridge
