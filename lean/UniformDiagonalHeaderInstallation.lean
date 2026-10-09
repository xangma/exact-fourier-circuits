import UniformGlobalDiagonalRowsMachine
import UniformGlobalTensorDiagonalMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDiagonalHeaderInstallation
open UniformMachine UniformTensorMonomialMachine
noncomputable section

/-- The actual retained allocator cells, plus saved startup102/103.
The combined prepared diagonal is always lane zero. Its coefficient row
 starts just after the actual W-role input slab, retaining persistent pools below2U. -/
def block(W:ℕ):List Op:=[.literal 5990 0,.literal 5991 1,
 .add 4580 102 5991,.add 4581 6020 5990,.literal 4582 0,
 .add 4583 6021 5990,.add 4584 6022 5990,
 .literal 5992 W,.mul 5993 5992 103,.add 4585 6026 5993,
 .add 4501 103 5990,.add 4502 6026 5990,.add 4503 6027 5990,
 .add 4504 102 5991,.add 4505 6021 5990,.add 4506 6024 5990,.add 4507 6025 5990]
lemma block_length(W:ℕ):(block W).length=17:=rfl

structure Input {W:ℕ}(L:UniformGlobalDiagonalRowsMachine.Layout)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W)(s:State):Prop where
 rowsCount:s.natReg 102+1=L.ell
 tensorCount:s.natReg 102+1=g.ell
 directory:s.natReg 6020=L.directory
 rows:s.natReg 6021=L.rows
 permutation:s.natReg 6022=L.permutation
 coefficient:s.natReg 6026+W*s.natReg 103=L.coefficient
 volume:s.natReg 103=g.volume
 source:s.natReg 6026=g.source
 destination:s.natReg 6027=g.destination
 tensorRows:s.natReg 6021=g.row
 natStack:s.natReg 6024=g.natStack
 scalarStack:s.natReg 6025=g.scalarStack

def Changed(q:ℕ):Prop:=(5990 ≤ q ∧ q ≤ 5993) ∨ (4580 ≤ q ∧ q ≤ 4585) ∨ (4501 ≤ q ∧ q ≤ 4507)
lemma frame(W:ℕ)(s:State):
 (applyBlock (block W) s).natHeap=s.natHeap ∧
 (applyBlock (block W) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (block W) s).scalarReg=s.scalarReg ∧
 (applyBlock (block W) s).outputs=s.outputs ∧
 (applyBlock (block W) s).rootOrders=s.rootOrders ∧
 (∀q,¬Changed q → (applyBlock (block W) s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q outside
 unfold Changed at outside
 simp (disch:=omega) [block,applyBlock,Op.apply,writeNat,next]

lemma safe {W:ℕ}(L:UniformGlobalDiagonalRowsMachine.Layout)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W)(s:State)(h:Input L g s)(wb:WordBound g.B s):
 readable (block W) s ∧ peak (block W) s ≤ g.B:=by
 have count:s.natReg 102+1 ≤ g.B:=by
  have bound:=g.natStackBound
  rw [h.tensorCount]
  omega
 have one:1 ≤ g.B:=by have code:=g.code;omega
 have h103:=wb.2.1 103
 have h20:=wb.2.1 6020;have h21:=wb.2.1 6021;have h22:=wb.2.1 6022
 have h23:=wb.2.1 6023;have h24:=wb.2.1 6024;have h25:=wb.2.1 6025
 have h26:=wb.2.1 6026;have h27:=wb.2.1 6027
 have roles:=g.roles
 have product:W*s.natReg 103 ≤ g.B:=by
  rw [h.volume]
  have below:=g.sourceBelow
  have stack:=g.scalarStackBound
  omega
 have coefficient:s.natReg 6026+W*s.natReg 103 ≤ g.B:=by
  rw [h.source,h.volume]
  have below:=g.sourceBelow
  have stack:=g.scalarStackBound
  omega
 simp [block,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega

lemma headers {W:ℕ}(L:UniformGlobalDiagonalRowsMachine.Layout)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W)(s:State)(h:Input L g s):
 UniformGlobalDiagonalRowsMachine.Header L (0:Fin 9) (applyBlock (block W) s) ∧
 UniformGlobalTensorDiagonalMachine.Header g (applyBlock (block W) s):=by
 constructor
 · constructor <;> simp [block,applyBlock,Op.apply,writeNat,next]
   · exact h.rowsCount
   · exact h.directory
   · exact h.rows
   · exact h.permutation
   · exact h.coefficient
 · constructor <;> simp [block,applyBlock,Op.apply,writeNat,next]
   · exact h.volume
   · exact h.source
   · exact h.destination
   · exact h.tensorCount
   · exact h.tensorRows
   · exact h.natStack
   · exact h.scalarStack

/-- Header setup is charged inside any literal caller placement and retains
all produced directory/pool/data cells exactly. -/
theorem execution {W n start:ℕ}(L:UniformGlobalDiagonalRowsMachine.Layout)
 (g:UniformGlobalTensorDiagonalMachine.Geometry W)(program:Program)(x:Fin n → ℂ)(s:State)
 (h:Input L g s)(code:BlockAt (block W) program start)(pc:s.pc=start)
 (room:start+17 ≤ g.B)(wb:WordBound g.B s):
 BoundedRuns program n x g.B s 17 (applyBlock (block W) s) ∧
 UniformGlobalDiagonalRowsMachine.Header L (0:Fin 9) (applyBlock (block W) s) ∧
 UniformGlobalTensorDiagonalMachine.Header g (applyBlock (block W) s) ∧
 (applyBlock (block W) s).natHeap=s.natHeap ∧
 (applyBlock (block W) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (block W) s).scalarReg=s.scalarReg ∧
 (applyBlock (block W) s).outputs=s.outputs ∧
 (applyBlock (block W) s).rootOrders=s.rootOrders ∧
 (∀q,¬Changed q → (applyBlock (block W) s).natReg q=s.natReg q):=by
 have safety:=safe L g s h wb
 have run:=block_runs (block W) program start n g.B x s code pc wb (by simpa only [block_length] using room) safety.1 safety.2
 have hd:=headers L g s h
 exact ⟨by simpa only [block_length] using run,hd.1,hd.2,frame W s⟩
end
end ExactFourierCircuits.UniformDiagonalHeaderInstallation
