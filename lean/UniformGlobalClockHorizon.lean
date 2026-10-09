import UniformKernelHeaderInstallation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockHorizon
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
/-- Truncated subtraction computes max using ordinary arithmetic. The load
reads the real root duration cell addressed by the timing producer6175. -/
def block:List Op:=[.literal 5934 2,.literal 5935 5,.getNat 5936 6175,
 .mul 5936 5936 5934,.add 5936 5936 5935,.sub 5936 5936 5921,.add 5921 5921 5936]
lemma block_length:block.length=7:=rfl
lemma max_identity (a b:ℕ):a+(b-a)=max a b:=by omega
lemma horizon (s:State) (d:ℕ) (root:s.natHeap (s.natReg 6175)=some d):
 (applyBlock block s).natReg 5921=max (s.natReg 5921) (2*d+5):=by
 simp only[block,applyBlock,Op.apply,writeNat,next]
 simp [root,Nat.mul_comm,max_identity]
lemma safe (s:State) (d B:ℕ) (root:s.natHeap (s.natReg 6175)=some d)
 (size:2*d+5≤B) (wb:WordBound B s):readable block s ∧peak block s≤B:=by
 have old:=wb.2.1 5921
 simp[block,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,root]
 omega
lemma frame (s:State):(applyBlock block s).natHeap=s.natHeap ∧
 (applyBlock block s).scalarHeap=s.scalarHeap ∧(applyBlock block s).scalarReg=s.scalarReg ∧
 (applyBlock block s).outputs=s.outputs ∧(applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,q≠5921→(q<5934 ∨5937≤q)→(applyBlock block s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q horizon scratch
 simp(disch:=omega)[block,applyBlock,Op.apply,writeNat,next]
/-- One charged placed block accumulates the true maximum full local Fourier
horizon. No host-computed time is installed or treated as a machine action. -/
theorem execution {n B start:ℕ} (program:Program) (x:Fin n→ℂ) (s:State) (d:ℕ)
 (root:s.natHeap (s.natReg 6175)=some d) (size:2*d+5≤B)
 (code:BlockAt block program start) (pc:s.pc=start) (room:start+7≤B) (wb:WordBound B s):
 BoundedRuns program n x B s 7 (applyBlock block s) ∧
 (applyBlock block s).natReg 5921=max (s.natReg 5921) (2*d+5) ∧
 (applyBlock block s).natHeap=s.natHeap ∧(applyBlock block s).scalarHeap=s.scalarHeap ∧
 (applyBlock block s).scalarReg=s.scalarReg ∧(applyBlock block s).outputs=s.outputs ∧
 (applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,q≠5921→(q<5934 ∨5937≤q)→(applyBlock block s).natReg q=s.natReg q):=by
 have good:=safe s d B root size wb
 exact ⟨block_runs block program start n B x s code pc wb room good.1 good.2,horizon s d root,frame s⟩
end
end ExactFourierCircuits.UniformGlobalClockHorizon
