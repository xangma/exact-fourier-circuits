import UniformGlobalClockConductor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockControl
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformGlobalClockConductor (boot axisBoot advance tickAdvance)
noncomputable section

lemma boot_headers (s:State):
 (applyBlock boot s).natReg 5920=0 ∧(applyBlock boot s).natReg 5921=s.natReg 5921 ∧
 (applyBlock boot s).natReg 5936=s.natReg 6819 ∧(applyBlock boot s).natReg 5937=s.natReg 6821 ∧
 (applyBlock boot s).natReg 5938=s.natReg 102+1 ∧(applyBlock boot s).natReg 5939=1:=by
 simp[boot,applyBlock,Op.apply,writeNat,next]
lemma boot_safe {B:ℕ} (s:State) (count:s.natReg 102+1 ≤ B) (wb:WordBound B s):
 readable boot s ∧peak boot s ≤ B:=by
 have n:=wb.2.1 6819;have a:=wb.2.1 6821
 simp[boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
lemma axis_headers (s:State) (one:s.natReg 5939=1):
 (applyBlock axisBoot s).natReg 5922=0 ∧(applyBlock axisBoot s).natReg 5923=s.natReg 6020 ∧
 (applyBlock axisBoot s).natReg 5924=s.natReg 5936 ∧(applyBlock axisBoot s).natReg 5925=s.natReg 5937:=by
 simp[axisBoot,applyBlock,Op.apply,writeNat,next,one]
lemma axis_safe {B:ℕ} (s:State) (one:s.natReg 5939=1) (wb:WordBound B s):
 readable axisBoot s ∧peak axisBoot s ≤ B:=by
 have n:=wb.2.1 5936;have a:=wb.2.1 5937;have d:=wb.2.1 6020
 simp[axisBoot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,one]
 omega
lemma advance_headers (s:State) (one:s.natReg 5939=1):
 (applyBlock advance s).natReg 5922=s.natReg 5922+1 ∧
 (applyBlock advance s).natReg 5923=s.natReg 5923+2 ∧
 (applyBlock advance s).natReg 5924=s.natReg 5934 ∧(applyBlock advance s).natReg 5925=s.natReg 5935:=by
 simp[advance,applyBlock,Op.apply,writeNat,next,one]
lemma advance_safe {B:ℕ} (s:State) (one:s.natReg 5939=1) (wb:WordBound B s)
 (index:s.natReg 5922+1 ≤ B) (directory:s.natReg 5923+2 ≤ B):
 readable advance s ∧peak advance s ≤ B:=by
 have n:=wb.2.1 5934;have a:=wb.2.1 5935
 simp[advance,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,one]
 omega
lemma tick_headers (s:State) (one:s.natReg 5939=1):
 (applyBlock tickAdvance s).natReg 5920=s.natReg 5920+1:=by
 simp[tickAdvance,applyBlock,Op.apply,writeNat,next,one]
lemma tick_safe {B:ℕ} (s:State) (one:s.natReg 5939=1) (wb:WordBound B s)
 (unfinished:s.natReg 5920 < s.natReg 5921):
 readable tickAdvance s ∧peak tickAdvance s ≤ B:=by
 have horizon:=wb.2.1 5921
 simp[tickAdvance,readable,peak,Op.readable,Op.peak,one]
 omega

/-- All control operations leave produced tables and tagged data untouched. -/
lemma heap_frame (s:State) (ops:List Op) (h:ops=boot ∨ops=axisBoot ∨ops=advance ∨ops=tickAdvance):
 (applyBlock ops s).natHeap=s.natHeap ∧(applyBlock ops s).scalarHeap=s.scalarHeap ∧
 (applyBlock ops s).scalarReg=s.scalarReg ∧(applyBlock ops s).outputs=s.outputs ∧
 (applyBlock ops s).rootOrders=s.rootOrders:=by
 rcases h with rfl|rfl|rfl|rfl <;>exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The five boot instructions are charged in their actual literal placement. -/
theorem boot_execution {n B start:ℕ} (p:Program) (x:Fin n→ℂ) (s:State)
 (code:BlockAt boot p start) (pc:s.pc=start) (space:start+5 ≤ B)
 (count:s.natReg 102+1 ≤ B) (wb:WordBound B s):
 BoundedRuns p n x B s 5 (applyBlock boot s):=by
 have safe:=boot_safe s count wb
 exact block_runs boot p start n B x s code pc wb space safe.1 safe.2

theorem axis_execution {n B start:ℕ} (p:Program) (x:Fin n→ℂ) (s:State)
 (code:BlockAt axisBoot p start) (pc:s.pc=start) (space:start+4 ≤ B)
 (one:s.natReg 5939=1) (wb:WordBound B s):
 BoundedRuns p n x B s 4 (applyBlock axisBoot s):=by
 have safe:=axis_safe s one wb
 exact block_runs axisBoot p start n B x s code pc wb space safe.1 safe.2

theorem advance_execution {n B start:ℕ} (p:Program) (x:Fin n→ℂ) (s:State)
 (code:BlockAt advance p start) (pc:s.pc=start) (space:start+5 ≤ B)
 (one:s.natReg 5939=1) (wb:WordBound B s) (index:s.natReg 5922+1 ≤ B) (directory:s.natReg 5923+2 ≤ B):
 BoundedRuns p n x B s 5 (applyBlock advance s):=by
 have safe:=advance_safe s one wb index directory
 exact block_runs advance p start n B x s code pc wb space safe.1 safe.2

theorem tick_execution {n B start:ℕ} (p:Program) (x:Fin n→ℂ) (s:State)
 (code:BlockAt tickAdvance p start) (pc:s.pc=start) (space:start+1 ≤ B)
 (one:s.natReg 5939=1) (wb:WordBound B s) (unfinished:s.natReg 5920 < s.natReg 5921):
 BoundedRuns p n x B s 1 (applyBlock tickAdvance s):=by
 have safe:=tick_safe s one wb unfinished
 exact block_runs tickAdvance p start n B x s code pc wb space safe.1 safe.2
end
end ExactFourierCircuits.UniformGlobalClockControl
