import UniformGlobalInverseReturn
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseHeaderInstallation
open UniformMachine UniformTensorMonomialMachine
noncomputable section

/-- Actual allocator bank6032 is7U, used as both the inverse native scalar
bank and the Nat suffix slab.6033 is8U, used for Nat stack/scalar temporary.
These ten copies and one literal install the retained inverse ABI. -/
def block:List Op:=[.literal 5911 0,.add 5900 5820 5911,.add 5901 6032 5911,
 .add 5902 6035 5911,.add 5903 5823 5911,.add 5904 6030 5911,
 .add 5905 6032 5911,.add 5906 6033 5911,.add 5907 6036 5911,
 .add 5908 6033 5911,.add 5910 6026 5911]
lemma block_length:block.length=11:=rfl
structure Input {W:ℕ} (p:UniformProducedInversePacking.Preparation W) (E:ℕ) (s:State):Prop where
 volume:s.natReg 5820=p.layout.total
 axes:s.natReg 5823=p.layout.ell
 source:s.natReg 6032=p.layout.source
 suffix:s.natReg 6032=p.layout.suffix
 directory:s.natReg 6035=E
 rows:s.natReg 6030=p.layout.rows
 stack:s.natReg 6033=p.layout.stack
 inverse:s.natReg 6036=p.layout.inverse
 temporary:s.natReg 6033=p.layout.destination
 destination:s.natReg 6026=p.destination
lemma safe (B:ℕ) (s:State) (wb:WordBound B s):readable block s ∧peak block s ≤ B:=by
 have h0:=wb.2.1 5820;have h3:=wb.2.1 5823;have h26:=wb.2.1 6026
 have h30:=wb.2.1 6030;have h32:=wb.2.1 6032;have h33:=wb.2.1 6033
 have h35:=wb.2.1 6035;have h36:=wb.2.1 6036
 simp[block,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
lemma args {W E:ℕ} (p:UniformProducedInversePacking.Preparation W) (s:State) (h:Input p E s):
 UniformGlobalInverseReturn.Args p E (applyBlock block s):=by
 constructor <;>simp[block,applyBlock,Op.apply,writeNat,next]
 all_goals first
  | exact h.volume
  | exact h.source
  | exact h.directory
  | exact h.axes
  | exact h.rows
  | exact h.suffix
  | exact h.stack
  | exact h.inverse
  | exact h.temporary
  | exact h.destination

lemma frame (s:State):(applyBlock block s).natHeap=s.natHeap ∧
 (applyBlock block s).scalarHeap=s.scalarHeap ∧(applyBlock block s).scalarReg=s.scalarReg ∧
 (applyBlock block s).outputs=s.outputs ∧(applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,q < 5900 ∨5912 ≤ q → (applyBlock block s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q outside
 simp (disch:=omega) [block,applyBlock,Op.apply,writeNat,next]
/-- Placement is arbitrary in the actual containing fixed program; all eleven
ordinary instructions are charged and preserve both heaps exactly. -/
theorem execution {W n B start E:ℕ} (p:UniformProducedInversePacking.Preparation W)
 (program:Program) (x:Fin n → ℂ) (s:State) (h:Input p E s)
 (code:BlockAt block program start) (pc:s.pc=start) (room:start+11 ≤ B) (wb:WordBound B s):
 BoundedRuns program n x B s 11 (applyBlock block s) ∧
 UniformGlobalInverseReturn.Args p E (applyBlock block s) ∧
 (applyBlock block s).natHeap=s.natHeap ∧(applyBlock block s).scalarHeap=s.scalarHeap ∧
 (applyBlock block s).scalarReg=s.scalarReg ∧(applyBlock block s).outputs=s.outputs ∧
 (applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,q < 5900 ∨5912 ≤ q → (applyBlock block s).natReg q=s.natReg q):=by
 have hs:=safe B s wb
 exact ⟨block_runs block program start n B x s code pc wb room hs.1 hs.2,args p s h,frame s⟩
end
end ExactFourierCircuits.UniformInverseHeaderInstallation
