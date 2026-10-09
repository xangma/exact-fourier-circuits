import UniformFourierAxisWorkspace
import UniformAxisCacheAllocationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisWorkspaceHeader
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformFourierAxisWorkspace (axisBank natAmount)
noncomputable section

/-- All addresses are charged computations from the current fresh frontiers
and the real allocator scalar span. Regs7050..59 are the durable result. -/
def block:List Op:=[.literal 7061 2,.literal 7062 3,.literal 7063 9,.literal 7064 64,.literal 7065 0,
 .binary .mul 7060 6800 7063,.binary .sub 7066 6821 6820,.binary .div 7060 7066 7060,
 .binary .add 7050 5924 7065,.binary .mul 7066 7060 7061,.binary .add 7051 7050 7066,
 .binary .mul 7066 6800 7062,.binary .add 7052 7051 7066,.literal 7067 11,
 .binary .add 7052 7052 7067,.binary .add 7053 7052 7064,
 .binary .mul 7066 6800 7062,.binary .add 7054 7053 7066,
 .binary .add 7055 7054 6800,.binary .add 7056 7055 6800,
 .binary .add 7058 7056 6800,.literal 7067 5,.binary .add 7058 7058 7067,
 .binary .add 7057 5925 7065,.binary .mul 7066 6800 7063,.binary .add 7059 7057 7066,
 .binary .add 5934 7058 7065,.binary .add 5935 7059 7065]
lemma block_length:block.length=28:=rfl

structure Args(r N S C:ℕ)(s:State):Prop where
 radix:s.natReg 6800=r
 natFrontier:s.natReg 5924=N
 scalarFrontier:s.natReg 5925=S
 cachePool:s.natReg 6820=C
 cacheEnd:s.natReg 6821=C+9*r*UniformJointCacheExtent.capacity r
structure Header(r N S:ℕ)(s:State):Prop where
 selected:s.natReg 7050=(axisBank r N S).selected
 boundary:s.natReg 7051=(axisBank r N S).boundary
 phase:s.natReg 7052=(axisBank r N S).phase
 rows:s.natReg 7053=(axisBank r N S).rawRows
 permutation:s.natReg 7054=(axisBank r N S).permutation
 widths:s.natReg 7055=(axisBank r N S).widths
 markers:s.natReg 7056=(axisBank r N S).markers
 pool:s.natReg 7057=(axisBank r N S).pool
 endNat:s.natReg 7058=(axisBank r N S).endNat
 endScalar:s.natReg 7059=(axisBank r N S).endScalar
 nextNat:s.natReg 5934=(axisBank r N S).endNat
 nextScalar:s.natReg 5935=(axisBank r N S).endScalar

lemma quotient(r:ℕ)(positive:0<r):9*r*UniformJointCacheExtent.capacity r/(9*r)=UniformJointCacheExtent.capacity r:=
 Nat.mul_div_cancel_left _ (Nat.mul_pos (by decide) positive)
lemma values{r N S C:ℕ}{s:State}(h:Args r N S C s)(positive:0<r):Header r N S (applyBlock block s):=by
 have nz:r≠0:=by omega
 have div:r*(9*UniformJointCacheExtent.capacity r)/(r*9)=UniformJointCacheExtent.capacity r:=by
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using quotient r positive
 constructor <;>simp [block,applyBlock,Op.apply,evalNat,writeNat,next,h.radix,h.natFrontier,h.scalarFrontier,
  h.cachePool,h.cacheEnd,nz,div,UniformFourierAxisWorkspace.axisBank,Nat.mul_comm,Nat.mul_assoc]

lemma safe{r N S C B:ℕ}{s:State}(h:Args r N S C s)(positive:0<r)
 (natFit:N+natAmount r ≤ B)(scalarFit:S+9*r ≤ B)(code:80 ≤ B)(wb:WordBound B s):
 readable block s ∧peak block s ≤ B:=by
 have nz:r≠0:=by omega
 have div:r*(9*UniformJointCacheExtent.capacity r)/(r*9)=UniformJointCacheExtent.capacity r:=by
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using quotient r positive
 have cap:1 ≤ UniformJointCacheExtent.capacity r:=
  Nat.mul_le_mul (Nat.one_le_pow 2 r (by omega)) (show 1 ≤ UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4 by omega)
 have scaled:=Nat.mul_le_mul_left (9*r) cap
 have span:9*r*UniformJointCacheExtent.capacity r ≤ B:=by
  have endBound:=wb.2.1 6821
  rw [h.cacheEnd] at endBound
  omega
 have span2:r*(9*UniformJointCacheExtent.capacity r) ≤ B:=by nlinarith only [span]
 have denominator:9*r ≤ B:=by simpa only [Nat.mul_one] using scaled.trans span
 unfold natAmount at natFit
 simp [block,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
  h.radix,h.natFrontier,h.scalarFrontier,h.cachePool,h.cacheEnd,nz,div,
  Nat.mul_comm,Nat.mul_assoc]
 omega

theorem execution{r N S C B n start:ℕ}(program:Program)(x:Fin n→ℂ)(s:State)
 (h:Args r N S C s)(positive:0<r)(natFit:N+natAmount r ≤ B)(scalarFit:S+9*r ≤ B)
 (code:80 ≤ B)(atCode:BlockAt block program start)(pc:s.pc=start)(extent:start+28 ≤ B)(wb:WordBound B s):
 BoundedRuns program n x B s 28 (applyBlock block s) ∧Header r N S (applyBlock block s):=by
 have good:=safe h positive natFit scalarFit code wb
 have run:=block_runs block program start n B x s atCode pc wb
  (by simpa only [block_length] using extent) good.1 good.2
 exact ⟨by simpa only [block_length] using run,values h positive⟩

lemma frame(s:State):
 (applyBlock block s).natHeap=s.natHeap ∧(applyBlock block s).scalarHeap=s.scalarHeap ∧
 (applyBlock block s).scalarReg=s.scalarReg ∧(applyBlock block s).outputs=s.outputs ∧
 (applyBlock block s).rootOrders=s.rootOrders ∧
 (∀j,(j<7050 ∨7068 ≤ j)→j≠5934→j≠5935→(applyBlock block s).natReg j=s.natReg j):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j outside n s
 simp(disch:=omega)[block,applyBlock,Op.apply,evalNat,writeNat,next]
end
end ExactFourierCircuits.UniformFourierAxisWorkspaceHeader
