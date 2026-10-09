import UniformFinalMovementCaller
import UniformFinalPhysicalTablePrefix

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOuterRetention
open UniformMachine
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants

/-- Exact outer fields, excluding the two frontiers restored at clock exit. -/
def RequiredNat (q:ℕ):Prop :=
 (100≤q∧q≤106) ∨ q=200 ∨ q=201 ∨ q=202 ∨ q=203 ∨ q=204 ∨ q=209 ∨
 (6020≤q∧q≤6037) ∨ q=5921 ∨ q=6904 ∨ q=6909 ∨ q=6910 ∨
 q=7300 ∨ q=7310 ∨ q=7311 ∨ (7790≤q∧q≤7797)

def RuntimeNat (q:ℕ):Prop := q=5921 ∨ q=6819 ∨ q=6821 ∨ q=6909 ∨ q=6910

/-- Retained physical inputs to the outer caller. Active data and scratch
cells are deliberately absent; AP and BI are separate produced tables. -/
structure Frame (n:ℕ)(s u:State):Prop where
 low:UniformCacheLowRetention.Frame n s u
 cache:∀j:Fin (UniformJointCacheAllocation.ell n),UniformAxisCachePhysical.Heaps c n j s u
 alpha:∀j:Fin (UniformInitialPreparation.len n),
  u.natHeap (UniformKernelSpectrumStorage.alphaBase c n+j.val)=
  s.natHeap (UniformKernelSpectrumStorage.alphaBase c n+j.val)
 inverse:∀j:Fin (UniformInitialPreparation.len n),
  u.natHeap (UniformKernelSpectrumStorage.betaInverseBase c n+j.val)=
  s.natHeap (UniformKernelSpectrumStorage.betaInverseBase c n+j.val)
 natReg:∀q,RequiredNat q→u.natReg q=s.natReg q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

/-- Saved spectrum is optional: saving it changes this bank while preserving
the basic outer frame. A clock can supply this stronger additional field. -/
def Spectrum (n:ℕ)(s u:State):Prop := ∀j:Fin (UniformInitialPreparation.len n),
 u.scalarHeap (UniformKernelSpectrumStorage.base c n+j.val)=
 s.scalarHeap (UniformKernelSpectrumStorage.base c n+j.val)

lemma Frame.refl (n:ℕ)(s:State):Frame n s s :=
 ⟨⟨by intros;rfl,by intros;rfl⟩,fun j=>.refl c n j s,
  by intros;rfl,by intros;rfl,by intros;rfl,rfl,rfl⟩

lemma Frame.trans {n:ℕ}{s u v:State}(a:Frame n s u)(b:Frame n u v):Frame n s v :=
 ⟨a.low.trans b.low,fun j=>(a.cache j).trans (b.cache j),
 fun j=>(b.alpha j).trans (a.alpha j),fun j=>(b.inverse j).trans (a.inverse j),
 fun q hq=>(b.natReg q hq).trans (a.natReg q hq),
 b.outputs.trans a.outputs,b.roots.trans a.roots⟩

lemma Frame.withPC {n:ℕ}{s u:State}(h:Frame n s u)(p:ℕ):Frame n s {u with pc:=p}:=by
 exact ⟨⟨h.low.nat,h.low.scalar⟩,fun j=>⟨(h.cache j).nat,(h.cache j).scalar⟩,
 h.alpha,h.inverse,h.natReg,h.outputs,h.roots⟩
lemma Frame.beforePC {n:ℕ}{s u:State}(h:Frame n s u)(p:ℕ):Frame n {s with pc:=p} u:=by
 exact ⟨⟨h.low.nat,h.low.scalar⟩,fun j=>⟨(h.cache j).nat,(h.cache j).scalar⟩,
 h.alpha,h.inverse,h.natReg,h.outputs,h.roots⟩

lemma Frame.saved {n:ℕ}{s u:State}(h:Frame n s u):
 ∀q,100≤q→q≤106→u.natReg q=s.natReg q:=by
 intro q lo hi;exact h.natReg q (Or.inl ⟨lo,hi⟩)

lemma Frame.runtime {n:ℕ}{s u:State}(h:Frame n s u)
 (natEnd:u.natReg 6819=s.natReg 6819)(scalarEnd:u.natReg 6821=s.natReg 6821):
 ∀q,RuntimeNat q→u.natReg q=s.natReg q:=by
 intro q hq
 rcases hq with rfl|rfl|rfl|rfl|rfl
 · exact h.natReg _ (by unfold RequiredNat;omega)
 · exact natEnd
 · exact scalarEnd
 · exact h.natReg _ (by unfold RequiredNat;omega)
 · exact h.natReg _ (by unfold RequiredNat;omega)

end
end ExactFourierCircuits.UniformFinalClockOuterRetention
