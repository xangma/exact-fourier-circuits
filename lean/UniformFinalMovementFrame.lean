import UniformFinalRoleRetention
import UniformKernelSpectrumCopy
import UniformRolePointwiseMachine
import UniformPhysicalCRTConsumerMachine
import UniformFinalNumericJoin
import UniformSequentialExecution

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalMovementFrame
open UniformMachine UniformAxisCachePreparationRetention
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants

def Q (n:ℕ):ℕ := UniformKernelSpectrumStorage.base c n

/-- Only actual protected headers and low banks are retained. The copied
spectrum at Q and the active data banks may change. -/
structure Frame (n:ℕ) (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalar:∀a,a<Q n→u.scalarHeap a=s.scalarHeap a
 saved:∀a,100≤a→a≤106→u.natReg a=s.natReg a
 high:∀a,200≤a→a≠7200→a≠7390→u.natReg a=s.natReg a
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma low_bound {n:ℕ}(hn:0<n):UniformJointCacheWorkspace.stride n≤Q n:=by
 change (n+2)^19≤Q n
 have low:=UniformAxisCachePreparationRetention.slab_above_seed_word c n
 have reserve:=UniformKernelSpectrumStorage.reserve c hn
 unfold Q UniformKernelSpectrumStorage.base
 omega

lemma Frame.low {n:ℕ}{s u:State}(hn:0<n)(h:Frame n s u):
 UniformCacheLowRetention.Frame n s u:=
 ⟨fun a _=>congrFun h.natHeap a,fun a ha=>h.scalar a (ha.trans_le (low_bound hn))⟩

lemma Frame.core {n:ℕ}{s u:State}{x:Fin n→ℂ}(hn:0<n)(h:Frame n s u)
 (old:Core n x s):Core n x u:=by
 have low:=h.low hn
 have protectedFrame:=(low.preserved hn h.saved h.outputs h.roots).protected
 have original:=(UniformAllAxisSeedPreparation.word_setup hn).2.1
 have conjugate:=(UniformAllAxisConjugatePreparation.word_setup hn).2.1
 refine ⟨?_,protectedFrame.metadata old.metadata,protectedFrame.operands old.operands,?_,?_⟩
 · constructor
   all_goals first
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.index
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.offset
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.count
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.one
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.directory
   | exact (h.high _ (by omega) (by omega) (by omega)).trans old.header.zero
 · exact old.seed.transport_before (fun a ha=>low.scalar a (ha.trans_le original)) h.natHeap
 · apply UniformLocalRectangleCoefficientMachine.conjugate_retained old.conjugate
   · intro a ha
     exact low.scalar a (ha.trans_le conjugate)
   · intro a _
     exact congrFun h.natHeap a

lemma Frame.cache_heaps {n:ℕ}{s u:State}(hn:0<n)(h:Frame n s u)
 (j:Fin (UniformJointCacheAllocation.ell n)):
 UniformAxisCachePhysical.Heaps c n j s u:=by
 refine ⟨fun a _ _=>congrFun h.natHeap a,?_⟩
 intro a _ ha
 exact h.scalar a (ha.trans_le (UniformKernelSpectrumStorage.caches_before c hn j))

lemma Frame.cache_all {n upto:ℕ}{s u:State}(hn:0<n)(h:Frame n s u)
 (old:UniformAxisCacheLoopState.All c n hn upto s):
 UniformAxisCacheLoopState.All c n hn upto u:=
 fun j hj=>UniformAxisCacheContents.transport (old j hj) (h.cache_heaps hn j)

lemma Frame.copy {n L:ℕ}{s u:State}(h:UniformKernelSpectrumCopy.Frame (Q n) L s u):
 Frame n s u:=by
 refine ⟨h.natHeap,fun a ha=>h.scalar a (Or.inl ha),?_,?_,h.outputs,h.roots⟩
 · intro a lo hi;exact h.natReg a (by unfold UniformKernelSpectrumCopy.Changed;omega)
 · intro a lo h1 h2;exact h.natReg a (by unfold UniformKernelSpectrumCopy.Changed;omega)

lemma Frame.pointwise {n S L:ℕ}{s u:State}(before:Q n≤S)
 (h:UniformRolePointwiseMachine.Frame S L s u):Frame n s u:=by
 refine ⟨h.natHeap,fun a ha=>h.scalar a (Or.inl (by omega)),?_,?_,h.outputs,h.roots⟩
 · intro a lo hi;exact h.natReg a (by unfold UniformRolePointwiseMachine.Changed;omega)
 · intro a lo h1 h2;exact h.natReg a (by unfold UniformRolePointwiseMachine.Changed;omega)

lemma Frame.crt {n S T L:ℕ}{s u:State}(beforeS:Q n≤S)(beforeT:Q n≤T)
 (outside:∀a,(a<S∨S+L≤a)→(a<T∨T+L≤a)→u.scalarHeap a=s.scalarHeap a)
 (h:UniformPhysicalCRTConsumerMachine.Frame s u):Frame n s u:=by
 refine ⟨h.natHeap,fun a ha=>outside a (Or.inl (by omega)) (Or.inl (by omega)),?_,?_,h.outputs,h.roots⟩
 · intro a lo hi;exact h.natReg a (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)
 · intro a lo h1 h2;exact h.natReg a (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)

lemma Frame.trans {n:ℕ}{s u v:State}(a:Frame n s u)(b:Frame n u v):Frame n s v:=
 ⟨b.natHeap.trans a.natHeap,fun j hj=>(b.scalar j hj).trans (a.scalar j hj),
 fun j lo hi=>(b.saved j lo hi).trans (a.saved j lo hi),
 fun j lo h1 h2=>(b.high j lo h1 h2).trans (a.high j lo h1 h2),
 b.outputs.trans a.outputs,b.roots.trans a.roots⟩

lemma Frame.withPC {n:ℕ}{s u:State}(h:Frame n s u)(p:ℕ):Frame n s {u with pc:=p}:=by
 cases h;constructor <;> assumption

lemma Frame.beforePC {n:ℕ}{s u:State}(h:Frame n s u)(p:ℕ):Frame n {s with pc:=p} u:=by
 cases h;constructor <;> assumption

end
end ExactFourierCircuits.UniformFinalMovementFrame
