import UniformLocalRequestFacts
import UniformLocalStoredRequestLoopControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl UniformLocalRequestGeometry
open UniformLocalCacheSlotConductorMachine
noncomputable section

/-- The loop invariant records only source banks and earlier actual outputs.
At index zero its completed-cache clause is empty. -/
structure Ready (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(R T:ℕ)
 (g:UniformLocalRequestGeometry.Geometry constants n j qs R T)(x:Fin n → ℂ)(i:ℕ)(s:State):Prop where
 control:Control constants n j qs R T i s
 source:Source R T qs s
 original:Retained n (axisCount n) s
 conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s
 metadata:UniformPermutationInversePreparation.Metadata n s
 operands:UniformInitialPreparation.Operands n x s
 completed:∀k (hk:k < qs.length),k < i → Complete constants n j qs R T g k hk s

lemma Ready.transport {constants n j qs R T g x i s u}
 (h:@Ready constants n j qs R T g x i s)(control:Control constants n j qs R T i u)
 (nat:u.natHeap=s.natHeap)(scalar:u.scalarHeap=s.scalarHeap)
 (saved:∀q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q)
 (out:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):Ready constants n j qs R T g x i u:=by
 have f:UniformSeedRankCrossPreparation.PreservedFrame n s u:=
  ⟨fun q _=>congrFun nat q,fun q _=>congrFun scalar q,saved,out,roots⟩
 refine ⟨control,h.source.transport (fun _ _ _=>congrFun nat _) (fun _ _=>congrFun nat _),
  f.retained h.original,?_,f.protected.metadata h.metadata,f.protected.operands h.operands,?_⟩
 · exact UniformLocalRectangleCoefficientMachine.conjugate_retained h.conjugate
    (fun q _=>congrFun scalar q) (fun q _=>congrFun nat q)
 · intro k hk old;exact (h.completed k hk old).heaps nat scalar

lemma Ready.withPC {constants n j qs R T g x i s}
 (h:@Ready constants n j qs R T g x i s)(pc:ℕ):Ready constants n j qs R T g x i (UniformTensorMonomialMachine.setPC s pc):=
 h.transport (h.control.withPC pc) rfl rfl (by intros;rfl) rfl rfl

def bodyCharge (n:ℕ)(j:Fin (axisCount n))(q:UniformLocalRectangleDescriptors.Row):ℕ:=
 UniformLocalRectanglePhaseBanks.runtimeBudget n j q (UniformJointCacheWorkspace.original n q)
  (UniformJointCacheWorkspace.work n)+slotCount n q*
  (4*(UniformJointCacheWorkspace.original n q).exponent+191*q.width+227*radix n j+315)+153
def requestCharge (n:ℕ)(j:Fin (axisCount n))(q:UniformLocalRectangleDescriptors.Row):ℕ:=bodyCharge n j q+16
def costPrefix (n:ℕ)(j:Fin (axisCount n))(qs:List Request):ℕ → ℕ
 | 0=>0
 | k+1=>costPrefix n j qs k+requestCharge n j (requestAt qs k).row
lemma costPrefix_step (n:ℕ)(j:Fin (axisCount n))(qs:List Request)(k:ℕ)(hk:k < qs.length):
 costPrefix n j qs (k+1)=costPrefix n j qs k+requestCharge n j (qs[k]'hk).row:=by
 rw[costPrefix,requestAt_eq qs k hk]

structure BodyResult {constants n j qs R T}(g:UniformLocalRequestGeometry.Geometry constants n j qs R T)
 (x:Fin n → ℂ)(i:ℕ)(hi:i < qs.length)(s u:State):Prop where
 ready:Ready constants n j qs R T g x i u
 current:Complete constants n j qs R T g i hi u
 measured:Cursor.Control (controller constants n j qs i) (slotCount n (qs[i]'hi).row) u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 low:∀a,slab constants n ≤ a → a < (controller constants n j qs i).cachePermutation → u.natHeap a=s.natHeap a
 high:∀a,slab constants n ≤ a → 
  (controller constants n j qs i).cachePermutation+(3*(controller constants n j qs i).ambient+11)*
   (352*(controller constants n j qs i).height.K+330) ≤ a → u.natHeap a=s.natHeap a
 scalar:∀a,slab constants n ≤ a → 
  (a < (controller constants n j qs i).pool ∨ (controller constants n j qs i).pool+
   9*(controller constants n j qs i).ambient*(352*(controller constants n j qs i).height.K+330) ≤ a) → 
  a ≠ (controller constants n j qs i).mu → a ≠ (controller constants n j qs i).conjugateMu → u.scalarHeap a=s.scalarHeap a
 driver:∀r,6160 ≤ r → r ≤ 6179 → u.natReg r=s.natReg r
 natHigh:∀r,6400 ≤ r → u.natReg r=s.natReg r

/-- Persistent forest/timing banks lie outside the cache interval. The fixed
global coefficient pools lie before or after this axis's reserved factors. -/
structure LoopFrame (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(s u:State):Prop where
 nat:∀a,slab constants n ≤ a →
  (a < (UniformJointCacheAllocation.axis constants n j).control ∨
   (UniformJointCacheAllocation.axis constants n j).leafForward ≤ a) → u.natHeap a=s.natHeap a
 scalar:∀a,slab constants n ≤ a →
  (a < (UniformJointCacheAllocation.axis constants n j).pool ∨
   (UniformJointCacheAllocation.axis constants n j).endScalar ≤ a) → u.scalarHeap a=s.scalarHeap a
 driver:∀r,6400 ≤ r → u.natReg r=s.natReg r
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma LoopFrame.refl (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(s:State):LoopFrame constants n j s s:=
 ⟨by intros;rfl,by intros;rfl,by intros;rfl,rfl,rfl⟩
lemma LoopFrame.trans {constants n j s u v}(f:LoopFrame constants n j s u)(g:LoopFrame constants n j u v):
 LoopFrame constants n j s v:=
 ⟨fun a h h'=>(g.nat a h h').trans (f.nat a h h'),
  fun a h h'=>(g.scalar a h h').trans (f.scalar a h h'),
  fun r h=>(g.driver r h).trans (f.driver r h),g.outputs.trans f.outputs,g.roots.trans f.roots⟩
lemma BodyResult.frame {constants n j qs R T g x i hi s u}(post:@BodyResult constants n j qs R T g x i hi s u):
 LoopFrame constants n j s u:=by
 refine ⟨?_,?_,post.natHigh,post.outputs,post.roots⟩
 · intro a low outside
   rcases outside with before|afterCache
   · apply post.low a low
     change a < (UniformJointCacheAllocation.axis constants n j).control+
      (3*radix n j+11)*slotPrefix n qs i
     omega
   · exact post.high a low ((g.end_before_leaf i hi).trans afterCache)
 · intro a low outside
   apply post.scalar a low
   · rcases outside with before|afterPool
     · left
       change a < (UniformJointCacheAllocation.axis constants n j).pool+9*radix n j*slotPrefix n qs i
       omega
     · exact Or.inr ((g.scalar_end i hi).trans afterPool)
   · change a ≠ 22*UniformJointCacheWorkspace.stride n
     have:=(low_before_cache constants n).2;omega
   · change a ≠ 22*UniformJointCacheWorkspace.stride n+1
     have:=(low_before_cache constants n).2;omega

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
