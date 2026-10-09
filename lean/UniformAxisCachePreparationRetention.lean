import UniformAxisCacheSelectedPreparation
import UniformAllAxisConjugatePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePreparationRetention
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation

structure Core (n:ℕ)(x:Fin n→ℂ)(s:State):Prop where
 header:Seed.Header n (C.ell n) s
 metadata:UniformPermutationInversePreparation.Metadata n s
 operands:UniformInitialPreparation.Operands n x s
 seed:Seed.Retained n (C.ell n) s
 conjugate:UniformAllAxisConjugatePreparation.Retained n (C.ell n) s

lemma Core.withPC {n pc:ℕ}{x:Fin n→ℂ}{s:State}(h:Core n x s):
 Core n x (UniformTensorMonomialMachine.setPC s pc):=
 ⟨h.header.withPC,h.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),
  h.operands.transport rfl,h.seed.withPC,h.conjugate.withPC⟩

lemma frontier_above_slab (c:A.Constants)(n j:ℕ):A.slab c n≤natAt c n j:=by
 unfold natAt UniformJointCacheAllocation.natStart
 omega
lemma slab_above_seed_word (c:A.Constants)(n:ℕ):(n+2)^19≤A.slab c n:=by
 have coefficient:1≤100000*(UniformJointAllocation.fixed c+1):=by omega
 simpa only [A.slab,Nat.one_mul] using Nat.mul_le_mul_right ((n+2)^19) coefficient

/-- Both compact coefficient directories and protected permutation metadata
precede every allocated cache axis. Scalar coefficients are retained verbatim. -/
theorem transport (c:A.Constants)(n j:ℕ)(hn:0<n)(x:Fin n→ℂ)(s u:State)
 (core:Core n x s)(scalars:UniformLocalRectangleDescriptors.ScalarFrame s u)
 (heap:∀q,q<natAt c n j→u.natHeap q=s.natHeap q)
 (regs:∀q,q≤209→u.natReg q=s.natReg q):Core n x u:=by
 have start:((n+2)^19)≤natAt c n j:=(slab_above_seed_word c n).trans (frontier_above_slab c n j)
 have original:Seed.directoryBase n+2*C.ell n≤natAt c n j:=
  (UniformAllAxisSeedPreparation.word_setup hn).2.2.trans start
 have conjugate:UniformAllAxisConjugatePreparation.directoryBase n+2*C.ell n≤natAt c n j:=
  (UniformAllAxisConjugatePreparation.word_setup hn).2.2.trans start
 have hprotect:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=by
  refine ⟨?_,fun i _=>congrFun scalars.scalarHeap i,?_,scalars.outputs,scalars.rootOrders⟩
  · intro i _ hi
    exact heap i (by omega)
  · intro i lo hi
    exact regs i (by omega)
 refine ⟨?_,hprotect.metadata core.metadata,hprotect.operands core.operands,?_,?_⟩
 · constructor
   all_goals first
   | exact (regs 200 (by omega)).trans core.header.index
   | exact (regs 201 (by omega)).trans core.header.offset
   | exact (regs 202 (by omega)).trans core.header.count
   | exact (regs 203 (by omega)).trans core.header.one
   | exact (regs 204 (by omega)).trans core.header.directory
   | exact (regs 209 (by omega)).trans core.header.zero
 · constructor
   · intro i hi q l
     exact (congrFun scalars.scalarHeap _).trans (core.seed.coefficients i hi q l)
   · intro i hi
     exact (heap _ (by omega)).trans (core.seed.address i hi)
   · intro i hi
     exact (heap _ (by omega)).trans (core.seed.width i hi)
 · constructor
   · intro i hi q l
     exact (congrFun scalars.scalarHeap _).trans (core.conjugate.coefficients i hi q l)
   · intro i hi
     exact (heap _ (by omega)).trans (core.conjugate.address i hi)
   · intro i hi
     exact (heap _ (by omega)).trans (core.conjugate.width i hi)

end ExactFourierCircuits.UniformAxisCachePreparationRetention
