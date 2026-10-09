import UniformAxisCachePreparationRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheInputs
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation
open UniformAxisCachePreparationRetention

/-- Only the original data and both compact coefficient pools are needed
after startup; its mutable loop header is not carried as an input obligation. -/
structure Inputs (n:ℕ)(x:Fin n→ℂ)(s:State):Prop where
 metadata:UniformPermutationInversePreparation.Metadata n s
 operands:UniformInitialPreparation.Operands n x s
 original:Seed.Retained n (C.ell n) s
 conjugate:UniformAllAxisConjugatePreparation.Retained n (C.ell n) s

lemma of_core {n:ℕ}{x:Fin n→ℂ}{s:State}(h:Core n x s):Inputs n x s:=
 ⟨h.metadata,h.operands,h.seed,h.conjugate⟩
lemma Inputs.withPC {n pc:ℕ}{x:Fin n→ℂ}{s:State}(h:Inputs n x s):
 Inputs n x (UniformTensorMonomialMachine.setPC s pc):=
 ⟨h.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),h.operands.transport rfl,
  h.original.withPC,h.conjugate.withPC⟩

theorem transport (c:A.Constants)(n j:ℕ)(hn:0<n)(x:Fin n→ℂ)(s u:State)
 (input:Inputs n x s)(scalars:UniformLocalRectangleDescriptors.ScalarFrame s u)
 (heap:∀q,q<natAt c n j→u.natHeap q=s.natHeap q)
 (regs:∀q,100≤q→q≤106→u.natReg q=s.natReg q):Inputs n x u:=by
 have start:((n+2)^19)≤natAt c n j:=(slab_above_seed_word c n).trans (frontier_above_slab c n j)
 have original:Seed.directoryBase n+2*C.ell n≤natAt c n j:=
  (UniformAllAxisSeedPreparation.word_setup hn).2.2.trans start
 have conjugate:UniformAllAxisConjugatePreparation.directoryBase n+2*C.ell n≤natAt c n j:=
  (UniformAllAxisConjugatePreparation.word_setup hn).2.2.trans start
 have frame:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=
  ⟨fun q _ hi=>heap q (by omega),fun q _=>congrFun scalars.scalarHeap q,regs,
   scalars.outputs,scalars.rootOrders⟩
 refine ⟨frame.metadata input.metadata,frame.operands input.operands,?_,?_⟩
 · exact ⟨fun i hi q l=>(congrFun scalars.scalarHeap _).trans (input.original.coefficients i hi q l),
   fun i hi=>(heap _ (by omega)).trans (input.original.address i hi),
   fun i hi=>(heap _ (by omega)).trans (input.original.width i hi)⟩
 · exact ⟨fun i hi q l=>(congrFun scalars.scalarHeap _).trans (input.conjugate.coefficients i hi q l),
   fun i hi=>(heap _ (by omega)).trans (input.conjugate.address i hi),
   fun i hi=>(heap _ (by omega)).trans (input.conjugate.width i hi)⟩

end ExactFourierCircuits.UniformAxisCacheInputs
