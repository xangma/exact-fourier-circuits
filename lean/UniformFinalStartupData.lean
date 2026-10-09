import UniformFinalAllocationStride
import UniformInitialCoreRetention

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 three-transform construction and §5.4 Theorem 1.1 proof,
PDF pp.22-24 (`eq:chirp`, `thm:main`), with the model in §1.1, PDF p.2 (`sec:model`).

Startup, header, continuation and output bookkeeping refines the fixed
deterministic program. There is no separate paper counterpart for these state
layouts; the surrounding paper argument requires their preparation/index cost.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStartupData
open UniformMachine UniformTensorMonomialMachine
noncomputable section
structure Data (n:ℕ)(x:Fin n→ℂ)(s:State):Prop where
 gathered:∀j:Fin (UniformInitialPreparation.len n),
  s.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
   (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
    (UniformCRTTraversalCycle.alphaPermutation n j).val)
 inverse:UniformGlobalNatPreparation.PermutationBank (UniformInitialPreparation.len n)
  (UniformPermutationInversePreparation.inverseBase n) s.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm
 roots:s.rootOrders=[UniformMasterRootMachine.order n]
 outputs:s.outputs=initial.outputs
lemma Data.withPC{n pc:ℕ}{x:Fin n→ℂ}{s:State}(h:Data n x s):Data n x (setPC s pc):=⟨h.gathered,h.inverse,h.roots,h.outputs⟩
lemma Data.transport{n:ℕ}{x:Fin n→ℂ}{s u:State}(h:Data n x s)
 (nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap)
 (roots:u.rootOrders=s.rootOrders)(outputs:u.outputs=s.outputs):Data n x u:=by
 refine ⟨fun j=>(congrFun sh _).trans (h.gathered j),?_,roots.trans h.roots,outputs.trans h.outputs⟩
 intro j
 exact (congrFun nh _).trans (h.inverse j)
end
end ExactFourierCircuits.UniformFinalStartupData
