import UniformFastPhysicalCRTInitialization
import UniformGlobalNatPreparation

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT index enumeration after (5.5), PDF p.22
(`eq:crt-fourier`), and prefix bound (4.1), PDF p.18.

Mixed-radix carry enumeration is an implementation refinement of the paper's
linear traversal. Initialization, carry visits, frames and instruction counts
have no one-to-one paper lemma; the final caller charges this actual producer.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTEmission
open UniformMachine UniformNatBlockMachine UniformFastPhysicalCRTMachine
open UniformFastPhysicalCRTInitialization
noncomputable section

def Outside (L:Addresses)(V:ℕ)(heap:ℕ→Option ℕ)(s:State):Prop:=
 ∀q,(q<L.physicalAlpha∨L.physicalAlpha+V≤q)→
 (q<L.inverseBeta∨L.inverseBeta+V≤q)→s.natHeap q=heap q
lemma emit_heap{a V p:ℕ}(L:Addresses)(s:State)(args:Args a V L s)
 (index:s.natReg 7803=p)(z:Fin V)(normalized:s.natReg 7806=z.val)
 (alpha beta:Fin V≃Fin V)
 (alphaTable:UniformGlobalNatPreparation.PermutationBank V L.alpha s.natHeap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank V L.beta s.natHeap beta)
 (fresh:L.beta+V≤L.physicalAlpha):
 (applyBlock emitBody s).natHeap=Function.update
  (Function.update s.natHeap (L.physicalAlpha+p) (some (alpha z).val))
  (L.inverseBeta+(beta z).val) (some p):=by
 simp [applyBlock,emitBody,Op.apply,writeNat,next,evalNat,args.alpha,args.beta,args.physicalAlpha,
  args.inverseBeta,index,normalized,alphaTable z,bt z,
  show L.beta+z.val≠L.physicalAlpha+p by omega]
lemma emit_safe{a V p B:ℕ}(L:Addresses)(s:State)(args:Args a V L s)(c:Constants s)
 (index:s.natReg 7803=p)(z:Fin V)(normalized:s.natReg 7806=z.val)
 (alpha beta:Fin V≃Fin V)
 (alphaTable:UniformGlobalNatPreparation.PermutationBank V L.alpha s.natHeap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank V L.beta s.natHeap beta)
 (hp:p<V)(af:L.alpha+V≤B)(bf:L.beta+V≤B)(pf:L.physicalAlpha+V≤B)(ifit:L.inverseBeta+V≤B)
 (fresh:L.beta+V≤L.physicalAlpha):readable emitBody s∧peak emitBody s≤B:=by
 simp [readable,peak,emitBody,Op.readable,Op.peak,Op.apply,writeNat,next,evalNat,
  args.alpha,args.beta,args.physicalAlpha,args.inverseBeta,index,normalized,alphaTable z,bt z,c.one,
  show L.beta+z.val≠L.physicalAlpha+p by omega]
 omega
lemma emit_frame(s:State):Frame s (applyBlock emitBody s):=by
 constructor <;>try rfl
 intro q hq
 simp (disch:=omega) [applyBlock,emitBody,Op.apply,writeNat,next]
lemma emit_constants(s:State)(c:Constants s):Constants (applyBlock emitBody s):=by
 constructor <;>simp [applyBlock,emitBody,Op.apply,writeNat,next,c.zero,c.one,c.two]
lemma emit_index(s:State)(c:Constants s):
 (applyBlock emitBody s).natReg 7803=s.natReg 7803+1:=by
 simp [applyBlock,emitBody,Op.apply,writeNat,next,evalNat,c.one]
lemma emit_normal(s:State):(applyBlock emitBody s).natReg 7806=s.natReg 7806:=by
 simp [applyBlock,emitBody,Op.apply,writeNat,next]
lemma emit_outside{a V p:ℕ}(L:Addresses)(s:State)(args:Args a V L s)
 (index:s.natReg 7803=p)(z:Fin V)(normalized:s.natReg 7806=z.val)
 (alpha beta:Fin V≃Fin V)
 (alphaTable:UniformGlobalNatPreparation.PermutationBank V L.alpha s.natHeap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank V L.beta s.natHeap beta)
 (hp:p<V)(fresh:L.beta+V≤L.physicalAlpha):Outside L V s.natHeap (applyBlock emitBody s):=by
 intro q hq hk
 rw [emit_heap L s args index z normalized alpha beta alphaTable bt fresh,
  Function.update_of_ne (by have h: (beta z).val<V:=(beta z).isLt;omega),
  Function.update_of_ne (by omega)]

/-- Both physical table writes, all source loads/addresses, and the ordinal
increment are executed as the literal nine-instruction emission block. -/
theorem execution{n a V p B:ℕ}(L:Addresses)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=19)(wb:WordBound B s)(args:Args a V L s)(c:Constants s)
 (index:s.natReg 7803=p)(z:Fin V)(normalized:s.natReg 7806=z.val)
 (alpha beta:Fin V≃Fin V)
 (alphaTable:UniformGlobalNatPreparation.PermutationBank V L.alpha s.natHeap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank V L.beta s.natHeap beta)
 (hp:p<V)(af:L.alpha+V≤B)(bf:L.beta+V≤B)(pf:L.physicalAlpha+V≤B)(ifit:L.inverseBeta+V≤B)
 (fresh:L.beta+V≤L.physicalAlpha)(code:53≤B):∃u,
 BoundedRuns program n x B s 9 u∧u.pc=28∧u.natReg 7803=p+1∧u.natReg 7806=z.val∧
 Args a V L u∧Constants u∧Frame s u∧Outside L V s.natHeap u∧
 u.natHeap=Function.update
  (Function.update s.natHeap (L.physicalAlpha+p) (some (alpha z).val))
  (L.inverseBeta+(beta z).val) (some p):=by
 have safe:=emit_safe L s args c index z normalized alpha beta alphaTable bt hp af bf pf ifit fresh
 have run:=block_runs emitBody program 19 n B x s emit_code pc wb (by change 19+9≤B;omega)
  safe.1 safe.2
 refine ⟨applyBlock emitBody s,run,?_,?_,(emit_normal s).trans normalized,
  (emit_frame s).args args,emit_constants s c,emit_frame s,
  emit_outside L s args index z normalized alpha beta alphaTable bt hp fresh,
  emit_heap L s args index z normalized alpha beta alphaTable bt fresh⟩
 · rw [block_pc,pc];rfl
 · exact (emit_index s c).trans (congrArg (·+1) index)
end
end ExactFourierCircuits.UniformFastPhysicalCRTEmission
