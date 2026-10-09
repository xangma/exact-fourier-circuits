import UniformLocalRectangleDriverFrames
import UniformLocalCacheContextConductor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleCacheBindings
open UniformMachine UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotConductorMachine
namespace P
abbrev actual:=UniformLocalRectanglePhaseBanks.actual
end P

/-- Only address/shape equalities identify the two physical producers. -/
structure Bindings(c:Header.Parameters)(q:Row)(original:UniformSeedHeightPreparation.Config)
 (D A dest FD FF FU FJ:ℕ):Prop where
 height:c.height=(P.actual q original).height
 falseRows:c.falseRows=FD
 falseColors:c.falseColors=FF
 falsePalette:c.falsePalette=FU
 falseDirectory:c.falseDirectory=FJ
 gates:c.gates=(P.actual q original).gates
 negative:c.negative=(P.actual q original).negative
 conjugates:c.conjugates=dest
 rectangle:c.rectangle=D
 slot:c.slot=A
 enabled:original.enabled=true

noncomputable section
/-- These are ordinary physical source registers for44, rather than its
initialized destination registers. The last field is the actual printed time
cell retained above the reused workspace. -/
structure Driver {n:ℕ}(j:Fin (axisCount n))(c:Header.Parameters)(I H:ℕ)(s:State):Prop where
 copies:∀p∈UniformLocalCacheContextMachine.copies,4237 ≤ p.2 → 
  s.natReg p.2=UniformLocalCacheContextMachine.value c I p.1
 originalDirectory:s.natReg 6167=directoryBase n+2*j.val
 radix:c.ambient=radix n j
 timeHigh:H ≤ s.natReg 6161
 time:s.natHeap (s.natReg 6161)=some c.time
 kind:c.kind=0

lemma Driver.retained {n j c I H s u}(h:@Driver n j c I H s)
 (nat:∀r,4237 ≤ r → u.natReg r=s.natReg r)
 (heap:∀i,H ≤ i → u.natHeap i=s.natHeap i):Driver j c I H u:=by
 refine ⟨?_,(nat _ (by omega)).trans h.originalDirectory,h.radix,?_,?_,h.kind⟩
 · intro p hp lo;exact (nat p.2 lo).trans (h.copies p hp lo)
 · rw [nat _ (by omega)];exact h.timeHigh
 · rw [nat _ (by omega),heap _ h.timeHigh];exact h.time

lemma update_height(v:UniformCrossHeightPreparationMachine.Parameters)(a e:ℕ)(b:Bool)
 (ha:v.a=a)(he:v.e=e)(hb:v.enabled=b):{v with a:=a,e:=e,enabled:=b}=v:=by
 cases v;simp_all

lemma true_height {c q original D A dest FD FF FU FJ}
 (h:Bindings c q original D A dest FD FF FU FJ):
 enabledHeight c q true=(P.actual q original).height:=by
 simp only [enabledHeight,UniformLocalCacheSlotHeaderMachine.selectedHeight,h.height,
  ite_true]
 apply update_height _ _ _ _ rfl rfl
 exact h.enabled

lemma false_height {c q original D A dest FD FF FU FJ}
 (h:Bindings c q original D A dest FD FF FU FJ):
 enabledHeight c q false=UniformLocalDisabledHeightMachine.disabled
  (P.actual q original).height FD FF FU FJ:=by
 simp only [enabledHeight,UniformLocalCacheSlotHeaderMachine.selectedHeight,h.height,
  Bool.false_eq_true,ite_false,h.falseRows,h.falseColors,h.falsePalette,h.falseDirectory,
  UniformLocalDisabledHeightMachine.disabled]
 rfl

lemma sources_of_cursor {n:ℕ}(j:Fin (axisCount n))(c:Header.Parameters)(q:Row)
 (original:UniformSeedHeightPreparation.Config)(D A dest FD FF FU FJ I H:ℕ)(s:State)
 (binding:Bindings c q original D A dest FD FF FU FJ)(driver:Driver j c I H s)
 (cursor:UniformCrossHeightPreparationMachine.Cursor
  (UniformLocalDisabledHeightMachine.disabled (P.actual q original).height FD FF FU FJ)
  (8*(P.actual q original).exponent+7) s)
 (retained:Retained n (axisCount n) s):UniformLocalCacheContextMachine.Sources c I s:=by
 constructor
 · intro p hp
   by_cases high:4237≤p.2
   · exact driver.copies p hp high
   simp only [UniformLocalCacheContextMachine.copies,List.mem_cons,List.not_mem_nil,or_false] at hp
   rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals first
    | omega
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.exponent
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.tape
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.order
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.sourceDirectory
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.coefficients
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,ite_false] using cursor.header.constants
    | simpa [UniformLocalCacheContextMachine.value,UniformLocalCacheSlotHeaderMachine.Parameters.register,
       binding.height,binding.gates,UniformLocalDisabledHeightMachine.disabled,UniformCrossHeightPreparationMachine.gates,
       UniformCrossHeightPreparationMachine.widthOf,UniformSeedHeightPreparation.Config.height,
       UniformSeedHeightPreparation.Config.gates,UniformSeedHeightPreparation.Config.width,ite_false] using cursor.gateCount
 · rw [driver.originalDirectory]
   simpa only [driver.radix,Nat.add_assoc] using retained.width j j.isLt
 · exact driver.time
 · exact driver.kind

lemma constants_of_operands {n:ℕ}{x:Fin n→ℂ}{s:State}(h:UniformInitialPreparation.Operands n x s):
 UniformHadamardPairMachine.Constants s:=by
 refine ⟨?_,?_,?_,?_,?_⟩
 all_goals first
  | simpa [UniformCConstantsMachine.bank] using h.constants ⟨1,by decide⟩
  | simpa [UniformCConstantsMachine.bank] using h.constants ⟨2,by decide⟩
  | simpa [UniformCConstantsMachine.bank] using h.constants ⟨3,by decide⟩
  | simpa [UniformCConstantsMachine.bank] using h.constants ⟨4,by decide⟩
  | simpa [UniformCConstantsMachine.bank] using h.constants ⟨5,by decide⟩

/-- Same real shared bank, with only the controller's finite-index width. -/
def coefficientBank {n:ℕ}(j:Fin (axisCount n))(q:Row)
 (original:UniformSeedHeightPreparation.Config)(c:Header.Parameters)
 (i:Fin (UniformToeplitzCrossDAG.bankSize c.height.K)):ℂ:=
 UniformRankCrossReplayPreparationMachine.bankValues
  (UniformSeedHeightPreparation.parameters n j (P.actual q original))
  (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val

lemma actual_a(q:Row)(original:UniformSeedHeightPreparation.Config):
 (P.actual q original).height.a=q.a:=rfl
lemma actual_e(q:Row)(original:UniformSeedHeightPreparation.Config):
 (P.actual q original).height.e=q.e:=rfl

lemma banks_of_outputs {n:ℕ}(hn:0<n)(j:Fin (axisCount n))(c:Header.Parameters)(q:Row)
 (original:UniformSeedHeightPreparation.Config)(D A dest FD FF FU FJ B:ℕ)(s:State)
 (binding:Bindings c q original D A dest FD FF FU FJ)
 (layout:UniformSeedHeightPreparation.Layout n j (P.actual q original) B)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (row:UniformLocalRectangleBankMachine.RowSource D q s)
 (generated:UniformLocalReplayAssembly.Generated (P.actual q original).exponent A 6 s)
 (yes:UniformCrossHeightPreparationMachine.Processed (P.actual q original).height (P.actual q original).negative
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j (P.actual q original))
   (layout.replay hn j (P.actual q original) B)).program (8*(P.actual q original).exponent+7) s)
 (no:UniformCrossHeightPreparationMachine.Processed
  (UniformLocalDisabledHeightMachine.disabled (P.actual q original).height FD FF FU FJ) (P.actual q original).negative
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j (P.actual q original))
   (layout.replay hn j (P.actual q original) B)).program (8*(P.actual q original).exponent+7) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources (P.actual q original).exponent (P.actual q original).C
  (P.actual q original).negative (P.actual q original).constants dest
  (fun i:Fin (7*(P.actual q original).width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j (P.actual q original))
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) s)
 (constants:UniformHadamardPairMachine.Constants s):
 UniformLocalCacheContextConductor.Banks c q ha he (coefficientBank j q original c) s:=by
 let N:=UniformRadixTwoDAG.width c.height.K
 cases c
 cases original
 rcases binding with ⟨bh,bfr,bfc,bfp,bfd,bg,bn,bc,br,bs,be⟩
 dsimp only at bh bfr bfc bfp bfd bg bn bc br bs
 subst_vars
 refine ⟨row,?_,?_,?_,?_,constants⟩
 · simpa only [UniformSeedHeightPreparation.Config.height] using generated
 · simpa [enabledHeight,UniformLocalCacheSlotHeaderMachine.selectedHeight,
    UniformRankCrossReplayPreparationMachine.cross,UniformSeedHeightPreparation.parameters,
    UniformSeedRankCrossPreparation.parameters,UniformSeedHeightPreparation.Config.seed,
    UniformSeedHeightPreparation.Config.height,UniformCrossHeightPreparationMachine.height,
    P.actual,UniformLocalRectanglePhaseBanks.actual,UniformLocalRectangleBankMachine.geometry] using yes
 · simpa [enabledHeight,UniformLocalCacheSlotHeaderMachine.selectedHeight,
    UniformLocalDisabledHeightMachine.disabled,
    UniformRankCrossReplayPreparationMachine.cross,UniformSeedHeightPreparation.parameters,
    UniformSeedRankCrossPreparation.parameters,UniformSeedHeightPreparation.Config.seed,
    UniformSeedHeightPreparation.Config.height,UniformCrossHeightPreparationMachine.height,
    P.actual,UniformLocalRectanglePhaseBanks.actual,UniformLocalRectangleBankMachine.geometry] using no
 · constructor
   · intro i
     have hi:i.val<7*N:=by
      have bound:=i.isLt
      change i.val<N+6*N at bound
      omega
     simpa only [coefficientBank,UniformSeedHeightPreparation.Config.height] using sources.positive ⟨i.val,hi⟩
   · intro i
     have hi:i.val<7*N:=by
      have bound:=i.isLt
      change i.val<N+6*N at bound
      omega
     simpa only [coefficientBank,UniformSeedHeightPreparation.Config.height] using sources.negative ⟨i.val,hi⟩
   · intro i
     have hi:i.val<7*N:=by
      have bound:=i.isLt
      change i.val<N+6*N at bound
      omega
     simpa only [coefficientBank,UniformSeedHeightPreparation.Config.height] using sources.conjugate ⟨i.val,hi⟩
   · exact sources.constants

end
end ExactFourierCircuits.UniformLocalRectangleCacheBindings
