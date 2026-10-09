import UniformForwardMatchingFactorPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
lemma setup_safe {c:Config} {s:State} {B:ℕ} (h:Header c s) (slot:Slot c.slot c.chunk s)
 (hs:WordBound B s) (_code:415≤B):readable chunkSetup s ∧peak chunkSetup s≤B:=by
 rcases slot with ⟨bc,en,inv,dep,col⟩
 have bcB:=hs.2.2.1 _ _ bc
 have enB:=hs.2.2.1 _ _ en
 have invB:=hs.2.2.1 _ _ inv
 have depB:=hs.2.2.1 _ _ dep
 have colB:=hs.2.2.1 _ _ col
 have regs:=hs.2.1
 have rb:=regs 4410;have sb:=regs 4411;have tb:=regs 4412;have bb:=regs 4413
 have selb:=regs 4414;have ob:=regs 4415;have mb:=regs 4416;have pb:=regs 4417
 have wb:=regs 4418;have vb:=regs 4419;have ab:=regs 4420
 simp only[h.radix,h.source,h.target,h.borrowed,h.selected,h.ordinals,h.mapped,
  h.permutation,h.widths,h.markers,h.axis] at rb sb tb bb selb ob mb pb wb vb ab
 constructor
 · simp[chunkSetup,readable,Op.readable,Op.apply,writeNat,next,h.slot,bc,en,inv,dep,col,Nat.add_assoc]
 · simp[chunkSetup,peak,Op.peak,Op.apply,writeNat,next,h.radix,h.source,h.target,h.borrowed,
    h.selected,h.ordinals,h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,bc,en,inv,dep,col,Nat.add_assoc]
   omega
lemma chunk_high {s u:State} (h:UniformChunkMatchingPreparation.Frame s u) (q:ℕ) (hq:1206≤q):
 u.natReg q=s.natReg q:=h.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega)
lemma chunk_height {s u:State} (h:UniformChunkMatchingPreparation.Frame s u) (q:ℕ)
 (lo:1050≤q) (hi:q≤1079):u.natReg q=s.natReg q:=
 h.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega)
lemma translationSetup_safe {s:State} {B:ℕ} (zero:s.natReg 4430=0) (hs:WordBound B s):
 readable translationSetup s ∧peak translationSetup s≤B:=by
 have a:=hs.2.1 894;have b:=hs.2.1 1186;have c:=hs.2.1 4422;have d:=hs.2.1 4423
 simp[translationSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero]
 omega
lemma factorSetup_safe {s:State} {B:ℕ} (zero:s.natReg 4430=0) (hs:WordBound B s):
 readable factorSetup s ∧peak factorSetup s≤B:=by
 have a:=hs.2.1 1060;have b:=hs.2.1 4429;have c:=hs.2.1 1062;have d:=hs.2.1 4428
 have e:=hs.2.1 4426;have f:=hs.2.1 4427;have g:=hs.2.1 4422
 have h:=hs.2.1 4424;have i:=hs.2.1 4425
 simp[factorSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero]
 omega
lemma translationSetup_heap (s:State):(applyBlock translationSetup s).natHeap=s.natHeap ∧
 (applyBlock translationSetup s).scalarHeap=s.scalarHeap ∧(applyBlock translationSetup s).outputs=s.outputs ∧
 (applyBlock translationSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma factorSetup_heap (s:State):(applyBlock factorSetup s).natHeap=s.natHeap ∧
 (applyBlock factorSetup s).scalarHeap=s.scalarHeap ∧(applyBlock factorSetup s).outputs=s.outputs ∧
 (applyBlock factorSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma translationSetup_nat (s:State) (q:ℕ) (hq:q<4990 ∨4993<q):
 (applyBlock translationSetup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[translationSetup,applyBlock,Op.apply,writeNat,next]
lemma factorSetup_nat (s:State) (q:ℕ)
 (h0:q<2100 ∨2103<q) (h1:q<2106 ∨2107<q) (h2:q<2140 ∨2141<q) (h3:q<4330 ∨4331<q):
 (applyBlock factorSetup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[factorSetup,applyBlock,Op.apply,writeNat,next]
lemma setup_zero (s:State):(applyBlock chunkSetup s).natReg 4430=0:=by
 simp[chunkSetup,applyBlock,Op.apply,writeNat,next]
lemma factorSetup_args {c:Config} {s:State}
 (z:s.natReg 4430=0)
 (hc:s.natReg 1060=c.chunk.height.C) (hp:s.natReg 1062=c.chunk.height.P)
 (hn:s.natReg 4429=c.negative) (hv:s.natReg 4428=c.conjugates)
 (ha:s.natReg 4426=c.mu) (hb:s.natReg 4427=c.conjugate)
 (hd:s.natReg 4422=c.translated):
 UniformMatchingConjugateLoadMachine.RowArgs c.chunk.height.C c.negative c.chunk.height.P
  c.conjugates c.mu c.conjugate c.translated ((applyBlock factorSetup s).natReg 2141)
  (applyBlock factorSetup s):=by
 constructor <;>simp[factorSetup,applyBlock,Op.apply,writeNat,next,z,hc,hp,hn,hv,ha,hb,hd]
lemma factorSetup_pool {c:Config} {s:State} (z:s.natReg 4430=0)
 (hp:s.natReg 4424=c.pool) (hr:s.natReg 4425=c.ambient):
 (applyBlock factorSetup s).natReg 4330=c.pool ∧(applyBlock factorSetup s).natReg 4331=c.ambient:=by
 simp[factorSetup,applyBlock,Op.apply,writeNat,next,z,hp,hr]
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
