import UniformLocalRectanglePhaseBanks
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRetentionRegions
open UniformMachine
noncomputable section
abbrev Config := UniformSeedHeightPreparation.Config
abbrev Params := UniformRankCrossPreparationMachine.Parameters

def OriginalNat (c:Config) (i:ℕ) : Prop :=
 (i<c.d ∨ c.d+3*UniformRadixTwoDAG.count c.exponent ≤ i) ∧
 (i<c.conv ∨ c.conv+5*UniformToeplitzCrossTopologyMachine.G c.exponent ≤ i) ∧
 (i<c.tape ∨ c.tape+5*c.gates ≤ i) ∧
 (i<c.depth ∨ c.depth+c.e+1+c.gates ≤ i) ∧
 (i<c.order ∨ c.order+c.gates*(c.gates+1) ≤ i) ∧
 (i<c.directory ∨ c.directory+c.gates+2 ≤ i) ∧
 (i<c.rows ∨ UniformCrossHeightPreparationMachine.rowBase c.height (8*c.exponent+7) ≤ i) ∧
 (i<c.colors ∨ UniformCrossHeightPreparationMachine.colorBase c.height (8*c.exponent+7) ≤ i) ∧
 (i<c.palette ∨ c.palette+12 ≤ i) ∧
 (i<c.heightDirectory ∨ UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7) ≤ i)
def OriginalScalar (c:Config) (i:ℕ) : Prop :=
 (i<c.S ∨ c.S+6*c.width ≤ i) ∧
 (i<c.A ∨ UniformPreparedFFTMachine.rootAddress c.exponent c.A+1 ≤ i) ∧
 (i<c.C ∨ c.C+7*c.width+1 ≤ i) ∧
 (i<c.negative ∨ c.negative+7*c.width ≤ i) ∧ (i<c.constants ∨ c.constants+6 ≤ i)
def ConjugateNat (p:Params) (i:ℕ) : Prop :=
 (i<p.d ∨ p.d+3*UniformRadixTwoDAG.count p.K ≤ i) ∧
 (i<p.conv ∨ p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ i) ∧
 (i<p.tape ∨ p.tape+5*UniformRankCrossPreparationMachine.Shape p ≤ i) ∧
 (i<p.depth ∨ p.depth+p.e+1+UniformRankCrossPreparationMachine.Shape p ≤ i)
def ConjugateScalar (p:Params) (dest i:ℕ) : Prop :=
 (i<p.S ∨ p.S+6*UniformRadixTwoDAG.width p.K ≤ i) ∧
 (i<p.A ∨ UniformPreparedFFTMachine.rootAddress p.K p.A+1 ≤ i) ∧
 (i<p.C ∨ p.C+7*UniformRadixTwoDAG.width p.K+1 ≤ i) ∧
 (i<dest ∨ dest+7*UniformRadixTwoDAG.width p.K ≤ i)
def Slot (K A i:ℕ) : Prop := i<A ∨ A+55*UniformLocalReplayAssembly.phasePrefix (8*K+6) 6 ≤ i
def DisabledNat (v:UniformCrossHeightPreparationMachine.Parameters) (i:ℕ) : Prop :=
 (i<v.D ∨ UniformCrossHeightPreparationMachine.rowBase v (UniformCrossHeightPreparationMachine.height v) ≤ i) ∧
 (i<v.F ∨ UniformCrossHeightPreparationMachine.colorBase v (UniformCrossHeightPreparationMachine.height v) ≤ i) ∧
 (i<v.U ∨ v.U+12 ≤ i) ∧
 (i<v.J ∨ UniformCrossHeightPreparationMachine.recordBase v (UniformCrossHeightPreparationMachine.height v) ≤ i)

def CoefficientFrame (c:Config) (p:Params) (dest:ℕ) (s u:State) : Prop :=
 (∀i, OriginalNat c i → ConjugateNat p i → u.natHeap i=s.natHeap i) ∧
 (∀i, OriginalScalar c i → ConjugateScalar p dest i → u.scalarHeap i=s.scalarHeap i)
def ReplayFrame (c:Config) (p:Params) (dest A:ℕ) (s u:State) : Prop :=
 (∀i, OriginalNat c i → ConjugateNat p i → Slot c.exponent A i → u.natHeap i=s.natHeap i) ∧
 (∀i, OriginalScalar c i → ConjugateScalar p dest i → u.scalarHeap i=s.scalarHeap i)
def PhaseFrame (c:Config) (p:Params) (dest A:ℕ) (v:UniformCrossHeightPreparationMachine.Parameters) (s u:State) : Prop :=
 (∀i, OriginalNat c i → ConjugateNat p i → Slot c.exponent A i → DisabledNat v i → u.natHeap i=s.natHeap i) ∧
 (∀i, OriginalScalar c i → ConjugateScalar p dest i → u.scalarHeap i=s.scalarHeap i)

lemma original_nat {n:ℕ} {j:Fin (UniformAllAxisSeedPreparation.axisCount n)} {c:Config} {s u:State}
 (f:UniformSeedEdgeRetention.Height.Outside n j c s u) (i:ℕ) (h:OriginalNat c i) : u.natHeap i=s.natHeap i := by
 rcases h with ⟨a,b,c,d,e,g,h,j,k,l⟩
 exact f.1 i a b c d e g h j k l
lemma original_scalar {n:ℕ} {j:Fin (UniformAllAxisSeedPreparation.axisCount n)} {c:Config} {s u:State}
 (f:UniformSeedEdgeRetention.Height.Outside n j c s u) (i:ℕ) (h:OriginalScalar c i) : u.scalarHeap i=s.scalarHeap i := by
 rcases h with ⟨a,b,c,d,e⟩
 exact f.2 i a b c d e
lemma conjugate_nat {p:Params} {dest:ℕ} {s u:State}
 (f:UniformConjugateRankSpectrumPreparation.Frame p dest s u) (i:ℕ) (h:ConjugateNat p i) : u.natHeap i=s.natHeap i := by
 rcases h with ⟨a,b,c,d⟩
 exact f.1 i a b c d
lemma conjugate_scalar {p:Params} {dest:ℕ} {s u:State}
 (f:UniformConjugateRankSpectrumPreparation.Frame p dest s u) (i:ℕ) (h:ConjugateScalar p dest i) : u.scalarHeap i=s.scalarHeap i := by
 rcases h with ⟨a,b,c,d⟩
 exact f.2.1 i a b c d
lemma disabled_nat {v:UniformCrossHeightPreparationMachine.Parameters} {s u:State}
 (f:UniformCrossHeightPreparationMachine.Outside v s u) (i:ℕ) (h:DisabledNat v i) : u.natHeap i=s.natHeap i := by
 rcases h with ⟨a,b,c,d⟩
 exact f i a b c d
lemma slot_nat {K A:ℕ} {s u:State} (f:UniformLocalReplayAssembly.Outside A K s u)
 (i:ℕ) (h:Slot K A i) : u.natHeap i=s.natHeap i := by
 apply f i
 rw [←Nat.mul_assoc]
 exact h
end
end ExactFourierCircuits.UniformCacheRetentionRegions
